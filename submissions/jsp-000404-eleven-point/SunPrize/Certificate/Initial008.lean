import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory003
import SunPrize.Certificate.Theory004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule6842 (p2122 p2819 p3325 : Prop) (h : (¬ p2122) ∨ (¬ p3325) ∨ p2819) : (¬ p2122) ∨ (p2819) ∨ (¬ p3325) := by
  classical
  tauto

theorem initial6842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2122)) ∨ (meaning t m 2819) ∨ (¬ (meaning t m 3325)) := by
  have source := ElevenTheory.theory989 (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule6842 (meaning t m 2122) (meaning t m 2819) (meaning t m 3325) source

theorem rule6843 (p2122 p3483 p4187 : Prop) (h : (¬ p2122) ∨ (¬ p4187) ∨ p3483) : (¬ p2122) ∨ (p3483) ∨ (¬ p4187) := by
  classical
  tauto

theorem initial6843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2122)) ∨ (meaning t m 3483) ∨ (¬ (meaning t m 4187)) := by
  have source := ElevenTheory.theory990 (m.theta 2 6) (m.theta 6 7) (m.theta 6 9)
  exact rule6843 (meaning t m 2122) (meaning t m 3483) (meaning t m 4187) source

theorem rule6844 (p2122 p3097 p4428 : Prop) (h : (¬ p3097) ∨ (¬ p4428) ∨ (¬ p2122)) : (¬ p2122) ∨ (¬ p3097) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial6844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory991 (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule6844 (meaning t m 2122) (meaning t m 3097) (meaning t m 4428) source

theorem rule6845 (p2386 p2578 : Prop) (h : p2578 ∨ p2386) : (p2386) ∨ (p2578) := by
  classical
  tauto

theorem initial6845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2386) ∨ (meaning t m 2578) := by
  have source := ElevenTheory.theory992 (m.theta 0 6) (m.theta 4 6)
  exact rule6845 (meaning t m 2386) (meaning t m 2578) source

theorem rule6846 (p2406 p2850 p3590 : Prop) (h : (¬ p3590) ∨ (¬ p2406) ∨ p2850) : (¬ p2406) ∨ (p2850) ∨ (¬ p3590) := by
  classical
  tauto

theorem initial6846 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (meaning t m 2850) ∨ (¬ (meaning t m 3590)) := by
  have source := ElevenTheory.theory993 (m.theta 1 4) (m.theta 2 4) (m.theta 4 5)
  exact rule6846 (meaning t m 2406) (meaning t m 2850) (meaning t m 3590) source

theorem rule6848 (p2156 p2563 p4109 : Prop) (h : (¬ p4109) ∨ (¬ p2156) ∨ p2563) : (¬ p2156) ∨ (p2563) ∨ (¬ p4109) := by
  classical
  tauto

theorem initial6848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (meaning t m 2563) ∨ (¬ (meaning t m 4109)) := by
  have source := ElevenTheory.theory995 (m.theta 0 5) (m.theta 4 5) (m.theta 5 6)
  exact rule6848 (meaning t m 2156) (meaning t m 2563) (meaning t m 4109) source

theorem rule6850 (p2685 p2810 p4112 : Prop) (h : (¬ p4112) ∨ (¬ p2685) ∨ (¬ p2810)) : (¬ p2685) ∨ (¬ p2810) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial6850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory997 (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule6850 (meaning t m 2685) (meaning t m 2810) (meaning t m 4112) source

theorem rule6851 (p2498 p3923 p3956 : Prop) (h : (¬ p3956) ∨ (¬ p2498) ∨ p3923) : (¬ p2498) ∨ (p3923) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial6851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2498)) ∨ (meaning t m 3923) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory998 (m.theta 1 6) (m.theta 4 6) (m.theta 6 8)
  exact rule6851 (meaning t m 2498) (meaning t m 3923) (meaning t m 3956) source

theorem rule6852 (p3921 p4107 p4278 : Prop) (h : (¬ p3921) ∨ (¬ p4107) ∨ p4278) : (¬ p3921) ∨ (¬ p4107) ∨ (p4278) := by
  classical
  tauto

theorem initial6852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4107)) ∨ (meaning t m 4278) := by
  have source := ElevenTheory.theory999 (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule6852 (meaning t m 3921) (meaning t m 4107) (meaning t m 4278) source

theorem rule6853 (p2138 p2780 p4193 : Prop) (h : (¬ p4193) ∨ (¬ p2138) ∨ p2780) : (¬ p2138) ∨ (p2780) ∨ (¬ p4193) := by
  classical
  tauto

theorem initial6853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (meaning t m 2780) ∨ (¬ (meaning t m 4193)) := by
  have source := ElevenTheory.theory1000 (m.theta 0 2) (m.theta 2 5) (m.theta 2 6)
  exact rule6853 (meaning t m 2138) (meaning t m 2780) (meaning t m 4193) source

theorem rule6855 (p2143 p3556 p4244 : Prop) (h : (¬ p2143) ∨ (¬ p3556) ∨ p4244) : (¬ p2143) ∨ (¬ p3556) ∨ (p4244) := by
  classical
  tauto

theorem initial6855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 3556)) ∨ (meaning t m 4244) := by
  have source := ElevenTheory.theory1002 (m.theta 0 5) (m.theta 2 5) (m.theta 5 7)
  exact rule6855 (meaning t m 2143) (meaning t m 3556) (meaning t m 4244) source

theorem rule6856 (p2685 p2797 p4067 : Prop) (h : (¬ p4067) ∨ (¬ p2685) ∨ p2797) : (¬ p2685) ∨ (p2797) ∨ (¬ p4067) := by
  classical
  tauto

theorem initial6856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2685)) ∨ (meaning t m 2797) ∨ (¬ (meaning t m 4067)) := by
  have source := ElevenTheory.theory1003 (m.theta 2 3) (m.theta 3 6) (m.theta 3 7)
  exact rule6856 (meaning t m 2685) (meaning t m 2797) (meaning t m 4067) source

theorem rule6857 (p3570 p3657 p3690 : Prop) (h : (¬ p3570) ∨ (¬ p3657) ∨ p3690) : (¬ p3570) ∨ (¬ p3657) ∨ (p3690) := by
  classical
  tauto

theorem initial6857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3657)) ∨ (meaning t m 3690) := by
  have source := ElevenTheory.theory1004 (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule6857 (meaning t m 3570) (meaning t m 3657) (meaning t m 3690) source

theorem rule6858 (p2619 p3105 p4335 : Prop) (h : (¬ p4335) ∨ (¬ p3105) ∨ p2619) : (p2619) ∨ (¬ p3105) ∨ (¬ p4335) := by
  classical
  tauto

theorem initial6858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2619) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4335)) := by
  have source := ElevenTheory.theory1005 (m.theta 2 5) (m.theta 5 8) (m.theta 5 9)
  exact rule6858 (meaning t m 2619) (meaning t m 3105) (meaning t m 4335) source

theorem rule6860 (p2685 p3755 p4429 : Prop) (h : (¬ p4429) ∨ (¬ p3755) ∨ p2685) : (p2685) ∨ (¬ p3755) ∨ (¬ p4429) := by
  classical
  tauto

theorem initial6860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2685) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4429)) := by
  have source := ElevenTheory.theory1007 (m.theta 2 3) (m.theta 3 7) (m.theta 3 9)
  exact rule6860 (meaning t m 2685) (meaning t m 3755) (meaning t m 4429) source

theorem rule6861 (p3096 p3744 p4137 : Prop) (h : (¬ p3744) ∨ (¬ p3096) ∨ p4137) : (¬ p3096) ∨ (¬ p3744) ∨ (p4137) := by
  classical
  tauto

theorem initial6861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3744)) ∨ (meaning t m 4137) := by
  have source := ElevenTheory.theory1008 (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule6861 (meaning t m 3096) (meaning t m 3744) (meaning t m 4137) source

theorem rule6863 (p2498 p2588 p3549 : Prop) (h : (¬ p2498) ∨ (¬ p2588) ∨ p3549) : (¬ p2498) ∨ (¬ p2588) ∨ (p3549) := by
  classical
  tauto

theorem initial6863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 3549) := by
  have source := ElevenTheory.theory1010 (m.theta 1 6) (m.theta 4 6) (m.theta 6 7)
  exact rule6863 (meaning t m 2498) (meaning t m 2588) (meaning t m 3549) source

theorem rule6865 (p2641 p2727 p4194 : Prop) (h : (¬ p2641) ∨ (¬ p4194) ∨ p2727) : (¬ p2641) ∨ (p2727) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial6865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (meaning t m 2727) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory1012 (m.theta 1 3) (m.theta 3 4) (m.theta 3 6)
  exact rule6865 (meaning t m 2641) (meaning t m 2727) (meaning t m 4194) source

theorem rule6866 (p2190 p2373 p2563 : Prop) (h : (¬ p2563) ∨ (¬ p2190) ∨ p2373) : (¬ p2190) ∨ (p2373) ∨ (¬ p2563) := by
  classical
  tauto

theorem initial6866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2190)) ∨ (meaning t m 2373) ∨ (¬ (meaning t m 2563)) := by
  have source := ElevenTheory.theory1013 (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule6866 (meaning t m 2190) (meaning t m 2373) (meaning t m 2563) source

theorem rule6867 (p2406 p2542 p4116 : Prop) (h : (¬ p4116) ∨ (¬ p2406) ∨ p2542) : (¬ p2406) ∨ (p2542) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial6867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (meaning t m 2542) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory1014 (m.theta 1 4) (m.theta 3 4) (m.theta 4 5)
  exact rule6867 (meaning t m 2406) (meaning t m 2542) (meaning t m 4116) source

theorem rule6871 (p2166 p2972 p4335 : Prop) (h : (¬ p4335) ∨ (¬ p2972) ∨ p2166) : (p2166) ∨ (¬ p2972) ∨ (¬ p4335) := by
  classical
  tauto

theorem initial6871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2166) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4335)) := by
  have source := ElevenTheory.theory1018 (m.theta 1 5) (m.theta 5 8) (m.theta 5 9)
  exact rule6871 (meaning t m 2166) (meaning t m 2972) (meaning t m 4335) source

theorem rule6872 (p4033 p4191 p4322 : Prop) (h : (¬ p4033) ∨ (¬ p4191) ∨ p4322) : (¬ p4033) ∨ (¬ p4191) ∨ (p4322) := by
  classical
  tauto

theorem initial6872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4191)) ∨ (meaning t m 4322) := by
  have source := ElevenTheory.theory1019 (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule6872 (meaning t m 4033) (meaning t m 4191) (meaning t m 4322) source

theorem rule6873 (p2166 p2373 p4210 : Prop) (h : (¬ p4210) ∨ (¬ p2373) ∨ p2166) : (p2166) ∨ (¬ p2373) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial6873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2166) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory1020 (m.theta 1 5) (m.theta 4 5) (m.theta 5 8)
  exact rule6873 (meaning t m 2166) (meaning t m 2373) (meaning t m 4210) source

theorem rule6876 (p4432 p4433 p4434 : Prop) (h : (¬ p4432) ∨ (¬ p4433) ∨ p4434) : (¬ p4432) ∨ (¬ p4433) ∨ (p4434) := by
  classical
  tauto

theorem initial6876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4433)) ∨ (meaning t m 4434) := by
  have source := ElevenTheory.theory1023 t (m.theta 4 8) (m.theta 5 8) (m.theta 6 8)
  exact rule6876 (meaning t m 4432) (meaning t m 4433) (meaning t m 4434) source

theorem rule6878 (p3922 p4228 p4435 : Prop) (h : (¬ p4435) ∨ (¬ p4228) ∨ (¬ p3922)) : (¬ p3922) ∨ (¬ p4228) ∨ (¬ p4435) := by
  classical
  tauto

theorem initial6878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4435)) := by
  have source := ElevenTheory.theory1025 (m.theta 1 6) (m.theta 3 6) (m.theta 6 10)
  exact rule6878 (meaning t m 3922) (meaning t m 4228) (meaning t m 4435) source

theorem rule6880 (p2122 p3309 p3918 : Prop) (h : (¬ p3918) ∨ (¬ p3309) ∨ p2122) : (p2122) ∨ (¬ p3309) ∨ (¬ p3918) := by
  classical
  tauto

theorem initial6880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2122) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3918)) := by
  have source := ElevenTheory.theory1027 (m.theta 1 6) (m.theta 2 6) (m.theta 6 7)
  exact rule6880 (meaning t m 2122) (meaning t m 3309) (meaning t m 3918) source

theorem rule6882 (p2352 p2668 p3984 : Prop) (h : (¬ p2352) ∨ (¬ p3984) ∨ p2668) : (¬ p2352) ∨ (p2668) ∨ (¬ p3984) := by
  classical
  tauto

theorem initial6882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2352)) ∨ (meaning t m 2668) ∨ (¬ (meaning t m 3984)) := by
  have source := ElevenTheory.theory1029 (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule6882 (meaning t m 2352) (meaning t m 2668) (meaning t m 3984) source

theorem rule6883 (p2122 p2295 p4328 : Prop) (h : (¬ p4328) ∨ (¬ p2295) ∨ p2122) : (p2122) ∨ (¬ p2295) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial6883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2122) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory1030 (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule6883 (meaning t m 2122) (meaning t m 2295) (meaning t m 4328) source

theorem rule6884 (p2143 p2870 p3556 : Prop) (h : (¬ p2143) ∨ (¬ p3556) ∨ (¬ p2870)) : (¬ p2143) ∨ (¬ p2870) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial6884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory1031 (m.theta 0 5) (m.theta 2 5) (m.theta 5 7)
  exact rule6884 (meaning t m 2143) (meaning t m 2870) (meaning t m 3556) source

theorem rule6886 (p3553 p3657 p3947 : Prop) (h : (¬ p3553) ∨ (¬ p3657) ∨ p3947) : (¬ p3553) ∨ (¬ p3657) ∨ (p3947) := by
  classical
  tauto

theorem initial6886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3657)) ∨ (meaning t m 3947) := by
  have source := ElevenTheory.theory1033 (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule6886 (meaning t m 3553) (meaning t m 3657) (meaning t m 3947) source

theorem rule6887 (p3660 p3741 p3920 : Prop) (h : (¬ p3920) ∨ (¬ p3660) ∨ p3741) : (¬ p3660) ∨ (p3741) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial6887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3660)) ∨ (meaning t m 3741) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory1034 (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule6887 (meaning t m 3660) (meaning t m 3741) (meaning t m 3920) source

theorem rule6888 (p3553 p3570 p3699 : Prop) (h : (¬ p3570) ∨ (¬ p3699) ∨ p3553) : (p3553) ∨ (¬ p3570) ∨ (¬ p3699) := by
  classical
  tauto

theorem initial6888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3553) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3699)) := by
  have source := ElevenTheory.theory1035 (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule6888 (meaning t m 3553) (meaning t m 3570) (meaning t m 3699) source

theorem rule6889 (p4041 p4437 p4438 : Prop) (h : (¬ p4437) ∨ (¬ p4438) ∨ p4041) : (p4041) ∨ (¬ p4437) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial6889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4041) ∨ (¬ (meaning t m 4437)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory1036 t (m.theta 3 8) (m.theta 4 8) (m.theta 7 8)
  exact rule6889 (meaning t m 4041) (meaning t m 4437) (meaning t m 4438) source

theorem rule6890 (p2156 p2284 p2951 : Prop) (h : (¬ p2951) ∨ (¬ p2156) ∨ p2284) : (¬ p2156) ∨ (p2284) ∨ (¬ p2951) := by
  classical
  tauto

theorem initial6890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (meaning t m 2284) ∨ (¬ (meaning t m 2951)) := by
  have source := ElevenTheory.theory1037 (m.theta 0 5) (m.theta 3 5) (m.theta 5 6)
  exact rule6890 (meaning t m 2156) (meaning t m 2284) (meaning t m 2951) source

theorem rule6891 (p3440 p3860 p4374 p4439 : Prop) (h : (¬ p4439) ∨ (¬ p3860) ∨ (¬ p4374) ∨ (¬ p3440)) : (¬ p3440) ∨ (¬ p3860) ∨ (¬ p4374) ∨ (¬ p4439) := by
  classical
  tauto

theorem initial6891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3440)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4374)) ∨ (¬ (meaning t m 4439)) := by
  have source := ElevenTheory.theory1038 (m.theta 0 1) (m.theta 0 9) (m.theta 1 8) (m.theta 1 9)
  exact rule6891 (meaning t m 3440) (meaning t m 3860) (meaning t m 4374) (meaning t m 4439) source

theorem rule6892 (p2088 p2475 p4045 p4440 : Prop) (h : (¬ p4440) ∨ (¬ p2475) ∨ (¬ p2088) ∨ (¬ p4045)) : (¬ p2088) ∨ (¬ p2475) ∨ (¬ p4045) ∨ (¬ p4440) := by
  classical
  tauto

theorem initial6892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 4045)) ∨ (¬ (meaning t m 4440)) := by
  have source := ElevenTheory.theory1039 (m.theta 0 8) (m.theta 4 8) (m.theta 4 9) (m.theta 8 9)
  exact rule6892 (meaning t m 2088) (meaning t m 2475) (meaning t m 4045) (meaning t m 4440) source

theorem rule6894 (p2363 p3146 p4441 : Prop) (h : (¬ p2363) ∨ (¬ p4441) ∨ p3146) : (¬ p2363) ∨ (p3146) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial6894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (meaning t m 3146) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory1041 (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule6894 (meaning t m 2363) (meaning t m 3146) (meaning t m 4441) source

theorem rule6896 (p2737 p3367 p3475 : Prop) (h : (¬ p3475) ∨ (¬ p2737) ∨ p3367) : (¬ p2737) ∨ (p3367) ∨ (¬ p3475) := by
  classical
  tauto

theorem initial6896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2737)) ∨ (meaning t m 3367) ∨ (¬ (meaning t m 3475)) := by
  have source := ElevenTheory.theory1043 (m.theta 1 2) (m.theta 2 3) (m.theta 2 4)
  exact rule6896 (meaning t m 2737) (meaning t m 3367) (meaning t m 3475) source

theorem rule6897 (p4173 p4334 p4363 : Prop) (h : (¬ p4334) ∨ (¬ p4363) ∨ p4173) : (p4173) ∨ (¬ p4334) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial6897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4173) ∨ (¬ (meaning t m 4334)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory1044 (m.theta 1 5) (m.theta 5 6) (m.theta 5 9)
  exact rule6897 (meaning t m 4173) (meaning t m 4334) (meaning t m 4363) source

theorem rule6898 (p4381 p4443 p4444 : Prop) (h : (¬ p4381) ∨ (¬ p4443) ∨ p4444) : (¬ p4381) ∨ (¬ p4443) ∨ (p4444) := by
  classical
  tauto

theorem initial6898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4443)) ∨ (meaning t m 4444) := by
  have source := ElevenTheory.theory1045 (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule6898 (meaning t m 4381) (meaning t m 4443) (meaning t m 4444) source

theorem rule6899 (p2331 p3292 p4421 : Prop) (h : (¬ p3292) ∨ (¬ p4421) ∨ (¬ p2331)) : (¬ p2331) ∨ (¬ p3292) ∨ (¬ p4421) := by
  classical
  tauto

theorem initial6899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4421)) := by
  have source := ElevenTheory.theory1046 (m.theta 0 3) (m.theta 3 6) (m.theta 3 9)
  exact rule6899 (meaning t m 2331) (meaning t m 3292) (meaning t m 4421) source

theorem rule6901 (p2264 p2449 p3945 : Prop) (h : (¬ p3945) ∨ (¬ p2264) ∨ p2449) : (¬ p2264) ∨ (p2449) ∨ (¬ p3945) := by
  classical
  tauto

theorem initial6901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (meaning t m 2449) ∨ (¬ (meaning t m 3945)) := by
  have source := ElevenTheory.theory1048 (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule6901 (meaning t m 2264) (meaning t m 2449) (meaning t m 3945) source

theorem rule6902 (p2996 p3919 p4360 : Prop) (h : (¬ p3919) ∨ (¬ p2996) ∨ p4360) : (¬ p2996) ∨ (¬ p3919) ∨ (p4360) := by
  classical
  tauto

theorem initial6902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3919)) ∨ (meaning t m 4360) := by
  have source := ElevenTheory.theory1049 (m.theta 1 3) (m.theta 3 7) (m.theta 3 8)
  exact rule6902 (meaning t m 2996) (meaning t m 3919) (meaning t m 4360) source

theorem rule6903 (p3487 p4116 : Prop) (h : p3487 ∨ p4116) : (p3487) ∨ (p4116) := by
  classical
  tauto

theorem initial6903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3487) ∨ (meaning t m 4116) := by
  have source := ElevenTheory.theory1050 (m.theta 1 4) (m.theta 3 4)
  exact rule6903 (meaning t m 3487) (meaning t m 4116) source

theorem rule6904 (p2542 p3083 p4355 : Prop) (h : (¬ p2542) ∨ (¬ p4355) ∨ p3083) : (¬ p2542) ∨ (p3083) ∨ (¬ p4355) := by
  classical
  tauto

theorem initial6904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2542)) ∨ (meaning t m 3083) ∨ (¬ (meaning t m 4355)) := by
  have source := ElevenTheory.theory1051 (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule6904 (meaning t m 2542) (meaning t m 3083) (meaning t m 4355) source

theorem rule6905 (p2510 p3016 p3083 : Prop) (h : (¬ p3016) ∨ (¬ p2510) ∨ p3083) : (¬ p2510) ∨ (¬ p3016) ∨ (p3083) := by
  classical
  tauto

theorem initial6905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 3016)) ∨ (meaning t m 3083) := by
  have source := ElevenTheory.theory1052 (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule6905 (meaning t m 2510) (meaning t m 3016) (meaning t m 3083) source

theorem rule6906 (p3146 p3657 p4132 p4445 : Prop) (h : (¬ p4445) ∨ (¬ p4132) ∨ (¬ p3146) ∨ (¬ p3657)) : (¬ p3146) ∨ (¬ p3657) ∨ (¬ p4132) ∨ (¬ p4445) := by
  classical
  tauto

theorem initial6906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4445)) := by
  have source := ElevenTheory.theory1053 (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule6906 (meaning t m 3146) (meaning t m 3657) (meaning t m 4132) (meaning t m 4445) source

theorem rule6908 (p3073 p3146 p4446 : Prop) (h : (¬ p3146) ∨ (¬ p4446) ∨ p3073) : (p3073) ∨ (¬ p3146) ∨ (¬ p4446) := by
  classical
  tauto

theorem initial6908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3073) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4446)) := by
  have source := ElevenTheory.theory1055 (m.theta 1 8) (m.theta 5 8) (m.theta 8 9)
  exact rule6908 (meaning t m 3073) (meaning t m 3146) (meaning t m 4446) source

theorem rule6909 (p4034 p4110 p4173 : Prop) (h : (¬ p4034) ∨ (¬ p4110) ∨ p4173) : (¬ p4034) ∨ (¬ p4110) ∨ (p4173) := by
  classical
  tauto

theorem initial6909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4110)) ∨ (meaning t m 4173) := by
  have source := ElevenTheory.theory1056 (m.theta 1 5) (m.theta 4 5) (m.theta 5 6)
  exact rule6909 (meaning t m 4034) (meaning t m 4110) (meaning t m 4173) source

theorem rule6913 (p2619 p2870 p3747 : Prop) (h : (¬ p3747) ∨ (¬ p2870) ∨ p2619) : (p2619) ∨ (¬ p2870) ∨ (¬ p3747) := by
  classical
  tauto

theorem initial6913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2619) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3747)) := by
  have source := ElevenTheory.theory1059 (m.theta 2 5) (m.theta 5 7) (m.theta 5 8)
  exact rule6913 (meaning t m 2619) (meaning t m 2870) (meaning t m 3747) source

theorem rule6914 (p2685 p2797 p4156 : Prop) (h : (¬ p2797) ∨ (¬ p4156) ∨ p2685) : (p2685) ∨ (¬ p2797) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial6914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2685) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory1060 (m.theta 2 3) (m.theta 3 6) (m.theta 3 7)
  exact rule6914 (meaning t m 2685) (meaning t m 2797) (meaning t m 4156) source

theorem rule6915 (p2657 p3172 p3878 : Prop) (h : (¬ p3878) ∨ (¬ p2657) ∨ p3172) : (¬ p2657) ∨ (p3172) ∨ (¬ p3878) := by
  classical
  tauto

theorem initial6915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2657)) ∨ (meaning t m 3172) ∨ (¬ (meaning t m 3878)) := by
  have source := ElevenTheory.theory1061 (m.theta 0 3) (m.theta 3 4) (m.theta 3 8)
  exact rule6915 (meaning t m 2657) (meaning t m 3172) (meaning t m 3878) source

theorem rule6916 (p2750 p3371 p4448 : Prop) (h : (¬ p3371) ∨ (¬ p2750) ∨ p4448) : (¬ p2750) ∨ (¬ p3371) ∨ (p4448) := by
  classical
  tauto

theorem initial6916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3371)) ∨ (meaning t m 4448) := by
  have source := ElevenTheory.theory1062 t (m.theta 1 2) (m.theta 1 3) (m.theta 1 5)
  exact rule6916 (meaning t m 2750) (meaning t m 3371) (meaning t m 4448) source

theorem rule6917 (p3989 p4185 p4358 : Prop) (h : (¬ p4358) ∨ (¬ p4185) ∨ p3989) : (p3989) ∨ (¬ p4185) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial6917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3989) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory1063 (m.theta 2 6) (m.theta 5 6) (m.theta 6 8)
  exact rule6917 (meaning t m 3989) (meaning t m 4185) (meaning t m 4358) source

theorem rule6918 (p3005 p3136 p4237 : Prop) (h : (¬ p3136) ∨ (¬ p4237) ∨ p3005) : (p3005) ∨ (¬ p3136) ∨ (¬ p4237) := by
  classical
  tauto

theorem initial6918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3005) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4237)) := by
  have source := ElevenTheory.theory1064 (m.theta 2 3) (m.theta 3 5) (m.theta 3 8)
  exact rule6918 (meaning t m 3005) (meaning t m 3136) (meaning t m 4237) source

theorem rule6919 (p2641 p2727 p3019 : Prop) (h : (¬ p2727) ∨ (¬ p3019) ∨ p2641) : (p2641) ∨ (¬ p2727) ∨ (¬ p3019) := by
  classical
  tauto

theorem initial6919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2641) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3019)) := by
  have source := ElevenTheory.theory1065 (m.theta 1 3) (m.theta 3 4) (m.theta 3 6)
  exact rule6919 (meaning t m 2641) (meaning t m 2727) (meaning t m 3019) source

theorem rule6921 (p3569 p3690 p4278 : Prop) (h : (¬ p4278) ∨ (¬ p3569) ∨ p3690) : (¬ p3569) ∨ (p3690) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial6921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3569)) ∨ (meaning t m 3690) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory1067 (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule6921 (meaning t m 3569) (meaning t m 3690) (meaning t m 4278) source

theorem rule6922 (p2230 p3355 p4449 : Prop) (h : (¬ p4449) ∨ (¬ p2230) ∨ p3355) : (¬ p2230) ∨ (p3355) ∨ (¬ p4449) := by
  classical
  tauto

theorem initial6922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (meaning t m 3355) ∨ (¬ (meaning t m 4449)) := by
  have source := ElevenTheory.theory1068 (m.theta 0 4) (m.theta 4 5) (m.theta 4 9)
  exact rule6922 (meaning t m 2230) (meaning t m 3355) (meaning t m 4449) source

theorem rule6924 (p4171 p4397 p4450 : Prop) (h : (¬ p4450) ∨ (¬ p4171) ∨ p4397) : (¬ p4171) ∨ (p4397) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial6924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4171)) ∨ (meaning t m 4397) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory1070 t (m.theta 5 9) (m.theta 6 9) (m.theta 8 9)
  exact rule6924 (meaning t m 4171) (meaning t m 4397) (meaning t m 4450) source

theorem rule6925 (p2098 p3365 p4364 : Prop) (h : (¬ p3365) ∨ (¬ p4364) ∨ (¬ p2098)) : (¬ p2098) ∨ (¬ p3365) ∨ (¬ p4364) := by
  classical
  tauto

theorem initial6925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4364)) := by
  have source := ElevenTheory.theory1071 (m.theta 0 2) (m.theta 2 3) (m.theta 2 8)
  exact rule6925 (meaning t m 2098) (meaning t m 3365) (meaning t m 4364) source

theorem rule6926 (p2641 p3189 p4341 : Prop) (h : (¬ p2641) ∨ (¬ p4341) ∨ p3189) : (¬ p2641) ∨ (p3189) ∨ (¬ p4341) := by
  classical
  tauto

theorem initial6926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (meaning t m 3189) ∨ (¬ (meaning t m 4341)) := by
  have source := ElevenTheory.theory1072 (m.theta 1 3) (m.theta 3 6) (m.theta 3 8)
  exact rule6926 (meaning t m 2641) (meaning t m 3189) (meaning t m 4341) source

theorem rule6927 (p2667 p3567 : Prop) (h : p2667 ∨ p3567) : (p2667) ∨ (p3567) := by
  classical
  tauto

theorem initial6927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2667) ∨ (meaning t m 3567) := by
  have source := ElevenTheory.theory1073 (m.theta 0 6) (m.theta 3 6)
  exact rule6927 (meaning t m 2667) (meaning t m 3567) source

theorem rule6928 (p2295 p2668 p3325 : Prop) (h : (¬ p3325) ∨ (¬ p2295) ∨ p2668) : (¬ p2295) ∨ (p2668) ∨ (¬ p3325) := by
  classical
  tauto

theorem initial6928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2295)) ∨ (meaning t m 2668) ∨ (¬ (meaning t m 3325)) := by
  have source := ElevenTheory.theory1074 (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule6928 (meaning t m 2295) (meaning t m 2668) (meaning t m 3325) source

theorem rule6929 (p2761 p3276 p4451 : Prop) (h : (¬ p4451) ∨ (¬ p2761) ∨ p3276) : (¬ p2761) ∨ (p3276) ∨ (¬ p4451) := by
  classical
  tauto

theorem initial6929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2761)) ∨ (meaning t m 3276) ∨ (¬ (meaning t m 4451)) := by
  have source := ElevenTheory.theory1075 (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule6929 (meaning t m 2761) (meaning t m 3276) (meaning t m 4451) source

theorem rule6930 (p2727 p2992 p3413 : Prop) (h : (¬ p3413) ∨ (¬ p2727) ∨ p2992) : (¬ p2727) ∨ (p2992) ∨ (¬ p3413) := by
  classical
  tauto

theorem initial6930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2727)) ∨ (meaning t m 2992) ∨ (¬ (meaning t m 3413)) := by
  have source := ElevenTheory.theory1076 (m.theta 1 3) (m.theta 3 4) (m.theta 3 5)
  exact rule6930 (meaning t m 2727) (meaning t m 2992) (meaning t m 3413) source

theorem rule6931 (p2590 p3660 : Prop) (h : p2590 ∨ p3660) : (p2590) ∨ (p3660) := by
  classical
  tauto

theorem initial6931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2590) ∨ (meaning t m 3660) := by
  have source := ElevenTheory.theory1077 (m.theta 4 5) (m.theta 4 6)
  exact rule6931 (meaning t m 2590) (meaning t m 3660) source

theorem rule6932 (p2417 p2911 p3945 : Prop) (h : (¬ p3945) ∨ (¬ p2911) ∨ p2417) : (p2417) ∨ (¬ p2911) ∨ (¬ p3945) := by
  classical
  tauto

theorem initial6932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2417) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3945)) := by
  have source := ElevenTheory.theory1078 (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule6932 (meaning t m 2417) (meaning t m 2911) (meaning t m 3945) source

theorem rule6933 (p3097 p3568 p3745 : Prop) (h : (¬ p3097) ∨ (¬ p3745) ∨ p3568) : (¬ p3097) ∨ (p3568) ∨ (¬ p3745) := by
  classical
  tauto

theorem initial6933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3097)) ∨ (meaning t m 3568) ∨ (¬ (meaning t m 3745)) := by
  have source := ElevenTheory.theory1079 (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule6933 (meaning t m 3097) (meaning t m 3568) (meaning t m 3745) source

theorem rule6935 (p3325 p3549 p3923 : Prop) (h : (¬ p3325) ∨ (¬ p3923) ∨ p3549) : (¬ p3325) ∨ (p3549) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial6935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3325)) ∨ (meaning t m 3549) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory1081 (m.theta 1 6) (m.theta 6 7) (m.theta 6 8)
  exact rule6935 (meaning t m 3325) (meaning t m 3549) (meaning t m 3923) source

theorem rule6937 (p2210 p4366 p4431 : Prop) (h : (¬ p4366) ∨ (¬ p4431) ∨ (¬ p2210)) : (¬ p2210) ∨ (¬ p4366) ∨ (¬ p4431) := by
  classical
  tauto

theorem initial6937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4431)) := by
  have source := ElevenTheory.theory1083 (m.theta 0 1) (m.theta 1 5) (m.theta 1 7)
  exact rule6937 (meaning t m 2210) (meaning t m 4366) (meaning t m 4431) source

theorem rule6938 (p2573 p2656 p3016 : Prop) (h : (¬ p2656) ∨ (¬ p2573) ∨ p3016) : (¬ p2573) ∨ (¬ p2656) ∨ (p3016) := by
  classical
  tauto

theorem initial6938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 3016) := by
  have source := ElevenTheory.theory1084 (m.theta 0 4) (m.theta 3 4) (m.theta 4 6)
  exact rule6938 (meaning t m 2573) (meaning t m 2656) (meaning t m 3016) source

theorem rule6940 (p2299 p3548 p4427 : Prop) (h : (¬ p4427) ∨ (¬ p2299) ∨ p3548) : (¬ p2299) ∨ (p3548) ∨ (¬ p4427) := by
  classical
  tauto

theorem initial6940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2299)) ∨ (meaning t m 3548) ∨ (¬ (meaning t m 4427)) := by
  have source := ElevenTheory.theory1086 (m.theta 1 7) (m.theta 6 7) (m.theta 7 8)
  exact rule6940 (meaning t m 2299) (meaning t m 3548) (meaning t m 4427) source

theorem rule6941 (p3591 p4366 p4452 : Prop) (h : (¬ p4452) ∨ (¬ p4366) ∨ p3591) : (p3591) ∨ (¬ p4366) ∨ (¬ p4452) := by
  classical
  tauto

theorem initial6941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3591) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4452)) := by
  have source := ElevenTheory.theory1087 (m.theta 0 1) (m.theta 1 6) (m.theta 1 7)
  exact rule6941 (meaning t m 3591) (meaning t m 4366) (meaning t m 4452) source

theorem rule6943 (p2299 p3570 p4275 : Prop) (h : (¬ p4275) ∨ (¬ p2299) ∨ p3570) : (¬ p2299) ∨ (p3570) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial6943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2299)) ∨ (meaning t m 3570) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory1089 (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule6943 (meaning t m 2299) (meaning t m 3570) (meaning t m 4275) source

theorem rule6944 (p3857 p4455 p4456 p4457 p4458 : Prop) : (¬ (p4455 ∧ p4456 ∧ p3857 ∧ p4457 ∧ p4458)) ∨ (p4455) := by
  classical
  tauto

theorem initial6944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4454)) ∨ (meaning t m 4455) := by
  exact rule6944 (meaning t m 3857) (meaning t m 4455) (meaning t m 4456) (meaning t m 4457) (meaning t m 4458)

theorem rule6945 (p3857 p4455 p4456 p4457 p4458 : Prop) : (¬ (p4455 ∧ p4456 ∧ p3857 ∧ p4457 ∧ p4458)) ∨ (p4456) := by
  classical
  tauto

theorem initial6945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4454)) ∨ (meaning t m 4456) := by
  exact rule6945 (meaning t m 3857) (meaning t m 4455) (meaning t m 4456) (meaning t m 4457) (meaning t m 4458)

theorem rule6946 (p3857 p4455 p4456 p4457 p4458 : Prop) : (p3857) ∨ (¬ (p4455 ∧ p4456 ∧ p3857 ∧ p4457 ∧ p4458)) := by
  classical
  tauto

theorem initial6946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3857) ∨ (¬ (meaning t m 4454)) := by
  exact rule6946 (meaning t m 3857) (meaning t m 4455) (meaning t m 4456) (meaning t m 4457) (meaning t m 4458)

theorem rule6950 (p2088 p4460 p4461 p4462 p4463 : Prop) : (¬ (p4460 ∧ p4461 ∧ p2088 ∧ p4462 ∧ p4463)) ∨ (p4460) := by
  classical
  tauto

theorem initial6950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4459)) ∨ (meaning t m 4460) := by
  exact rule6950 (meaning t m 2088) (meaning t m 4460) (meaning t m 4461) (meaning t m 4462) (meaning t m 4463)

theorem rule6951 (p2088 p4460 p4461 p4462 p4463 : Prop) : (¬ (p4460 ∧ p4461 ∧ p2088 ∧ p4462 ∧ p4463)) ∨ (p4461) := by
  classical
  tauto

theorem initial6951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4459)) ∨ (meaning t m 4461) := by
  exact rule6951 (meaning t m 2088) (meaning t m 4460) (meaning t m 4461) (meaning t m 4462) (meaning t m 4463)

theorem rule6952 (p2088 p4460 p4461 p4462 p4463 : Prop) : (p2088) ∨ (¬ (p4460 ∧ p4461 ∧ p2088 ∧ p4462 ∧ p4463)) := by
  classical
  tauto

theorem initial6952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2088) ∨ (¬ (meaning t m 4459)) := by
  exact rule6952 (meaning t m 2088) (meaning t m 4460) (meaning t m 4461) (meaning t m 4462) (meaning t m 4463)

theorem rule6958 (p4454 p4459 : Prop) : (¬ (p4454 ∨ p4459)) ∨ (p4454) ∨ (p4459) := by
  classical
  tauto

theorem initial6958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4453)) ∨ (meaning t m 4454) ∨ (meaning t m 4459) := by
  exact rule6958 (meaning t m 4454) (meaning t m 4459)

theorem rule6959 (p2082 p4453 : Prop) (h : (p2082 ↔ p4453)) : (¬ p2082) ∨ (p4453) := by
  classical
  tauto

theorem initial6959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2082)) ∨ (meaning t m 4453) := by
  have source := ElevenTheory.theory1090 t (m.theta 0 8) (m.theta 0 9) (m.theta 8 9)
  exact rule6959 (meaning t m 2082) (meaning t m 4453) source

theorem rule6963 (p2101 p2108 : Prop) : (p2101) ∨ (p2108) ∨ (¬ (p2101 ∨ p2108)) := by
  classical
  tauto

theorem initial6963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2101) ∨ (meaning t m 2108) ∨ (¬ (meaning t m 4464)) := by
  exact rule6963 (meaning t m 2101) (meaning t m 2108)

theorem rule6964 (p2092 p4464 : Prop) (h : (p2092 ↔ p4464)) : (¬ p2092) ∨ (p4464) := by
  classical
  tauto

theorem initial6964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2092)) ∨ (meaning t m 4464) := by
  have source := ElevenTheory.theory1091 t (m.theta 0 2) (m.theta 0 8) (m.theta 2 8)
  exact rule6964 (meaning t m 2092) (meaning t m 4464) source

theorem rule6982 (p3689 p3822 p4471 p4472 p4473 : Prop) : (p3689) ∨ (¬ (p3689 ∧ p4471 ∧ p3822 ∧ p4472 ∧ p4473)) := by
  classical
  tauto

theorem initial6982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3689) ∨ (¬ (meaning t m 4470)) := by
  exact rule6982 (meaning t m 3689) (meaning t m 3822) (meaning t m 4471) (meaning t m 4472) (meaning t m 4473)

theorem rule6983 (p3689 p3822 p4471 p4472 p4473 : Prop) : (¬ (p3689 ∧ p4471 ∧ p3822 ∧ p4472 ∧ p4473)) ∨ (p4471) := by
  classical
  tauto

theorem initial6983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4470)) ∨ (meaning t m 4471) := by
  exact rule6983 (meaning t m 3689) (meaning t m 3822) (meaning t m 4471) (meaning t m 4472) (meaning t m 4473)

theorem rule6984 (p3689 p3822 p4471 p4472 p4473 : Prop) : (p3822) ∨ (¬ (p3689 ∧ p4471 ∧ p3822 ∧ p4472 ∧ p4473)) := by
  classical
  tauto

theorem initial6984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3822) ∨ (¬ (meaning t m 4470)) := by
  exact rule6984 (meaning t m 3689) (meaning t m 3822) (meaning t m 4471) (meaning t m 4472) (meaning t m 4473)

theorem rule6985 (p3689 p3822 p4471 p4472 p4473 : Prop) : (¬ (p3689 ∧ p4471 ∧ p3822 ∧ p4472 ∧ p4473)) ∨ (p4472) := by
  classical
  tauto

theorem initial6985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4470)) ∨ (meaning t m 4472) := by
  exact rule6985 (meaning t m 3689) (meaning t m 3822) (meaning t m 4471) (meaning t m 4472) (meaning t m 4473)

theorem rule6986 (p3689 p3822 p4471 p4472 p4473 : Prop) : (¬ (p3689 ∧ p4471 ∧ p3822 ∧ p4472 ∧ p4473)) ∨ (p4473) := by
  classical
  tauto

theorem initial6986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4470)) ∨ (meaning t m 4473) := by
  exact rule6986 (meaning t m 3689) (meaning t m 3822) (meaning t m 4471) (meaning t m 4472) (meaning t m 4473)

theorem rule6988 (p2122 p3426 p4475 p4476 p4477 : Prop) : (¬ (p4475 ∧ p3426 ∧ p2122 ∧ p4476 ∧ p4477)) ∨ (p4475) := by
  classical
  tauto

theorem initial6988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4474)) ∨ (meaning t m 4475) := by
  exact rule6988 (meaning t m 2122) (meaning t m 3426) (meaning t m 4475) (meaning t m 4476) (meaning t m 4477)

theorem rule6989 (p2122 p3426 p4475 p4476 p4477 : Prop) : (p3426) ∨ (¬ (p4475 ∧ p3426 ∧ p2122 ∧ p4476 ∧ p4477)) := by
  classical
  tauto

theorem initial6989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3426) ∨ (¬ (meaning t m 4474)) := by
  exact rule6989 (meaning t m 2122) (meaning t m 3426) (meaning t m 4475) (meaning t m 4476) (meaning t m 4477)

theorem rule6990 (p2122 p3426 p4475 p4476 p4477 : Prop) : (p2122) ∨ (¬ (p4475 ∧ p3426 ∧ p2122 ∧ p4476 ∧ p4477)) := by
  classical
  tauto

theorem initial6990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2122) ∨ (¬ (meaning t m 4474)) := by
  exact rule6990 (meaning t m 2122) (meaning t m 3426) (meaning t m 4475) (meaning t m 4476) (meaning t m 4477)

theorem rule6992 (p2122 p3426 p4475 p4476 p4477 : Prop) : (¬ (p4475 ∧ p3426 ∧ p2122 ∧ p4476 ∧ p4477)) ∨ (p4477) := by
  classical
  tauto

theorem initial6992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4474)) ∨ (meaning t m 4477) := by
  exact rule6992 (meaning t m 2122) (meaning t m 3426) (meaning t m 4475) (meaning t m 4476) (meaning t m 4477)

theorem rule6996 (p4470 p4474 : Prop) : (¬ (p4470 ∨ p4474)) ∨ (p4470) ∨ (p4474) := by
  classical
  tauto

theorem initial6996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4469)) ∨ (meaning t m 4470) ∨ (meaning t m 4474) := by
  exact rule6996 (meaning t m 4470) (meaning t m 4474)

theorem rule6997 (p2116 p4469 : Prop) (h : (p2116 ↔ p4469)) : (¬ p2116) ∨ (p4469) := by
  classical
  tauto

theorem initial6997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2116)) ∨ (meaning t m 4469) := by
  have source := ElevenTheory.theory1094 t (m.theta 2 6) (m.theta 2 7) (m.theta 6 7)
  exact rule6997 (meaning t m 2116) (meaning t m 4469) source

theorem rule7001 (p2135 p2142 : Prop) : (p2135) ∨ (p2142) ∨ (¬ (p2135 ∨ p2142)) := by
  classical
  tauto

theorem initial7001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2135) ∨ (meaning t m 2142) ∨ (¬ (meaning t m 4478)) := by
  exact rule7001 (meaning t m 2135) (meaning t m 2142)

theorem rule7002 (p2126 p4478 : Prop) (h : (p2126 ↔ p4478)) : (¬ p2126) ∨ (p4478) := by
  classical
  tauto

theorem initial7002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2126)) ∨ (meaning t m 4478) := by
  have source := ElevenTheory.theory1095 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5)
  exact rule7002 (meaning t m 2126) (meaning t m 4478) source

theorem rule7020 (p3646 p3743 p4198 p4485 p4486 : Prop) : (p4198) ∨ (¬ (p4198 ∧ p3743 ∧ p3646 ∧ p4485 ∧ p4486)) := by
  classical
  tauto

theorem initial7020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4198) ∨ (¬ (meaning t m 4484)) := by
  exact rule7020 (meaning t m 3646) (meaning t m 3743) (meaning t m 4198) (meaning t m 4485) (meaning t m 4486)

theorem rule7021 (p3646 p3743 p4198 p4485 p4486 : Prop) : (p3743) ∨ (¬ (p4198 ∧ p3743 ∧ p3646 ∧ p4485 ∧ p4486)) := by
  classical
  tauto

theorem initial7021 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3743) ∨ (¬ (meaning t m 4484)) := by
  exact rule7021 (meaning t m 3646) (meaning t m 3743) (meaning t m 4198) (meaning t m 4485) (meaning t m 4486)

theorem rule7022 (p3646 p3743 p4198 p4485 p4486 : Prop) : (p3646) ∨ (¬ (p4198 ∧ p3743 ∧ p3646 ∧ p4485 ∧ p4486)) := by
  classical
  tauto

theorem initial7022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3646) ∨ (¬ (meaning t m 4484)) := by
  exact rule7022 (meaning t m 3646) (meaning t m 3743) (meaning t m 4198) (meaning t m 4485) (meaning t m 4486)

theorem rule7024 (p3646 p3743 p4198 p4485 p4486 : Prop) : (¬ (p4198 ∧ p3743 ∧ p3646 ∧ p4485 ∧ p4486)) ∨ (p4486) := by
  classical
  tauto

theorem initial7024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4484)) ∨ (meaning t m 4486) := by
  exact rule7024 (meaning t m 3646) (meaning t m 3743) (meaning t m 4198) (meaning t m 4485) (meaning t m 4486)

theorem rule7026 (p2156 p2962 p4356 p4488 p4489 : Prop) : (p4356) ∨ (¬ (p4356 ∧ p2962 ∧ p2156 ∧ p4488 ∧ p4489)) := by
  classical
  tauto

theorem initial7026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4356) ∨ (¬ (meaning t m 4487)) := by
  exact rule7026 (meaning t m 2156) (meaning t m 2962) (meaning t m 4356) (meaning t m 4488) (meaning t m 4489)

theorem rule7027 (p2156 p2962 p4356 p4488 p4489 : Prop) : (p2962) ∨ (¬ (p4356 ∧ p2962 ∧ p2156 ∧ p4488 ∧ p4489)) := by
  classical
  tauto

theorem initial7027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2962) ∨ (¬ (meaning t m 4487)) := by
  exact rule7027 (meaning t m 2156) (meaning t m 2962) (meaning t m 4356) (meaning t m 4488) (meaning t m 4489)

theorem rule7028 (p2156 p2962 p4356 p4488 p4489 : Prop) : (p2156) ∨ (¬ (p4356 ∧ p2962 ∧ p2156 ∧ p4488 ∧ p4489)) := by
  classical
  tauto

theorem initial7028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2156) ∨ (¬ (meaning t m 4487)) := by
  exact rule7028 (meaning t m 2156) (meaning t m 2962) (meaning t m 4356) (meaning t m 4488) (meaning t m 4489)

theorem rule7030 (p2156 p2962 p4356 p4488 p4489 : Prop) : (¬ (p4356 ∧ p2962 ∧ p2156 ∧ p4488 ∧ p4489)) ∨ (p4489) := by
  classical
  tauto

theorem initial7030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4487)) ∨ (meaning t m 4489) := by
  exact rule7030 (meaning t m 2156) (meaning t m 2962) (meaning t m 4356) (meaning t m 4488) (meaning t m 4489)

theorem rule7034 (p4484 p4487 : Prop) : (¬ (p4484 ∨ p4487)) ∨ (p4484) ∨ (p4487) := by
  classical
  tauto

theorem initial7034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4483)) ∨ (meaning t m 4484) ∨ (meaning t m 4487) := by
  exact rule7034 (meaning t m 4484) (meaning t m 4487)

theorem rule7035 (p2150 p4483 : Prop) (h : (p2150 ↔ p4483)) : (¬ p2150) ∨ (p4483) := by
  classical
  tauto

theorem initial7035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2150)) ∨ (meaning t m 4483) := by
  have source := ElevenTheory.theory1098 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 6)
  exact rule7035 (meaning t m 2150) (meaning t m 4483) source

theorem rule7037 (p2191 p3906 p4492 p4493 p4494 : Prop) : (¬ (p4492 ∧ p3906 ∧ p2191 ∧ p4493 ∧ p4494)) ∨ (p4492) := by
  classical
  tauto

theorem initial7037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4491)) ∨ (meaning t m 4492) := by
  exact rule7037 (meaning t m 2191) (meaning t m 3906) (meaning t m 4492) (meaning t m 4493) (meaning t m 4494)

theorem rule7038 (p2191 p3906 p4492 p4493 p4494 : Prop) : (p3906) ∨ (¬ (p4492 ∧ p3906 ∧ p2191 ∧ p4493 ∧ p4494)) := by
  classical
  tauto

theorem initial7038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3906) ∨ (¬ (meaning t m 4491)) := by
  exact rule7038 (meaning t m 2191) (meaning t m 3906) (meaning t m 4492) (meaning t m 4493) (meaning t m 4494)

theorem rule7039 (p2191 p3906 p4492 p4493 p4494 : Prop) : (p2191) ∨ (¬ (p4492 ∧ p3906 ∧ p2191 ∧ p4493 ∧ p4494)) := by
  classical
  tauto

theorem initial7039 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2191) ∨ (¬ (meaning t m 4491)) := by
  exact rule7039 (meaning t m 2191) (meaning t m 3906) (meaning t m 4492) (meaning t m 4493) (meaning t m 4494)

theorem rule7041 (p2191 p3906 p4492 p4493 p4494 : Prop) : (¬ (p4492 ∧ p3906 ∧ p2191 ∧ p4493 ∧ p4494)) ∨ (p4494) := by
  classical
  tauto

theorem initial7041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4491)) ∨ (meaning t m 4494) := by
  exact rule7041 (meaning t m 2191) (meaning t m 3906) (meaning t m 4492) (meaning t m 4493) (meaning t m 4494)

theorem rule7043 (p2166 p4446 p4496 p4497 p4498 : Prop) : (p4446) ∨ (¬ (p4446 ∧ p4496 ∧ p2166 ∧ p4497 ∧ p4498)) := by
  classical
  tauto

theorem initial7043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4446) ∨ (¬ (meaning t m 4495)) := by
  exact rule7043 (meaning t m 2166) (meaning t m 4446) (meaning t m 4496) (meaning t m 4497) (meaning t m 4498)

theorem rule7044 (p2166 p4446 p4496 p4497 p4498 : Prop) : (¬ (p4446 ∧ p4496 ∧ p2166 ∧ p4497 ∧ p4498)) ∨ (p4496) := by
  classical
  tauto

theorem initial7044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4495)) ∨ (meaning t m 4496) := by
  exact rule7044 (meaning t m 2166) (meaning t m 4446) (meaning t m 4496) (meaning t m 4497) (meaning t m 4498)

theorem rule7045 (p2166 p4446 p4496 p4497 p4498 : Prop) : (p2166) ∨ (¬ (p4446 ∧ p4496 ∧ p2166 ∧ p4497 ∧ p4498)) := by
  classical
  tauto

theorem initial7045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2166) ∨ (¬ (meaning t m 4495)) := by
  exact rule7045 (meaning t m 2166) (meaning t m 4446) (meaning t m 4496) (meaning t m 4497) (meaning t m 4498)

theorem rule7047 (p2166 p4446 p4496 p4497 p4498 : Prop) : (¬ (p4446 ∧ p4496 ∧ p2166 ∧ p4497 ∧ p4498)) ∨ (p4498) := by
  classical
  tauto

theorem initial7047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4495)) ∨ (meaning t m 4498) := by
  exact rule7047 (meaning t m 2166) (meaning t m 4446) (meaning t m 4496) (meaning t m 4497) (meaning t m 4498)

theorem rule7051 (p4491 p4495 : Prop) : (¬ (p4491 ∨ p4495)) ∨ (p4491) ∨ (p4495) := by
  classical
  tauto

theorem initial7051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4490)) ∨ (meaning t m 4491) ∨ (meaning t m 4495) := by
  exact rule7051 (meaning t m 4491) (meaning t m 4495)

theorem rule7052 (p2160 p4490 : Prop) (h : (p2160 ↔ p4490)) : (¬ p2160) ∨ (p4490) := by
  classical
  tauto

theorem initial7052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2160)) ∨ (meaning t m 4490) := by
  have source := ElevenTheory.theory1099 t (m.theta 1 5) (m.theta 1 8) (m.theta 5 8)
  exact rule7052 (meaning t m 2160) (meaning t m 4490) source

theorem rule7054 (p2299 p3955 p4133 p4138 p4501 : Prop) : (p3955) ∨ (¬ (p3955 ∧ p4138 ∧ p2299 ∧ p4501 ∧ p4133)) := by
  classical
  tauto

theorem initial7054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3955) ∨ (¬ (meaning t m 4500)) := by
  exact rule7054 (meaning t m 2299) (meaning t m 3955) (meaning t m 4133) (meaning t m 4138) (meaning t m 4501)

theorem rule7055 (p2299 p3955 p4133 p4138 p4501 : Prop) : (p4138) ∨ (¬ (p3955 ∧ p4138 ∧ p2299 ∧ p4501 ∧ p4133)) := by
  classical
  tauto

theorem initial7055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4138) ∨ (¬ (meaning t m 4500)) := by
  exact rule7055 (meaning t m 2299) (meaning t m 3955) (meaning t m 4133) (meaning t m 4138) (meaning t m 4501)

theorem rule7056 (p2299 p3955 p4133 p4138 p4501 : Prop) : (p2299) ∨ (¬ (p3955 ∧ p4138 ∧ p2299 ∧ p4501 ∧ p4133)) := by
  classical
  tauto

theorem initial7056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2299) ∨ (¬ (meaning t m 4500)) := by
  exact rule7056 (meaning t m 2299) (meaning t m 3955) (meaning t m 4133) (meaning t m 4138) (meaning t m 4501)

theorem rule7057 (p2299 p3955 p4133 p4138 p4501 : Prop) : (¬ (p3955 ∧ p4138 ∧ p2299 ∧ p4501 ∧ p4133)) ∨ (p4501) := by
  classical
  tauto

theorem initial7057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4500)) ∨ (meaning t m 4501) := by
  exact rule7057 (meaning t m 2299) (meaning t m 3955) (meaning t m 4133) (meaning t m 4138) (meaning t m 4501)

theorem rule7058 (p2299 p3955 p4133 p4138 p4501 : Prop) : (p4133) ∨ (¬ (p3955 ∧ p4138 ∧ p2299 ∧ p4501 ∧ p4133)) := by
  classical
  tauto

theorem initial7058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4133) ∨ (¬ (meaning t m 4500)) := by
  exact rule7058 (meaning t m 2299) (meaning t m 3955) (meaning t m 4133) (meaning t m 4138) (meaning t m 4501)

theorem rule7060 (p2177 p3325 p3550 p4405 p4503 : Prop) : (p3550) ∨ (¬ (p3550 ∧ p3325 ∧ p2177 ∧ p4405 ∧ p4503)) := by
  classical
  tauto

theorem initial7060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3550) ∨ (¬ (meaning t m 4502)) := by
  exact rule7060 (meaning t m 2177) (meaning t m 3325) (meaning t m 3550) (meaning t m 4405) (meaning t m 4503)

theorem rule7061 (p2177 p3325 p3550 p4405 p4503 : Prop) : (p3325) ∨ (¬ (p3550 ∧ p3325 ∧ p2177 ∧ p4405 ∧ p4503)) := by
  classical
  tauto

theorem initial7061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3325) ∨ (¬ (meaning t m 4502)) := by
  exact rule7061 (meaning t m 2177) (meaning t m 3325) (meaning t m 3550) (meaning t m 4405) (meaning t m 4503)

theorem rule7062 (p2177 p3325 p3550 p4405 p4503 : Prop) : (p2177) ∨ (¬ (p3550 ∧ p3325 ∧ p2177 ∧ p4405 ∧ p4503)) := by
  classical
  tauto

theorem initial7062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2177) ∨ (¬ (meaning t m 4502)) := by
  exact rule7062 (meaning t m 2177) (meaning t m 3325) (meaning t m 3550) (meaning t m 4405) (meaning t m 4503)

theorem rule7063 (p2177 p3325 p3550 p4405 p4503 : Prop) : (p4405) ∨ (¬ (p3550 ∧ p3325 ∧ p2177 ∧ p4405 ∧ p4503)) := by
  classical
  tauto

theorem initial7063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4405) ∨ (¬ (meaning t m 4502)) := by
  exact rule7063 (meaning t m 2177) (meaning t m 3325) (meaning t m 3550) (meaning t m 4405) (meaning t m 4503)

theorem rule7064 (p2177 p3325 p3550 p4405 p4503 : Prop) : (¬ (p3550 ∧ p3325 ∧ p2177 ∧ p4405 ∧ p4503)) ∨ (p4503) := by
  classical
  tauto

theorem initial7064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4502)) ∨ (meaning t m 4503) := by
  exact rule7064 (meaning t m 2177) (meaning t m 3325) (meaning t m 3550) (meaning t m 4405) (meaning t m 4503)

theorem rule7068 (p4500 p4502 : Prop) : (¬ (p4500 ∨ p4502)) ∨ (p4500) ∨ (p4502) := by
  classical
  tauto

theorem initial7068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4499)) ∨ (meaning t m 4500) ∨ (meaning t m 4502) := by
  exact rule7068 (meaning t m 4500) (meaning t m 4502)

theorem rule7069 (p2171 p4499 : Prop) (h : (p2171 ↔ p4499)) : (¬ p2171) ∨ (p4499) := by
  classical
  tauto

theorem initial7069 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2171)) ∨ (meaning t m 4499) := by
  have source := ElevenTheory.theory1100 t (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule7069 (meaning t m 2171) (meaning t m 4499) source

theorem rule7071 (p3988 p3989 p4433 p4506 p4507 : Prop) : (p3988) ∨ (¬ (p3988 ∧ p4506 ∧ p3989 ∧ p4507 ∧ p4433)) := by
  classical
  tauto

theorem initial7071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3988) ∨ (¬ (meaning t m 4505)) := by
  exact rule7071 (meaning t m 3988) (meaning t m 3989) (meaning t m 4433) (meaning t m 4506) (meaning t m 4507)

theorem rule7072 (p3988 p3989 p4433 p4506 p4507 : Prop) : (¬ (p3988 ∧ p4506 ∧ p3989 ∧ p4507 ∧ p4433)) ∨ (p4506) := by
  classical
  tauto

theorem initial7072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4505)) ∨ (meaning t m 4506) := by
  exact rule7072 (meaning t m 3988) (meaning t m 3989) (meaning t m 4433) (meaning t m 4506) (meaning t m 4507)

theorem rule7073 (p3988 p3989 p4433 p4506 p4507 : Prop) : (p3989) ∨ (¬ (p3988 ∧ p4506 ∧ p3989 ∧ p4507 ∧ p4433)) := by
  classical
  tauto

theorem initial7073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3989) ∨ (¬ (meaning t m 4505)) := by
  exact rule7073 (meaning t m 3988) (meaning t m 3989) (meaning t m 4433) (meaning t m 4506) (meaning t m 4507)

theorem rule7074 (p3988 p3989 p4433 p4506 p4507 : Prop) : (¬ (p3988 ∧ p4506 ∧ p3989 ∧ p4507 ∧ p4433)) ∨ (p4507) := by
  classical
  tauto

theorem initial7074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4505)) ∨ (meaning t m 4507) := by
  exact rule7074 (meaning t m 3988) (meaning t m 3989) (meaning t m 4433) (meaning t m 4506) (meaning t m 4507)

theorem rule7075 (p3988 p3989 p4433 p4506 p4507 : Prop) : (p4433) ∨ (¬ (p3988 ∧ p4506 ∧ p3989 ∧ p4507 ∧ p4433)) := by
  classical
  tauto

theorem initial7075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4433) ∨ (¬ (meaning t m 4505)) := by
  exact rule7075 (meaning t m 3988) (meaning t m 3989) (meaning t m 4433) (meaning t m 4506) (meaning t m 4507)

theorem rule7077 (p2187 p2190 p4134 p4441 p4509 : Prop) : (p4441) ∨ (¬ (p4441 ∧ p2190 ∧ p2187 ∧ p4509 ∧ p4134)) := by
  classical
  tauto

theorem initial7077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4441) ∨ (¬ (meaning t m 4508)) := by
  exact rule7077 (meaning t m 2187) (meaning t m 2190) (meaning t m 4134) (meaning t m 4441) (meaning t m 4509)

theorem rule7078 (p2187 p2190 p4134 p4441 p4509 : Prop) : (p2190) ∨ (¬ (p4441 ∧ p2190 ∧ p2187 ∧ p4509 ∧ p4134)) := by
  classical
  tauto

theorem initial7078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2190) ∨ (¬ (meaning t m 4508)) := by
  exact rule7078 (meaning t m 2187) (meaning t m 2190) (meaning t m 4134) (meaning t m 4441) (meaning t m 4509)

theorem rule7079 (p2187 p2190 p4134 p4441 p4509 : Prop) : (p2187) ∨ (¬ (p4441 ∧ p2190 ∧ p2187 ∧ p4509 ∧ p4134)) := by
  classical
  tauto

theorem initial7079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2187) ∨ (¬ (meaning t m 4508)) := by
  exact rule7079 (meaning t m 2187) (meaning t m 2190) (meaning t m 4134) (meaning t m 4441) (meaning t m 4509)

theorem rule7080 (p2187 p2190 p4134 p4441 p4509 : Prop) : (¬ (p4441 ∧ p2190 ∧ p2187 ∧ p4509 ∧ p4134)) ∨ (p4509) := by
  classical
  tauto

theorem initial7080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4508)) ∨ (meaning t m 4509) := by
  exact rule7080 (meaning t m 2187) (meaning t m 2190) (meaning t m 4134) (meaning t m 4441) (meaning t m 4509)

theorem rule7081 (p2187 p2190 p4134 p4441 p4509 : Prop) : (p4134) ∨ (¬ (p4441 ∧ p2190 ∧ p2187 ∧ p4509 ∧ p4134)) := by
  classical
  tauto

theorem initial7081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4134) ∨ (¬ (meaning t m 4508)) := by
  exact rule7081 (meaning t m 2187) (meaning t m 2190) (meaning t m 4134) (meaning t m 4441) (meaning t m 4509)

theorem rule7085 (p4505 p4508 : Prop) : (¬ (p4505 ∨ p4508)) ∨ (p4505) ∨ (p4508) := by
  classical
  tauto

theorem initial7085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4504)) ∨ (meaning t m 4505) ∨ (meaning t m 4508) := by
  exact rule7085 (meaning t m 4505) (meaning t m 4508)

theorem rule7086 (p2181 p4504 : Prop) (h : (p2181 ↔ p4504)) : (¬ p2181) ∨ (p4504) := by
  classical
  tauto

theorem initial7086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2181)) ∨ (meaning t m 4504) := by
  have source := ElevenTheory.theory1101 t (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule7086 (meaning t m 2181) (meaning t m 4504) source

theorem rule7088 (p3957 p4173 p4512 p4513 p4514 : Prop) : (¬ (p4512 ∧ p3957 ∧ p4173 ∧ p4513 ∧ p4514)) ∨ (p4512) := by
  classical
  tauto

theorem initial7088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4511)) ∨ (meaning t m 4512) := by
  exact rule7088 (meaning t m 3957) (meaning t m 4173) (meaning t m 4512) (meaning t m 4513) (meaning t m 4514)

theorem rule7089 (p3957 p4173 p4512 p4513 p4514 : Prop) : (p3957) ∨ (¬ (p4512 ∧ p3957 ∧ p4173 ∧ p4513 ∧ p4514)) := by
  classical
  tauto

theorem initial7089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3957) ∨ (¬ (meaning t m 4511)) := by
  exact rule7089 (meaning t m 3957) (meaning t m 4173) (meaning t m 4512) (meaning t m 4513) (meaning t m 4514)

theorem rule7090 (p3957 p4173 p4512 p4513 p4514 : Prop) : (p4173) ∨ (¬ (p4512 ∧ p3957 ∧ p4173 ∧ p4513 ∧ p4514)) := by
  classical
  tauto

theorem initial7090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4173) ∨ (¬ (meaning t m 4511)) := by
  exact rule7090 (meaning t m 3957) (meaning t m 4173) (meaning t m 4512) (meaning t m 4513) (meaning t m 4514)

theorem rule7092 (p3957 p4173 p4512 p4513 p4514 : Prop) : (¬ (p4512 ∧ p3957 ∧ p4173 ∧ p4513 ∧ p4514)) ∨ (p4514) := by
  classical
  tauto

theorem initial7092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4511)) ∨ (meaning t m 4514) := by
  exact rule7092 (meaning t m 3957) (meaning t m 4173) (meaning t m 4512) (meaning t m 4513) (meaning t m 4514)

theorem rule7094 (p2192 p4338 p4516 p4517 p4518 : Prop) : (¬ (p4516 ∧ p4338 ∧ p2192 ∧ p4517 ∧ p4518)) ∨ (p4516) := by
  classical
  tauto

theorem initial7094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4515)) ∨ (meaning t m 4516) := by
  exact rule7094 (meaning t m 2192) (meaning t m 4338) (meaning t m 4516) (meaning t m 4517) (meaning t m 4518)

theorem rule7095 (p2192 p4338 p4516 p4517 p4518 : Prop) : (p4338) ∨ (¬ (p4516 ∧ p4338 ∧ p2192 ∧ p4517 ∧ p4518)) := by
  classical
  tauto

theorem initial7095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4338) ∨ (¬ (meaning t m 4515)) := by
  exact rule7095 (meaning t m 2192) (meaning t m 4338) (meaning t m 4516) (meaning t m 4517) (meaning t m 4518)

theorem rule7096 (p2192 p4338 p4516 p4517 p4518 : Prop) : (p2192) ∨ (¬ (p4516 ∧ p4338 ∧ p2192 ∧ p4517 ∧ p4518)) := by
  classical
  tauto

theorem initial7096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2192) ∨ (¬ (meaning t m 4515)) := by
  exact rule7096 (meaning t m 2192) (meaning t m 4338) (meaning t m 4516) (meaning t m 4517) (meaning t m 4518)

theorem rule7098 (p2192 p4338 p4516 p4517 p4518 : Prop) : (¬ (p4516 ∧ p4338 ∧ p2192 ∧ p4517 ∧ p4518)) ∨ (p4518) := by
  classical
  tauto

theorem initial7098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4515)) ∨ (meaning t m 4518) := by
  exact rule7098 (meaning t m 2192) (meaning t m 4338) (meaning t m 4516) (meaning t m 4517) (meaning t m 4518)

theorem rule7102 (p4511 p4515 : Prop) : (¬ (p4511 ∨ p4515)) ∨ (p4511) ∨ (p4515) := by
  classical
  tauto

theorem initial7102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4510)) ∨ (meaning t m 4511) ∨ (meaning t m 4515) := by
  exact rule7102 (meaning t m 4511) (meaning t m 4515)

theorem rule7103 (p2194 p4510 : Prop) (h : (p2194 ↔ p4510)) : (¬ p2194) ∨ (p4510) := by
  classical
  tauto

theorem initial7103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2194)) ∨ (meaning t m 4510) := by
  have source := ElevenTheory.theory1102 t (m.theta 1 5) (m.theta 1 6) (m.theta 5 6)
  exact rule7103 (meaning t m 2194) (meaning t m 4510) source

theorem rule7105 (p3369 p3370 p3555 p4521 p4522 : Prop) : (p3369) ∨ (¬ (p3369 ∧ p3370 ∧ p3555 ∧ p4521 ∧ p4522)) := by
  classical
  tauto

theorem initial7105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3369) ∨ (¬ (meaning t m 4520)) := by
  exact rule7105 (meaning t m 3369) (meaning t m 3370) (meaning t m 3555) (meaning t m 4521) (meaning t m 4522)

theorem rule7106 (p3369 p3370 p3555 p4521 p4522 : Prop) : (p3370) ∨ (¬ (p3369 ∧ p3370 ∧ p3555 ∧ p4521 ∧ p4522)) := by
  classical
  tauto

theorem initial7106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3370) ∨ (¬ (meaning t m 4520)) := by
  exact rule7106 (meaning t m 3369) (meaning t m 3370) (meaning t m 3555) (meaning t m 4521) (meaning t m 4522)

theorem rule7107 (p3369 p3370 p3555 p4521 p4522 : Prop) : (p3555) ∨ (¬ (p3369 ∧ p3370 ∧ p3555 ∧ p4521 ∧ p4522)) := by
  classical
  tauto

theorem initial7107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3555) ∨ (¬ (meaning t m 4520)) := by
  exact rule7107 (meaning t m 3369) (meaning t m 3370) (meaning t m 3555) (meaning t m 4521) (meaning t m 4522)

theorem rule7108 (p3369 p3370 p3555 p4521 p4522 : Prop) : (¬ (p3369 ∧ p3370 ∧ p3555 ∧ p4521 ∧ p4522)) ∨ (p4521) := by
  classical
  tauto

theorem initial7108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4520)) ∨ (meaning t m 4521) := by
  exact rule7108 (meaning t m 3369) (meaning t m 3370) (meaning t m 3555) (meaning t m 4521) (meaning t m 4522)

theorem rule7109 (p3369 p3370 p3555 p4521 p4522 : Prop) : (¬ (p3369 ∧ p3370 ∧ p3555 ∧ p4521 ∧ p4522)) ∨ (p4522) := by
  classical
  tauto

theorem initial7109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4520)) ∨ (meaning t m 4522) := by
  exact rule7109 (meaning t m 3369) (meaning t m 3370) (meaning t m 3555) (meaning t m 4521) (meaning t m 4522)

theorem rule7111 (p2210 p3645 p4172 p4524 p4525 : Prop) : (p3645) ∨ (¬ (p3645 ∧ p4172 ∧ p2210 ∧ p4524 ∧ p4525)) := by
  classical
  tauto

theorem initial7111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3645) ∨ (¬ (meaning t m 4523)) := by
  exact rule7111 (meaning t m 2210) (meaning t m 3645) (meaning t m 4172) (meaning t m 4524) (meaning t m 4525)

theorem rule7112 (p2210 p3645 p4172 p4524 p4525 : Prop) : (p4172) ∨ (¬ (p3645 ∧ p4172 ∧ p2210 ∧ p4524 ∧ p4525)) := by
  classical
  tauto

theorem initial7112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4172) ∨ (¬ (meaning t m 4523)) := by
  exact rule7112 (meaning t m 2210) (meaning t m 3645) (meaning t m 4172) (meaning t m 4524) (meaning t m 4525)

theorem rule7113 (p2210 p3645 p4172 p4524 p4525 : Prop) : (p2210) ∨ (¬ (p3645 ∧ p4172 ∧ p2210 ∧ p4524 ∧ p4525)) := by
  classical
  tauto

theorem initial7113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2210) ∨ (¬ (meaning t m 4523)) := by
  exact rule7113 (meaning t m 2210) (meaning t m 3645) (meaning t m 4172) (meaning t m 4524) (meaning t m 4525)

theorem rule7114 (p2210 p3645 p4172 p4524 p4525 : Prop) : (¬ (p3645 ∧ p4172 ∧ p2210 ∧ p4524 ∧ p4525)) ∨ (p4524) := by
  classical
  tauto

theorem initial7114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4523)) ∨ (meaning t m 4524) := by
  exact rule7114 (meaning t m 2210) (meaning t m 3645) (meaning t m 4172) (meaning t m 4524) (meaning t m 4525)

theorem rule7115 (p2210 p3645 p4172 p4524 p4525 : Prop) : (¬ (p3645 ∧ p4172 ∧ p2210 ∧ p4524 ∧ p4525)) ∨ (p4525) := by
  classical
  tauto

theorem initial7115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4523)) ∨ (meaning t m 4525) := by
  exact rule7115 (meaning t m 2210) (meaning t m 3645) (meaning t m 4172) (meaning t m 4524) (meaning t m 4525)

theorem rule7119 (p4520 p4523 : Prop) : (¬ (p4520 ∨ p4523)) ∨ (p4520) ∨ (p4523) := by
  classical
  tauto

theorem initial7119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4519)) ∨ (meaning t m 4520) ∨ (meaning t m 4523) := by
  exact rule7119 (meaning t m 4520) (meaning t m 4523)

theorem rule7120 (p2204 p4519 : Prop) (h : (p2204 ↔ p4519)) : (¬ p2204) ∨ (p4519) := by
  classical
  tauto

theorem initial7120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2204)) ∨ (meaning t m 4519) := by
  have source := ElevenTheory.theory1103 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 5)
  exact rule7120 (meaning t m 2204) (meaning t m 4519) source

theorem rule7122 (p3696 p3697 p4120 p4528 p4529 : Prop) : (p3697) ∨ (¬ (p3697 ∧ p3696 ∧ p4120 ∧ p4528 ∧ p4529)) := by
  classical
  tauto

theorem initial7122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3697) ∨ (¬ (meaning t m 4527)) := by
  exact rule7122 (meaning t m 3696) (meaning t m 3697) (meaning t m 4120) (meaning t m 4528) (meaning t m 4529)

theorem rule7123 (p3696 p3697 p4120 p4528 p4529 : Prop) : (p3696) ∨ (¬ (p3697 ∧ p3696 ∧ p4120 ∧ p4528 ∧ p4529)) := by
  classical
  tauto

theorem initial7123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3696) ∨ (¬ (meaning t m 4527)) := by
  exact rule7123 (meaning t m 3696) (meaning t m 3697) (meaning t m 4120) (meaning t m 4528) (meaning t m 4529)

theorem rule7124 (p3696 p3697 p4120 p4528 p4529 : Prop) : (p4120) ∨ (¬ (p3697 ∧ p3696 ∧ p4120 ∧ p4528 ∧ p4529)) := by
  classical
  tauto

theorem initial7124 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4120) ∨ (¬ (meaning t m 4527)) := by
  exact rule7124 (meaning t m 3696) (meaning t m 3697) (meaning t m 4120) (meaning t m 4528) (meaning t m 4529)

theorem rule7126 (p3696 p3697 p4120 p4528 p4529 : Prop) : (¬ (p3697 ∧ p3696 ∧ p4120 ∧ p4528 ∧ p4529)) ∨ (p4529) := by
  classical
  tauto

theorem initial7126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4527)) ∨ (meaning t m 4529) := by
  exact rule7126 (meaning t m 3696) (meaning t m 3697) (meaning t m 4120) (meaning t m 4528) (meaning t m 4529)

theorem rule7128 (p2220 p4115 p4238 p4531 p4532 : Prop) : (p4115) ∨ (¬ (p4115 ∧ p4238 ∧ p2220 ∧ p4531 ∧ p4532)) := by
  classical
  tauto

theorem initial7128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4115) ∨ (¬ (meaning t m 4530)) := by
  exact rule7128 (meaning t m 2220) (meaning t m 4115) (meaning t m 4238) (meaning t m 4531) (meaning t m 4532)

theorem rule7129 (p2220 p4115 p4238 p4531 p4532 : Prop) : (p4238) ∨ (¬ (p4115 ∧ p4238 ∧ p2220 ∧ p4531 ∧ p4532)) := by
  classical
  tauto

theorem initial7129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4238) ∨ (¬ (meaning t m 4530)) := by
  exact rule7129 (meaning t m 2220) (meaning t m 4115) (meaning t m 4238) (meaning t m 4531) (meaning t m 4532)

theorem rule7130 (p2220 p4115 p4238 p4531 p4532 : Prop) : (p2220) ∨ (¬ (p4115 ∧ p4238 ∧ p2220 ∧ p4531 ∧ p4532)) := by
  classical
  tauto

theorem initial7130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2220) ∨ (¬ (meaning t m 4530)) := by
  exact rule7130 (meaning t m 2220) (meaning t m 4115) (meaning t m 4238) (meaning t m 4531) (meaning t m 4532)

theorem rule7132 (p2220 p4115 p4238 p4531 p4532 : Prop) : (¬ (p4115 ∧ p4238 ∧ p2220 ∧ p4531 ∧ p4532)) ∨ (p4532) := by
  classical
  tauto

theorem initial7132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4530)) ∨ (meaning t m 4532) := by
  exact rule7132 (meaning t m 2220) (meaning t m 4115) (meaning t m 4238) (meaning t m 4531) (meaning t m 4532)

theorem rule7136 (p4527 p4530 : Prop) : (¬ (p4527 ∨ p4530)) ∨ (p4527) ∨ (p4530) := by
  classical
  tauto

theorem initial7136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4526)) ∨ (meaning t m 4527) ∨ (meaning t m 4530) := by
  exact rule7136 (meaning t m 4527) (meaning t m 4530)

theorem rule7137 (p2214 p4526 : Prop) (h : (p2214 ↔ p4526)) : (¬ p2214) ∨ (p4526) := by
  classical
  tauto

theorem initial7137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2214)) ∨ (meaning t m 4526) := by
  have source := ElevenTheory.theory1104 t (m.theta 0 5) (m.theta 0 8) (m.theta 5 8)
  exact rule7137 (meaning t m 2214) (meaning t m 4526) source

theorem rule7139 (p2027 p2352 p3646 p3660 p3989 p4533 : Prop) (h : p2027 ∨ (¬ p4533) ∨ (¬ p3646) ∨ (¬ p3660) ∨ (¬ p3989) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2352) ∨ (¬ p3646) ∨ (¬ p3660) ∨ (¬ p3989) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial7139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory1105 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule7139 (meaning t m 2027) (meaning t m 2352) (meaning t m 3646) (meaning t m 3660) (meaning t m 3989) (meaning t m 4533) source

theorem rule7140 (p2589 p3904 p4109 p4533 p4536 : Prop) : (p3904) ∨ (¬ (p3904 ∧ p4109 ∧ p2589 ∧ p4536 ∧ p4533)) := by
  classical
  tauto

theorem initial7140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3904) ∨ (¬ (meaning t m 4535)) := by
  exact rule7140 (meaning t m 2589) (meaning t m 3904) (meaning t m 4109) (meaning t m 4533) (meaning t m 4536)

theorem rule7141 (p2589 p3904 p4109 p4533 p4536 : Prop) : (p4109) ∨ (¬ (p3904 ∧ p4109 ∧ p2589 ∧ p4536 ∧ p4533)) := by
  classical
  tauto

theorem initial7141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4109) ∨ (¬ (meaning t m 4535)) := by
  exact rule7141 (meaning t m 2589) (meaning t m 3904) (meaning t m 4109) (meaning t m 4533) (meaning t m 4536)

theorem rule7142 (p2589 p3904 p4109 p4533 p4536 : Prop) : (p2589) ∨ (¬ (p3904 ∧ p4109 ∧ p2589 ∧ p4536 ∧ p4533)) := by
  classical
  tauto

theorem initial7142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2589) ∨ (¬ (meaning t m 4535)) := by
  exact rule7142 (meaning t m 2589) (meaning t m 3904) (meaning t m 4109) (meaning t m 4533) (meaning t m 4536)

theorem rule7144 (p2589 p3904 p4109 p4533 p4536 : Prop) : (p4533) ∨ (¬ (p3904 ∧ p4109 ∧ p2589 ∧ p4536 ∧ p4533)) := by
  classical
  tauto

theorem initial7144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4533) ∨ (¬ (meaning t m 4535)) := by
  exact rule7144 (meaning t m 2589) (meaning t m 3904) (meaning t m 4109) (meaning t m 4533) (meaning t m 4536)

theorem rule7146 (p2230 p4031 p4399 p4538 p4539 : Prop) : (p4031) ∨ (¬ (p4031 ∧ p4399 ∧ p2230 ∧ p4538 ∧ p4539)) := by
  classical
  tauto

theorem initial7146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4031) ∨ (¬ (meaning t m 4537)) := by
  exact rule7146 (meaning t m 2230) (meaning t m 4031) (meaning t m 4399) (meaning t m 4538) (meaning t m 4539)

theorem rule7147 (p2230 p4031 p4399 p4538 p4539 : Prop) : (p4399) ∨ (¬ (p4031 ∧ p4399 ∧ p2230 ∧ p4538 ∧ p4539)) := by
  classical
  tauto

theorem initial7147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4399) ∨ (¬ (meaning t m 4537)) := by
  exact rule7147 (meaning t m 2230) (meaning t m 4031) (meaning t m 4399) (meaning t m 4538) (meaning t m 4539)

theorem rule7148 (p2230 p4031 p4399 p4538 p4539 : Prop) : (p2230) ∨ (¬ (p4031 ∧ p4399 ∧ p2230 ∧ p4538 ∧ p4539)) := by
  classical
  tauto

theorem initial7148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2230) ∨ (¬ (meaning t m 4537)) := by
  exact rule7148 (meaning t m 2230) (meaning t m 4031) (meaning t m 4399) (meaning t m 4538) (meaning t m 4539)

theorem rule7150 (p2230 p4031 p4399 p4538 p4539 : Prop) : (¬ (p4031 ∧ p4399 ∧ p2230 ∧ p4538 ∧ p4539)) ∨ (p4539) := by
  classical
  tauto

theorem initial7150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4537)) ∨ (meaning t m 4539) := by
  exact rule7150 (meaning t m 2230) (meaning t m 4031) (meaning t m 4399) (meaning t m 4538) (meaning t m 4539)

theorem rule7154 (p4535 p4537 : Prop) : (¬ (p4535 ∨ p4537)) ∨ (p4535) ∨ (p4537) := by
  classical
  tauto

theorem initial7154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4534)) ∨ (meaning t m 4535) ∨ (meaning t m 4537) := by
  exact rule7154 (meaning t m 4535) (meaning t m 4537)

theorem rule7155 (p2224 p4534 : Prop) (h : (p2224 ↔ p4534)) : (¬ p2224) ∨ (p4534) := by
  classical
  tauto

theorem initial7155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2224)) ∨ (meaning t m 4534) := by
  have source := ElevenTheory.theory1106 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5)
  exact rule7155 (meaning t m 2224) (meaning t m 4534) source

theorem rule7159 (p2244 p2251 : Prop) : (p2244) ∨ (p2251) ∨ (¬ (p2244 ∨ p2251)) := by
  classical
  tauto

theorem initial7159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2244) ∨ (meaning t m 2251) ∨ (¬ (meaning t m 4540)) := by
  exact rule7159 (meaning t m 2244) (meaning t m 2251)

theorem rule7160 (p2235 p4540 : Prop) (h : (p2235 ↔ p4540)) : (¬ p2235) ∨ (p4540) := by
  classical
  tauto

theorem initial7160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2235)) ∨ (meaning t m 4540) := by
  have source := ElevenTheory.theory1107 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3)
  exact rule7160 (meaning t m 2235) (meaning t m 4540) source

theorem rule7183 (p3553 p3919 p4548 p4549 p4550 : Prop) : (p3919) ∨ (¬ (p3919 ∧ p4548 ∧ p3553 ∧ p4549 ∧ p4550)) := by
  classical
  tauto

theorem initial7183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3919) ∨ (¬ (meaning t m 4547)) := by
  exact rule7183 (meaning t m 3553) (meaning t m 3919) (meaning t m 4548) (meaning t m 4549) (meaning t m 4550)

theorem rule7184 (p3553 p3919 p4548 p4549 p4550 : Prop) : (¬ (p3919 ∧ p4548 ∧ p3553 ∧ p4549 ∧ p4550)) ∨ (p4548) := by
  classical
  tauto

theorem initial7184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4547)) ∨ (meaning t m 4548) := by
  exact rule7184 (meaning t m 3553) (meaning t m 3919) (meaning t m 4548) (meaning t m 4549) (meaning t m 4550)

theorem rule7185 (p3553 p3919 p4548 p4549 p4550 : Prop) : (p3553) ∨ (¬ (p3919 ∧ p4548 ∧ p3553 ∧ p4549 ∧ p4550)) := by
  classical
  tauto

theorem initial7185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3553) ∨ (¬ (meaning t m 4547)) := by
  exact rule7185 (meaning t m 3553) (meaning t m 3919) (meaning t m 4548) (meaning t m 4549) (meaning t m 4550)

theorem rule7187 (p3553 p3919 p4548 p4549 p4550 : Prop) : (¬ (p3919 ∧ p4548 ∧ p3553 ∧ p4549 ∧ p4550)) ∨ (p4550) := by
  classical
  tauto

theorem initial7187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4547)) ∨ (meaning t m 4550) := by
  exact rule7187 (meaning t m 3553) (meaning t m 3919) (meaning t m 4548) (meaning t m 4549) (meaning t m 4550)

theorem rule7189 (p2264 p4041 p4044 p4378 p4552 : Prop) : (p4378) ∨ (¬ (p4378 ∧ p4044 ∧ p2264 ∧ p4552 ∧ p4041)) := by
  classical
  tauto

theorem initial7189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4378) ∨ (¬ (meaning t m 4551)) := by
  exact rule7189 (meaning t m 2264) (meaning t m 4041) (meaning t m 4044) (meaning t m 4378) (meaning t m 4552)

theorem rule7190 (p2264 p4041 p4044 p4378 p4552 : Prop) : (p4044) ∨ (¬ (p4378 ∧ p4044 ∧ p2264 ∧ p4552 ∧ p4041)) := by
  classical
  tauto

theorem initial7190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4044) ∨ (¬ (meaning t m 4551)) := by
  exact rule7190 (meaning t m 2264) (meaning t m 4041) (meaning t m 4044) (meaning t m 4378) (meaning t m 4552)

theorem rule7191 (p2264 p4041 p4044 p4378 p4552 : Prop) : (p2264) ∨ (¬ (p4378 ∧ p4044 ∧ p2264 ∧ p4552 ∧ p4041)) := by
  classical
  tauto

theorem initial7191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2264) ∨ (¬ (meaning t m 4551)) := by
  exact rule7191 (meaning t m 2264) (meaning t m 4041) (meaning t m 4044) (meaning t m 4378) (meaning t m 4552)

theorem rule7193 (p2264 p4041 p4044 p4378 p4552 : Prop) : (p4041) ∨ (¬ (p4378 ∧ p4044 ∧ p2264 ∧ p4552 ∧ p4041)) := by
  classical
  tauto

theorem initial7193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4041) ∨ (¬ (meaning t m 4551)) := by
  exact rule7193 (meaning t m 2264) (meaning t m 4041) (meaning t m 4044) (meaning t m 4378) (meaning t m 4552)

theorem rule7197 (p4547 p4551 : Prop) : (¬ (p4547 ∨ p4551)) ∨ (p4547) ∨ (p4551) := by
  classical
  tauto

theorem initial7197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4546)) ∨ (meaning t m 4547) ∨ (meaning t m 4551) := by
  exact rule7197 (meaning t m 4547) (meaning t m 4551)

theorem rule7198 (p2258 p4546 : Prop) (h : (p2258 ↔ p4546)) : (¬ p2258) ∨ (p4546) := by
  classical
  tauto

theorem initial7198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2258)) ∨ (meaning t m 4546) := by
  have source := ElevenTheory.theory1110 t (m.theta 3 7) (m.theta 3 8) (m.theta 7 8)
  exact rule7198 (meaning t m 2258) (meaning t m 4546) source

theorem rule7200 (p3097 p4204 p4275 p4555 p4556 : Prop) : (p4204) ∨ (¬ (p4204 ∧ p4275 ∧ p3097 ∧ p4555 ∧ p4556)) := by
  classical
  tauto

theorem initial7200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4204) ∨ (¬ (meaning t m 4554)) := by
  exact rule7200 (meaning t m 3097) (meaning t m 4204) (meaning t m 4275) (meaning t m 4555) (meaning t m 4556)

theorem rule7201 (p3097 p4204 p4275 p4555 p4556 : Prop) : (p4275) ∨ (¬ (p4204 ∧ p4275 ∧ p3097 ∧ p4555 ∧ p4556)) := by
  classical
  tauto

theorem initial7201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4275) ∨ (¬ (meaning t m 4554)) := by
  exact rule7201 (meaning t m 3097) (meaning t m 4204) (meaning t m 4275) (meaning t m 4555) (meaning t m 4556)

theorem rule7202 (p3097 p4204 p4275 p4555 p4556 : Prop) : (p3097) ∨ (¬ (p4204 ∧ p4275 ∧ p3097 ∧ p4555 ∧ p4556)) := by
  classical
  tauto

theorem initial7202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3097) ∨ (¬ (meaning t m 4554)) := by
  exact rule7202 (meaning t m 3097) (meaning t m 4204) (meaning t m 4275) (meaning t m 4555) (meaning t m 4556)

theorem rule7203 (p3097 p4204 p4275 p4555 p4556 : Prop) : (¬ (p4204 ∧ p4275 ∧ p3097 ∧ p4555 ∧ p4556)) ∨ (p4555) := by
  classical
  tauto

theorem initial7203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4554)) ∨ (meaning t m 4555) := by
  exact rule7203 (meaning t m 3097) (meaning t m 4204) (meaning t m 4275) (meaning t m 4555) (meaning t m 4556)

end SunPrize.SMT
