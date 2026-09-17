import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory052
import SunPrize.Certificate.Theory053
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule29868 (p2027 p2274 p3434 p4137 p4203 p4361 p4396 p4777 : Prop) (h : (¬ p4396) ∨ (¬ p4361) ∨ (¬ p4137) ∨ (¬ p4203) ∨ p2027 ∨ (¬ p3434) ∨ (¬ p4777) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2274) ∨ (¬ p3434) ∨ (¬ p4137) ∨ (¬ p4203) ∨ (¬ p4361) ∨ (¬ p4396) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial29868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory19124 t (m.theta 2 7) (m.theta 3 7) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule29868 (meaning t m 2027) (meaning t m 2274) (meaning t m 3434) (meaning t m 4137) (meaning t m 4203) (meaning t m 4361) (meaning t m 4396) (meaning t m 4777) source

theorem rule29871 (p1998 p2027 p2307 p2363 p2406 p2409 p2962 p3325 p4109 p4348 : Prop) (h : (¬ p2406) ∨ (¬ p2962) ∨ (¬ p4348) ∨ (¬ p2307) ∨ (¬ p1998) ∨ (¬ p4109) ∨ (¬ p3325) ∨ p2027 ∨ (¬ p2363) ∨ p2409) : (¬ p1998) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2363) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2962) ∨ (¬ p3325) ∨ (¬ p4109) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial29871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory19127 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 4) (m.theta 4 5) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29871 (meaning t m 1998) (meaning t m 2027) (meaning t m 2307) (meaning t m 2363) (meaning t m 2406) (meaning t m 2409) (meaning t m 2962) (meaning t m 3325) (meaning t m 4109) (meaning t m 4348) source

theorem rule29872 (p2027 p2307 p2396 p2761 p3583 p3954 p4316 p5017 p5405 p5740 : Prop) (h : (¬ p3954) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p5017) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p5405) ∨ (¬ p3583) ∨ (¬ p5740) ∨ (¬ p4316)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4316) ∨ (¬ p5017) ∨ (¬ p5405) ∨ (¬ p5740) := by
  classical
  tauto

theorem initial29872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 5017)) ∨ (¬ (meaning t m 5405)) ∨ (¬ (meaning t m 5740)) := by
  have source := ElevenTheory.theory19128 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 10) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule29872 (meaning t m 2027) (meaning t m 2307) (meaning t m 2396) (meaning t m 2761) (meaning t m 3583) (meaning t m 3954) (meaning t m 4316) (meaning t m 5017) (meaning t m 5405) (meaning t m 5740) source

theorem rule29875 (p2027 p2331 p2427 p3005 p3556 p3904 p3945 p4117 p4195 p4382 p4550 p4729 p4948 : Prop) (h : (¬ p4382) ∨ (¬ p3945) ∨ (¬ p4948) ∨ (¬ p2331) ∨ (¬ p3904) ∨ (¬ p4195) ∨ (¬ p3556) ∨ (¬ p4729) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p4550) ∨ (¬ p4117) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2427) ∨ (¬ p3005) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p3945) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4382) ∨ (¬ p4550) ∨ (¬ p4729) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial29875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory19131 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8) (m.theta 7 9)
  exact rule29875 (meaning t m 2027) (meaning t m 2331) (meaning t m 2427) (meaning t m 3005) (meaning t m 3556) (meaning t m 3904) (meaning t m 3945) (meaning t m 4117) (meaning t m 4195) (meaning t m 4382) (meaning t m 4550) (meaning t m 4729) (meaning t m 4948) source

theorem rule29877 (p2027 p2098 p2589 p3266 p3609 p4235 p4729 p4831 p5660 : Prop) (h : (¬ p2589) ∨ (¬ p5660) ∨ (¬ p4729) ∨ (¬ p4235) ∨ (¬ p4831) ∨ p2027 ∨ (¬ p2098) ∨ (¬ p3609) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2589) ∨ (¬ p3266) ∨ (¬ p3609) ∨ (¬ p4235) ∨ (¬ p4729) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial29877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory19133 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule29877 (meaning t m 2027) (meaning t m 2098) (meaning t m 2589) (meaning t m 3266) (meaning t m 3609) (meaning t m 4235) (meaning t m 4729) (meaning t m 4831) (meaning t m 5660) source

theorem rule29878 (p2027 p2427 p3063 p3093 p3347 p3556 p3880 p3904 p3954 p4134 p5216 : Prop) (h : (¬ p3904) ∨ (¬ p3880) ∨ (¬ p3347) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p4134) ∨ (¬ p3556) ∨ (¬ p3063) ∨ (¬ p3954) ∨ (¬ p3093) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3347) ∨ (¬ p3556) ∨ (¬ p3880) ∨ (¬ p3904) ∨ (¬ p3954) ∨ (¬ p4134) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial29878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory19134 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule29878 (meaning t m 2027) (meaning t m 2427) (meaning t m 3063) (meaning t m 3093) (meaning t m 3347) (meaning t m 3556) (meaning t m 3880) (meaning t m 3904) (meaning t m 3954) (meaning t m 4134) (meaning t m 5216) source

theorem rule29883 (p2027 p2441 p2870 p2881 p3644 p4885 : Prop) (h : p2027 ∨ (¬ p2881) ∨ (¬ p3644) ∨ (¬ p4885) ∨ (¬ p2441) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3644) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial29883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory19139 t (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule29883 (meaning t m 2027) (meaning t m 2441) (meaning t m 2870) (meaning t m 2881) (meaning t m 3644) (meaning t m 4885) source

theorem rule29884 (p1997 p2027 p2766 p3979 p3988 p4110 p4347 p5568 : Prop) (h : (¬ p4110) ∨ p2027 ∨ (¬ p4347) ∨ p2766 ∨ (¬ p3979) ∨ (¬ p3988) ∨ (¬ p1997) ∨ (¬ p5568)) : (¬ p1997) ∨ (p2027) ∨ (p2766) ∨ (¬ p3979) ∨ (¬ p3988) ∨ (¬ p4110) ∨ (¬ p4347) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial29884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory19140 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule29884 (meaning t m 1997) (meaning t m 2027) (meaning t m 2766) (meaning t m 3979) (meaning t m 3988) (meaning t m 4110) (meaning t m 4347) (meaning t m 5568) source

theorem rule29886 (p2860 p3879 p4110 p4316 : Prop) (h : (¬ p2860) ∨ (¬ p4316) ∨ (¬ p4110) ∨ (¬ p3879)) : (¬ p2860) ∨ (¬ p3879) ∨ (¬ p4110) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial29886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory19142 (m.theta 2 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule29886 (meaning t m 2860) (meaning t m 3879) (meaning t m 4110) (meaning t m 4316) source

theorem rule29888 (p2027 p2143 p2493 p2553 p2598 p3583 p3590 p3646 p3989 p4501 p4737 : Prop) (h : (¬ p2493) ∨ (¬ p4501) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p3590) ∨ (¬ p3989) ∨ (¬ p4737) ∨ (¬ p3646) ∨ (¬ p3583) ∨ (¬ p2143) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p3583) ∨ (¬ p3590) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4501) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial29888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory19144 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule29888 (meaning t m 2027) (meaning t m 2143) (meaning t m 2493) (meaning t m 2553) (meaning t m 2598) (meaning t m 3583) (meaning t m 3590) (meaning t m 3646) (meaning t m 3989) (meaning t m 4501) (meaning t m 4737) source

theorem rule29889 (p1987 p2027 p2462 p2881 p2957 p3551 p3690 p4315 p4984 : Prop) (h : p2027 ∨ (¬ p2957) ∨ (¬ p3551) ∨ (¬ p4984) ∨ p2462 ∨ (¬ p3690) ∨ (¬ p2881) ∨ (¬ p1987) ∨ (¬ p4315)) : (¬ p1987) ∨ (p2027) ∨ (p2462) ∨ (¬ p2881) ∨ (¬ p2957) ∨ (¬ p3551) ∨ (¬ p3690) ∨ (¬ p4315) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial29889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory19145 t (m.theta 0 5) (m.theta 0 7) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29889 (meaning t m 1987) (meaning t m 2027) (meaning t m 2462) (meaning t m 2881) (meaning t m 2957) (meaning t m 3551) (meaning t m 3690) (meaning t m 4315) (meaning t m 4984) source

theorem rule29892 (p2210 p3954 p4874 : Prop) (h : (¬ p4874) ∨ (¬ p2210) ∨ (¬ p3954)) : (¬ p2210) ∨ (¬ p3954) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial29892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory19148 (m.theta 0 1) (m.theta 1 2) (m.theta 1 5)
  exact rule29892 (meaning t m 2210) (meaning t m 3954) (meaning t m 4874) source

theorem rule29894 (p2027 p2295 p2313 p2383 p3956 p4976 : Prop) (h : (¬ p2383) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p4976) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3956) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial29894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory19150 t (m.theta 0 6) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule29894 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2383) (meaning t m 3956) (meaning t m 4976) source

theorem rule29899 (p2027 p2963 p3276 p3324 p3355 p3366 p3519 p3950 p4236 p4347 p4376 p4381 : Prop) (h : (¬ p3519) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p4381) ∨ (¬ p4347) ∨ (¬ p4376) ∨ (¬ p4236) ∨ (¬ p2963) ∨ (¬ p3366) ∨ (¬ p3324) ∨ (¬ p3355) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3276) ∨ (¬ p3324) ∨ (¬ p3355) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4347) ∨ (¬ p4376) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial29899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory19155 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule29899 (meaning t m 2027) (meaning t m 2963) (meaning t m 3276) (meaning t m 3324) (meaning t m 3355) (meaning t m 3366) (meaning t m 3519) (meaning t m 3950) (meaning t m 4236) (meaning t m 4347) (meaning t m 4376) (meaning t m 4381) source

theorem rule29900 (p2839 p3688 p3985 : Prop) (h : (¬ p2839) ∨ (¬ p3985) ∨ (¬ p3688)) : (¬ p2839) ∨ (¬ p3688) ∨ (¬ p3985) := by
  classical
  tauto

theorem initial29900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3985)) := by
  have source := ElevenTheory.theory19156 (m.theta 1 2) (m.theta 2 5) (m.theta 2 6)
  exact rule29900 (meaning t m 2839) (meaning t m 3688) (meaning t m 3985) source

theorem rule29901 (p1987 p2027 p2104 p2696 p2764 p4340 p4444 : Prop) (h : (¬ p4444) ∨ p2764 ∨ (¬ p2696) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p2104) ∨ (¬ p4340)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2104) ∨ (¬ p2696) ∨ (p2764) ∨ (¬ p4340) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial29901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory19157 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 8) (m.theta 8 9) (m.theta 9 10)
  exact rule29901 (meaning t m 1987) (meaning t m 2027) (meaning t m 2104) (meaning t m 2696) (meaning t m 2764) (meaning t m 4340) (meaning t m 4444) source

theorem rule29902 (p2027 p2363 p2598 p2911 p3201 p3860 p4261 p4503 p4733 : Prop) (h : p2027 ∨ (¬ p4733) ∨ (¬ p3201) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p4503) ∨ (¬ p2911) ∨ (¬ p3860) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4503) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial29902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory19158 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29902 (meaning t m 2027) (meaning t m 2363) (meaning t m 2598) (meaning t m 2911) (meaning t m 3201) (meaning t m 3860) (meaning t m 4261) (meaning t m 4503) (meaning t m 4733) source

theorem rule29904 (p2027 p2299 p3083 p3742 p4370 p4712 p5307 : Prop) (h : (¬ p2299) ∨ (¬ p3742) ∨ (¬ p4370) ∨ (¬ p5307) ∨ (¬ p4712) ∨ p2027 ∨ (¬ p3083)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3083) ∨ (¬ p3742) ∨ (¬ p4370) ∨ (¬ p4712) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial29904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4370)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory19160 t (m.theta 1 8) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule29904 (meaning t m 2027) (meaning t m 2299) (meaning t m 3083) (meaning t m 3742) (meaning t m 4370) (meaning t m 4712) (meaning t m 5307) source

theorem rule29905 (p2027 p2122 p2177 p2252 p2657 p2750 p2829 p3742 p4278 p4666 : Prop) (h : (¬ p2177) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p4666) ∨ (¬ p3742) ∨ (¬ p2252) ∨ (¬ p2122) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial29905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory19161 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29905 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2829) (meaning t m 3742) (meaning t m 4278) (meaning t m 4666) source

theorem rule29908 (p1998 p2027 p2177 p2307 p2765 p3125 p3946 : Prop) (h : (¬ p2177) ∨ p2765 ∨ p2027 ∨ (¬ p3125) ∨ (¬ p1998) ∨ (¬ p2307) ∨ (¬ p3946)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (p2765) ∨ (¬ p3125) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial29908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory19164 t (m.theta 0 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule29908 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2765) (meaning t m 3125) (meaning t m 3946) source

theorem rule29912 (p2553 p3564 p4025 : Prop) (h : (¬ p4025) ∨ (¬ p3564) ∨ p2553) : (p2553) ∨ (¬ p3564) ∨ (¬ p4025) := by
  classical
  tauto

theorem initial29912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2553) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4025)) := by
  have source := ElevenTheory.theory19168 (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule29912 (meaning t m 2553) (meaning t m 3564) (meaning t m 4025) source

theorem rule29913 (p1982 p2027 p2470 p2528 p2542 p2545 p2589 : Prop) (h : (¬ p2589) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2528) ∨ p2545 ∨ (¬ p2542)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2589) := by
  classical
  tauto

theorem initial29913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2589)) := by
  have source := ElevenTheory.theory19169 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule29913 (meaning t m 1982) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2542) (meaning t m 2545) (meaning t m 2589) source

theorem rule29914 (p2440 p3237 p3343 : Prop) (h : (¬ p3343) ∨ (¬ p2440) ∨ (¬ p3237)) : (¬ p2440) ∨ (¬ p3237) ∨ (¬ p3343) := by
  classical
  tauto

theorem initial29914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3237)) ∨ (¬ (meaning t m 3343)) := by
  have source := ElevenTheory.theory19170 (m.theta 3 4) (m.theta 4 5) (m.theta 4 9)
  exact rule29914 (meaning t m 2440) (meaning t m 3237) (meaning t m 3343) source

theorem rule29916 (p2027 p2657 p2707 p2780 p3361 p3366 p3434 p3644 p3742 p4668 p4842 : Prop) (h : (¬ p3366) ∨ (¬ p2780) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3742) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p4668) ∨ (¬ p4842) ∨ (¬ p2657) ∨ (¬ p3361)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2707) ∨ (¬ p2780) ∨ (¬ p3361) ∨ (¬ p3366) ∨ (¬ p3434) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4668) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial29916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory19172 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29916 (meaning t m 2027) (meaning t m 2657) (meaning t m 2707) (meaning t m 2780) (meaning t m 3361) (meaning t m 3366) (meaning t m 3434) (meaning t m 3644) (meaning t m 3742) (meaning t m 4668) (meaning t m 4842) source

theorem rule29917 (p1999 p2027 p2187 p2202 p2563 p3319 p3923 : Prop) (h : (¬ p3319) ∨ (¬ p1999) ∨ p2202 ∨ (¬ p2187) ∨ (¬ p2563) ∨ (¬ p3923) ∨ p2027) : (¬ p1999) ∨ (p2027) ∨ (¬ p2187) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3319) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial29917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory19173 t (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule29917 (meaning t m 1999) (meaning t m 2027) (meaning t m 2187) (meaning t m 2202) (meaning t m 2563) (meaning t m 3319) (meaning t m 3923) source

theorem rule29920 (p1977 p2027 p2191 p2462 p3156 p3368 p3690 p4320 : Prop) (h : (¬ p3368) ∨ p2462 ∨ (¬ p3156) ∨ (¬ p3690) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p4320) ∨ (¬ p2191)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2191) ∨ (p2462) ∨ (¬ p3156) ∨ (¬ p3368) ∨ (¬ p3690) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial29920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory19176 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 9)
  exact rule29920 (meaning t m 1977) (meaning t m 2027) (meaning t m 2191) (meaning t m 2462) (meaning t m 3156) (meaning t m 3368) (meaning t m 3690) (meaning t m 4320) source

theorem rule29926 (p1982 p2027 p2138 p2187 p2363 p2774 p3474 p4185 : Prop) (h : (¬ p4185) ∨ (¬ p2138) ∨ p3474 ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2774) ∨ (¬ p2363)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2774) ∨ (p3474) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial29926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2774)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory19182 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule29926 (meaning t m 1982) (meaning t m 2027) (meaning t m 2138) (meaning t m 2187) (meaning t m 2363) (meaning t m 2774) (meaning t m 3474) (meaning t m 4185) source

theorem rule29933 (p1976 p2027 p2122 p2313 p2766 p2778 p4347 p4358 : Prop) (h : p2766 ∨ (¬ p1976) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2778) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p4347)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (p2766) ∨ (¬ p2778) ∨ (¬ p4347) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial29933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory19189 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule29933 (meaning t m 1976) (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2766) (meaning t m 2778) (meaning t m 4347) (meaning t m 4358) source

theorem rule29934 (p1990 p2027 p2284 p3128 p3461 p4282 p4322 p4363 : Prop) (h : p3128 ∨ (¬ p3461) ∨ (¬ p4282) ∨ (¬ p4363) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p4322)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (p3128) ∨ (¬ p3461) ∨ (¬ p4282) ∨ (¬ p4322) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial29934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory19190 t (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule29934 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 3128) (meaning t m 3461) (meaning t m 4282) (meaning t m 4322) (meaning t m 4363) source

theorem rule29937 (p2027 p2230 p2427 p2881 p3688 p3954 p4358 p4503 p5190 : Prop) (h : (¬ p3688) ∨ (¬ p4503) ∨ (¬ p3954) ∨ (¬ p2230) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p5190) ∨ (¬ p4358)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4358) ∨ (¬ p4503) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial29937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory19193 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule29937 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2881) (meaning t m 3688) (meaning t m 3954) (meaning t m 4358) (meaning t m 4503) (meaning t m 5190) source

theorem rule29938 (p2027 p2156 p2246 p2608 p2744 p2958 p3506 p3745 p3817 p4191 p4366 p4421 p4621 : Prop) (h : (¬ p3506) ∨ (¬ p4621) ∨ (¬ p2246) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p4421) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p2958) ∨ (¬ p2156) ∨ (¬ p3745) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3506) ∨ (¬ p3745) ∨ (¬ p3817) ∨ (¬ p4191) ∨ (¬ p4366) ∨ (¬ p4421) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial29938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory19194 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 6) (m.theta 3 9) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29938 (meaning t m 2027) (meaning t m 2156) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 2958) (meaning t m 3506) (meaning t m 3745) (meaning t m 3817) (meaning t m 4191) (meaning t m 4366) (meaning t m 4421) (meaning t m 4621) source

theorem rule29940 (p1992 p2027 p2608 p2766 p3548 p4348 p4366 : Prop) (h : p2027 ∨ p2766 ∨ (¬ p2608) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p1992) ∨ (¬ p3548)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2766) ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial29940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory19196 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 7 8) (m.theta 8 9)
  exact rule29940 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2766) (meaning t m 3548) (meaning t m 4348) (meaning t m 4366) source

theorem rule29941 (p2027 p2247 p2299 p2449 p2579 p2744 p3037 p3366 p3399 p3822 p3905 p4390 p4668 : Prop) (h : (¬ p2579) ∨ (¬ p2299) ∨ (¬ p4668) ∨ (¬ p3822) ∨ (¬ p3905) ∨ (¬ p2247) ∨ (¬ p2744) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3366) ∨ (¬ p4390) ∨ (¬ p3037) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2449) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3037) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3822) ∨ (¬ p3905) ∨ (¬ p4390) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial29941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory19197 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 6) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29941 (meaning t m 2027) (meaning t m 2247) (meaning t m 2299) (meaning t m 2449) (meaning t m 2579) (meaning t m 2744) (meaning t m 3037) (meaning t m 3366) (meaning t m 3399) (meaning t m 3822) (meaning t m 3905) (meaning t m 4390) (meaning t m 4668) source

theorem rule29943 (p2027 p2417 p3201 p3821 p4727 p5197 : Prop) (h : (¬ p3201) ∨ (¬ p2417) ∨ (¬ p5197) ∨ (¬ p4727) ∨ p2027 ∨ (¬ p3821)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3201) ∨ (¬ p3821) ∨ (¬ p4727) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial29943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4727)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory19199 t (m.theta 0 4) (m.theta 0 7) (m.theta 2 4) (m.theta 4 7) (m.theta 7 9)
  exact rule29943 (meaning t m 2027) (meaning t m 2417) (meaning t m 3201) (meaning t m 3821) (meaning t m 4727) (meaning t m 5197) source

theorem rule29944 (p1990 p2027 p2699 p3051 p3319 p3486 p3744 p4172 p4338 : Prop) (h : (¬ p3744) ∨ p2699 ∨ (¬ p4172) ∨ (¬ p3319) ∨ (¬ p4338) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p3486)) : (¬ p1990) ∨ (p2027) ∨ (p2699) ∨ (¬ p3051) ∨ (¬ p3319) ∨ (¬ p3486) ∨ (¬ p3744) ∨ (¬ p4172) ∨ (¬ p4338) := by
  classical
  tauto

theorem initial29944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4338)) := by
  have source := ElevenTheory.theory19200 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule29944 (meaning t m 1990) (meaning t m 2027) (meaning t m 2699) (meaning t m 3051) (meaning t m 3319) (meaning t m 3486) (meaning t m 3744) (meaning t m 4172) (meaning t m 4338) source

theorem rule29947 (p2027 p2630 p2656 p2922 p3347 p3879 p4315 p4646 : Prop) (h : (¬ p4646) ∨ (¬ p3879) ∨ (¬ p2922) ∨ (¬ p2630) ∨ (¬ p3347) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p4315)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2922) ∨ (¬ p3347) ∨ (¬ p3879) ∨ (¬ p4315) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial29947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory19203 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7)
  exact rule29947 (meaning t m 2027) (meaning t m 2630) (meaning t m 2656) (meaning t m 2922) (meaning t m 3347) (meaning t m 3879) (meaning t m 4315) (meaning t m 4646) source

theorem rule29950 (p1990 p2027 p2139 p2220 p2553 p2633 p3097 p3365 p3553 p3572 p3660 p3880 : Prop) (h : (¬ p3553) ∨ (¬ p3365) ∨ (¬ p3572) ∨ p2633 ∨ (¬ p1990) ∨ (¬ p2139) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p3097) ∨ (¬ p3880) ∨ (¬ p3660) ∨ (¬ p2553)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p2553) ∨ (p2633) ∨ (¬ p3097) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p3660) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial29950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory19206 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule29950 (meaning t m 1990) (meaning t m 2027) (meaning t m 2139) (meaning t m 2220) (meaning t m 2553) (meaning t m 2633) (meaning t m 3097) (meaning t m 3365) (meaning t m 3553) (meaning t m 3572) (meaning t m 3660) (meaning t m 3880) source

theorem rule29953 (p2027 p2102 p3073 p3471 p3857 p3918 p3985 p4313 p4317 p4782 : Prop) (h : (¬ p4317) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p2102) ∨ (¬ p3857) ∨ (¬ p3918) ∨ (¬ p4782) ∨ (¬ p4313) ∨ (¬ p3073) ∨ (¬ p3985)) : (p2027) ∨ (¬ p2102) ∨ (¬ p3073) ∨ (¬ p3471) ∨ (¬ p3857) ∨ (¬ p3918) ∨ (¬ p3985) ∨ (¬ p4313) ∨ (¬ p4317) ∨ (¬ p4782) := by
  classical
  tauto

theorem initial29953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2102)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4317)) ∨ (¬ (meaning t m 4782)) := by
  have source := ElevenTheory.theory19209 t (m.theta 0 2) (m.theta 0 8) (m.theta 1 6) (m.theta 1 8) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 2 7) (m.theta 8 9)
  exact rule29953 (meaning t m 2027) (meaning t m 2102) (meaning t m 3073) (meaning t m 3471) (meaning t m 3857) (meaning t m 3918) (meaning t m 3985) (meaning t m 4313) (meaning t m 4317) (meaning t m 4782) source

theorem rule29954 (p2027 p2727 p3641 p4360 p4437 p4753 : Prop) (h : (¬ p4437) ∨ (¬ p4360) ∨ p2027 ∨ (¬ p4753) ∨ (¬ p2727) ∨ (¬ p3641)) : (p2027) ∨ (¬ p2727) ∨ (¬ p3641) ∨ (¬ p4360) ∨ (¬ p4437) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial29954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4437)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory19210 t (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule29954 (meaning t m 2027) (meaning t m 2727) (meaning t m 3641) (meaning t m 4360) (meaning t m 4437) (meaning t m 4753) source

theorem rule29955 (p2027 p2220 p2761 p3115 p3366 p3370 p3425 p3497 p4377 p4395 p5228 p5387 : Prop) (h : (¬ p4395) ∨ (¬ p3366) ∨ (¬ p5228) ∨ (¬ p4377) ∨ (¬ p5387) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p3425) ∨ (¬ p2220) ∨ p2027 ∨ (¬ p3370) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2761) ∨ (¬ p3115) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3425) ∨ (¬ p3497) ∨ (¬ p4377) ∨ (¬ p4395) ∨ (¬ p5228) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial29955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 5228)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory19211 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 7) (m.theta 2 9) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29955 (meaning t m 2027) (meaning t m 2220) (meaning t m 2761) (meaning t m 3115) (meaning t m 3366) (meaning t m 3370) (meaning t m 3425) (meaning t m 3497) (meaning t m 4377) (meaning t m 4395) (meaning t m 5228) (meaning t m 5387) source

theorem rule29956 (p2427 p2901 p4241 : Prop) (h : (¬ p4241) ∨ (¬ p2427) ∨ p2901) : (¬ p2427) ∨ (p2901) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial29956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (meaning t m 2901) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory19212 (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule29956 (meaning t m 2427) (meaning t m 2901) (meaning t m 4241) source

theorem rule29958 (p2027 p2210 p2972 p3055 p3680 p3876 p4736 p4831 p5503 : Prop) (h : (¬ p3680) ∨ (¬ p5503) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p4831) ∨ (¬ p3055) ∨ (¬ p2972) ∨ (¬ p3876) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2972) ∨ (¬ p3055) ∨ (¬ p3680) ∨ (¬ p3876) ∨ (¬ p4736) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial29958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory19214 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule29958 (meaning t m 2027) (meaning t m 2210) (meaning t m 2972) (meaning t m 3055) (meaning t m 3680) (meaning t m 3876) (meaning t m 4736) (meaning t m 4831) (meaning t m 5503) source

theorem rule29963 (p1992 p2027 p2132 p2169 p2780 p3583 p3989 p4428 : Prop) (h : (¬ p1992) ∨ p2169 ∨ (¬ p3583) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p4428) ∨ (¬ p2780)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2132) ∨ (p2169) ∨ (¬ p2780) ∨ (¬ p3583) ∨ (¬ p3989) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial29963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory19219 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 8)
  exact rule29963 (meaning t m 1992) (meaning t m 2027) (meaning t m 2132) (meaning t m 2169) (meaning t m 2780) (meaning t m 3583) (meaning t m 3989) (meaning t m 4428) source

theorem rule29967 (p2950 p4849 p4984 : Prop) (h : (¬ p2950) ∨ (¬ p4984) ∨ p4849) : (¬ p2950) ∨ (p4849) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial29967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2950)) ∨ (meaning t m 4849) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory19223 (m.theta 0 3) (m.theta 0 5) (m.theta 0 7)
  exact rule29967 (meaning t m 2950) (meaning t m 4849) (meaning t m 4984) source

theorem rule29971 (p2027 p2352 p2363 p2573 p3583 p3954 p4385 p5059 p5190 : Prop) (h : (¬ p5059) ∨ (¬ p2573) ∨ (¬ p2363) ∨ (¬ p3954) ∨ (¬ p5190) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p4385) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4385) ∨ (¬ p5059) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial29971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5059)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory19227 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule29971 (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 3583) (meaning t m 3954) (meaning t m 4385) (meaning t m 5059) (meaning t m 5190) source

theorem rule29973 (p3246 p3434 p4169 : Prop) (h : (¬ p3434) ∨ (¬ p4169) ∨ p3246) : (p3246) ∨ (¬ p3434) ∨ (¬ p4169) := by
  classical
  tauto

theorem initial29973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3246) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4169)) := by
  have source := ElevenTheory.theory19229 (m.theta 2 7) (m.theta 5 7) (m.theta 7 9)
  exact rule29973 (meaning t m 3246) (meaning t m 3434) (meaning t m 4169) source

theorem rule29974 (p2027 p2499 p2573 p3362 p3365 p4030 p4752 : Prop) (h : (¬ p3362) ∨ (¬ p2499) ∨ (¬ p4030) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p4752) ∨ (¬ p2573)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p3362) ∨ (¬ p3365) ∨ (¬ p4030) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial29974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory19230 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 6)
  exact rule29974 (meaning t m 2027) (meaning t m 2499) (meaning t m 2573) (meaning t m 3362) (meaning t m 3365) (meaning t m 4030) (meaning t m 4752) source

theorem rule29977 (p2027 p2248 p2363 p2437 p2651 p2911 p3860 p4261 p4503 : Prop) (h : (¬ p4503) ∨ (¬ p3860) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p2437) ∨ (¬ p4261) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2363) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial29977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory19233 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 8) (m.theta 3 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29977 (meaning t m 2027) (meaning t m 2248) (meaning t m 2363) (meaning t m 2437) (meaning t m 2651) (meaning t m 2911) (meaning t m 3860) (meaning t m 4261) (meaning t m 4503) source

theorem rule29978 (p3690 p4001 p4278 : Prop) (h : (¬ p3690) ∨ (¬ p4001) ∨ p4278) : (¬ p3690) ∨ (¬ p4001) ∨ (p4278) := by
  classical
  tauto

theorem initial29978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4001)) ∨ (meaning t m 4278) := by
  have source := ElevenTheory.theory19234 (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule29978 (meaning t m 3690) (meaning t m 4001) (meaning t m 4278) source

theorem rule29979 (p2027 p2881 p3609 p3690 p4445 p4807 : Prop) (h : (¬ p4445) ∨ p2027 ∨ (¬ p3609) ∨ (¬ p2881) ∨ (¬ p4807) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3609) ∨ (¬ p3690) ∨ (¬ p4445) ∨ (¬ p4807) := by
  classical
  tauto

theorem initial29979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 4807)) := by
  have source := ElevenTheory.theory19235 t (m.theta 2 8) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule29979 (meaning t m 2027) (meaning t m 2881) (meaning t m 3609) (meaning t m 3690) (meaning t m 4445) (meaning t m 4807) source

theorem rule29980 (p2027 p3063 p3549 p3550 p3570 p4556 : Prop) (h : p2027 ∨ (¬ p3550) ∨ (¬ p3063) ∨ (¬ p3570) ∨ (¬ p3549) ∨ (¬ p4556)) : (p2027) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3550) ∨ (¬ p3570) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial29980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory19236 t (m.theta 1 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule29980 (meaning t m 2027) (meaning t m 3063) (meaning t m 3549) (meaning t m 3550) (meaning t m 3570) (meaning t m 4556) source

theorem rule29981 (p2027 p2088 p2707 p2748 p3365 p3497 p3577 p3662 p4348 p4590 p4734 p4905 : Prop) (h : (¬ p3662) ∨ (¬ p2707) ∨ (¬ p2748) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3577) ∨ (¬ p4905) ∨ (¬ p3497) ∨ (¬ p2088) ∨ (¬ p4734) ∨ (¬ p4348) ∨ (¬ p4590)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2707) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3497) ∨ (¬ p3577) ∨ (¬ p3662) ∨ (¬ p4348) ∨ (¬ p4590) ∨ (¬ p4734) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial29981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory19237 t (m.theta 0 2) (m.theta 0 7) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29981 (meaning t m 2027) (meaning t m 2088) (meaning t m 2707) (meaning t m 2748) (meaning t m 3365) (meaning t m 3497) (meaning t m 3577) (meaning t m 3662) (meaning t m 4348) (meaning t m 4590) (meaning t m 4734) (meaning t m 4905) source

theorem rule29982 (p1995 p2027 p2766 p3379 p3591 p3923 p4347 : Prop) (h : (¬ p1995) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4347) ∨ p2766) : (¬ p1995) ∨ (p2027) ∨ (p2766) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial29982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory19238 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 6 8) (m.theta 8 9)
  exact rule29982 (meaning t m 1995) (meaning t m 2027) (meaning t m 2766) (meaning t m 3379) (meaning t m 3591) (meaning t m 3923) (meaning t m 4347) source

theorem rule29986 (p2027 p2341 p2761 p3773 p4666 p5294 : Prop) (h : (¬ p2341) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p5294) ∨ (¬ p3773)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2761) ∨ (¬ p3773) ∨ (¬ p4666) ∨ (¬ p5294) := by
  classical
  tauto

theorem initial29986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5294)) := by
  have source := ElevenTheory.theory19242 t (m.theta 0 7) (m.theta 0 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule29986 (meaning t m 2027) (meaning t m 2341) (meaning t m 2761) (meaning t m 3773) (meaning t m 4666) (meaning t m 5294) source

theorem rule29989 (p2027 p2589 p2807 p3572 p3692 p3755 p3880 p4117 p4729 p5109 : Prop) (h : (¬ p2807) ∨ (¬ p3572) ∨ (¬ p2589) ∨ (¬ p3692) ∨ (¬ p5109) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p3755)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p3692) ∨ (¬ p3755) ∨ (¬ p3880) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p5109) := by
  classical
  tauto

theorem initial29989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5109)) := by
  have source := ElevenTheory.theory19245 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule29989 (meaning t m 2027) (meaning t m 2589) (meaning t m 2807) (meaning t m 3572) (meaning t m 3692) (meaning t m 3755) (meaning t m 3880) (meaning t m 4117) (meaning t m 4729) (meaning t m 5109) source

theorem rule29990 (p1988 p2027 p2114 p2737 p3115 p3136 p3680 : Prop) (h : (¬ p1988) ∨ (¬ p3136) ∨ (¬ p2737) ∨ (¬ p3115) ∨ (¬ p3680) ∨ p2027 ∨ p2114) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial29990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory19246 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 9 10)
  exact rule29990 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 3115) (meaning t m 3136) (meaning t m 3680) source

theorem rule29991 (p1990 p2027 p2114 p2132 p2284 p2737 p3365 p5051 : Prop) (h : (¬ p3365) ∨ (¬ p2737) ∨ (¬ p2284) ∨ p2114 ∨ p2027 ∨ (¬ p2132) ∨ (¬ p5051) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2132) ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial29991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory19247 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule29991 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2132) (meaning t m 2284) (meaning t m 2737) (meaning t m 3365) (meaning t m 5051) source

theorem rule29992 (p2027 p2579 p2696 p3005 p4009 p4137 p4191 p4729 p5119 : Prop) (h : (¬ p4009) ∨ (¬ p4191) ∨ (¬ p4729) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p5119) ∨ (¬ p4137) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p4009) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4729) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial29992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory19248 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule29992 (meaning t m 2027) (meaning t m 2579) (meaning t m 2696) (meaning t m 3005) (meaning t m 4009) (meaning t m 4137) (meaning t m 4191) (meaning t m 4729) (meaning t m 5119) source

theorem rule29995 (p2027 p2246 p2579 p2744 p2901 p2946 p3246 p3366 p3422 p3905 p4022 p4625 p5160 : Prop) (h : (¬ p2946) ∨ (¬ p4022) ∨ p2027 ∨ (¬ p3905) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p4625) ∨ (¬ p2901) ∨ (¬ p3246) ∨ (¬ p2579) ∨ (¬ p5160) ∨ (¬ p3422)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4022) ∨ (¬ p4625) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial29995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory19251 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 4 9) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule29995 (meaning t m 2027) (meaning t m 2246) (meaning t m 2579) (meaning t m 2744) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3366) (meaning t m 3422) (meaning t m 3905) (meaning t m 4022) (meaning t m 4625) (meaning t m 5160) source

theorem rule29997 (p2001 p2027 p2202 p2528 p3641 p3684 p3692 : Prop) (h : (¬ p2528) ∨ (¬ p2001) ∨ (¬ p3692) ∨ p2202 ∨ (¬ p3684) ∨ (¬ p3641) ∨ p2027) : (¬ p2001) ∨ (p2027) ∨ (p2202) ∨ (¬ p2528) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial29997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory19253 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule29997 (meaning t m 2001) (meaning t m 2027) (meaning t m 2202) (meaning t m 2528) (meaning t m 3641) (meaning t m 3684) (meaning t m 3692) source

theorem rule30002 (p1994 p2027 p2462 p2761 p3574 p4137 p4191 : Prop) (h : p2462 ∨ (¬ p1994) ∨ (¬ p2761) ∨ (¬ p4191) ∨ (¬ p4137) ∨ (¬ p3574) ∨ p2027) : (¬ p1994) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial30002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory19258 t (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule30002 (meaning t m 1994) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 3574) (meaning t m 4137) (meaning t m 4191) source

theorem rule30003 (p2015 p2027 p2307 p2764 p3549 p3946 p4381 p4396 : Prop) (h : p2027 ∨ (¬ p4396) ∨ (¬ p2015) ∨ p2764 ∨ (¬ p4381) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3946)) : (¬ p2015) ∨ (p2027) ∨ (¬ p2307) ∨ (p2764) ∨ (¬ p3549) ∨ (¬ p3946) ∨ (¬ p4381) ∨ (¬ p4396) := by
  classical
  tauto

theorem initial30003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4396)) := by
  have source := ElevenTheory.theory19259 t (m.theta 0 6) (m.theta 1 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule30003 (meaning t m 2015) (meaning t m 2027) (meaning t m 2307) (meaning t m 2764) (meaning t m 3549) (meaning t m 3946) (meaning t m 4381) (meaning t m 4396) source

theorem rule30004 (p2027 p2247 p2588 p2744 p3055 p3063 p3093 p3366 p3584 p4405 : Prop) (h : p2027 ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p2588) ∨ (¬ p4405) ∨ (¬ p3584) ∨ (¬ p3063) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2588) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3584) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial30004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory19260 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30004 (meaning t m 2027) (meaning t m 2247) (meaning t m 2588) (meaning t m 2744) (meaning t m 3055) (meaning t m 3063) (meaning t m 3093) (meaning t m 3366) (meaning t m 3584) (meaning t m 4405) source

theorem rule30013 (p2027 p2156 p2274 p2396 p2509 p2534 p3452 p3950 p4521 : Prop) (h : (¬ p3950) ∨ (¬ p3452) ∨ (¬ p2509) ∨ (¬ p2396) ∨ (¬ p2156) ∨ (¬ p4521) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3452) ∨ (¬ p3950) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial30013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory19269 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule30013 (meaning t m 2027) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 2509) (meaning t m 2534) (meaning t m 3452) (meaning t m 3950) (meaning t m 4521) source

theorem rule30015 (p2187 p3822 p3955 p4185 : Prop) (h : (¬ p4185) ∨ (¬ p2187) ∨ (¬ p3822) ∨ (¬ p3955)) : (¬ p2187) ∨ (¬ p3822) ∨ (¬ p3955) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial30015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory19271 (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30015 (meaning t m 2187) (meaning t m 3822) (meaning t m 3955) (meaning t m 4185) source

theorem rule30018 (p2027 p2579 p2696 p2797 p3905 p4973 : Prop) (h : (¬ p2797) ∨ (¬ p4973) ∨ p2027 ∨ (¬ p3905) ∨ (¬ p2696) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3905) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial30018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory19274 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 6)
  exact rule30018 (meaning t m 2027) (meaning t m 2579) (meaning t m 2696) (meaning t m 2797) (meaning t m 3905) (meaning t m 4973) source

theorem rule30020 (p1982 p2027 p2202 p2373 p3256 p3696 p3998 p5600 : Prop) (h : (¬ p1982) ∨ (¬ p5600) ∨ (¬ p3256) ∨ p2027 ∨ (¬ p3696) ∨ (¬ p3998) ∨ p2202 ∨ (¬ p2373)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2373) ∨ (¬ p3256) ∨ (¬ p3696) ∨ (¬ p3998) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial30020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory19276 t (m.theta 0 8) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule30020 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2373) (meaning t m 3256) (meaning t m 3696) (meaning t m 3998) (meaning t m 5600) source

theorem rule30024 (p1984 p2027 p2098 p2114 p2247 p2780 p2829 p3609 p3662 p4208 p5059 : Prop) (h : (¬ p4208) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p2247) ∨ p2114 ∨ (¬ p2829) ∨ (¬ p5059) ∨ (¬ p2780) ∨ (¬ p3609) ∨ (¬ p2098)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2098) ∨ (p2114) ∨ (¬ p2247) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3609) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial30024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory19280 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 2 8) (m.theta 3 5) (m.theta 5 9) (m.theta 8 9)
  exact rule30024 (meaning t m 1984) (meaning t m 2027) (meaning t m 2098) (meaning t m 2114) (meaning t m 2247) (meaning t m 2780) (meaning t m 2829) (meaning t m 3609) (meaning t m 3662) (meaning t m 4208) (meaning t m 5059) source

theorem rule30026 (p1985 p2027 p2287 p3027 p3516 p3690 p4066 p4154 : Prop) (h : p2287 ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p3690) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (p2287) ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4066) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial30026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory19282 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule30026 (meaning t m 1985) (meaning t m 2027) (meaning t m 2287) (meaning t m 3027) (meaning t m 3516) (meaning t m 3690) (meaning t m 4066) (meaning t m 4154) source

theorem rule30028 (p2027 p2132 p2187 p2245 p2860 p3027 p3414 p4360 p4733 p4774 : Prop) (h : p2027 ∨ (¬ p2245) ∨ (¬ p2132) ∨ (¬ p3414) ∨ (¬ p2860) ∨ (¬ p4774) ∨ (¬ p2187) ∨ (¬ p3027) ∨ (¬ p4733) ∨ (¬ p4360)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2245) ∨ (¬ p2860) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4360) ∨ (¬ p4733) ∨ (¬ p4774) := by
  classical
  tauto

theorem initial30028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4774)) := by
  have source := ElevenTheory.theory19284 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8)
  exact rule30028 (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2245) (meaning t m 2860) (meaning t m 3027) (meaning t m 3414) (meaning t m 4360) (meaning t m 4733) (meaning t m 4774) source

theorem rule30034 (p2027 p2745 p2797 p3567 p3654 p4026 p4245 : Prop) (h : (¬ p2745) ∨ (¬ p4245) ∨ (¬ p3654) ∨ p2027 ∨ (¬ p4026) ∨ (¬ p3567) ∨ (¬ p2797)) : (p2027) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4026) ∨ (¬ p4245) := by
  classical
  tauto

theorem initial30034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4245)) := by
  have source := ElevenTheory.theory19290 t (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9)
  exact rule30034 (meaning t m 2027) (meaning t m 2745) (meaning t m 2797) (meaning t m 3567) (meaning t m 3654) (meaning t m 4026) (meaning t m 4245) source

theorem rule30037 (p1985 p2027 p2192 p2427 p2842 p3371 p3585 p3646 p4031 : Prop) (h : (¬ p3646) ∨ (¬ p1985) ∨ (¬ p2427) ∨ p2842 ∨ p2027 ∨ (¬ p4031) ∨ (¬ p3371) ∨ (¬ p3585) ∨ (¬ p2192)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2427) ∨ (p2842) ∨ (¬ p3371) ∨ (¬ p3585) ∨ (¬ p3646) ∨ (¬ p4031) := by
  classical
  tauto

theorem initial30037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4031)) := by
  have source := ElevenTheory.theory19293 t (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule30037 (meaning t m 1985) (meaning t m 2027) (meaning t m 2192) (meaning t m 2427) (meaning t m 2842) (meaning t m 3371) (meaning t m 3585) (meaning t m 3646) (meaning t m 4031) source

theorem rule30040 (p2027 p2761 p3246 p4277 p4425 p4635 : Prop) (h : (¬ p4277) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p3246) ∨ (¬ p4635) ∨ (¬ p4425)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3246) ∨ (¬ p4277) ∨ (¬ p4425) ∨ (¬ p4635) := by
  classical
  tauto

theorem initial30040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4635)) := by
  have source := ElevenTheory.theory19296 t (m.theta 4 7) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule30040 (meaning t m 2027) (meaning t m 2761) (meaning t m 3246) (meaning t m 4277) (meaning t m 4425) (meaning t m 4635) source

theorem rule30043 (p2891 p3412 p4320 : Prop) (h : (¬ p2891) ∨ (¬ p3412) ∨ (¬ p4320)) : (¬ p2891) ∨ (¬ p3412) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial30043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory19299 (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule30043 (meaning t m 2891) (meaning t m 3412) (meaning t m 4320) source

theorem rule30044 (p1998 p2027 p2177 p2386 p2545 p2553 p2797 p2810 p3567 : Prop) (h : (¬ p2177) ∨ p2545 ∨ (¬ p2810) ∨ (¬ p2386) ∨ (¬ p1998) ∨ (¬ p3567) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p2797)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2386) ∨ (p2545) ∨ (¬ p2553) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3567) := by
  classical
  tauto

theorem initial30044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2386)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3567)) := by
  have source := ElevenTheory.theory19300 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule30044 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2386) (meaning t m 2545) (meaning t m 2553) (meaning t m 2797) (meaning t m 2810) (meaning t m 3567) source

theorem rule30045 (p2027 p2510 p2528 p2891 p3096 p4261 p4492 p4558 : Prop) (h : (¬ p2891) ∨ (¬ p3096) ∨ (¬ p2510) ∨ (¬ p4492) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2891) ∨ (¬ p3096) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial30045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory19301 t (m.theta 1 5) (m.theta 1 8) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 5 7) (m.theta 8 9)
  exact rule30045 (meaning t m 2027) (meaning t m 2510) (meaning t m 2528) (meaning t m 2891) (meaning t m 3096) (meaning t m 4261) (meaning t m 4492) (meaning t m 4558) source

theorem rule30052 (p2027 p2241 p3055 p3189 p3256 p3584 p4137 p4604 p4736 : Prop) (h : (¬ p3189) ∨ (¬ p4137) ∨ (¬ p3584) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p4604) ∨ (¬ p2241) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3055) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial30052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory19308 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9)
  exact rule30052 (meaning t m 2027) (meaning t m 2241) (meaning t m 3055) (meaning t m 3189) (meaning t m 3256) (meaning t m 3584) (meaning t m 4137) (meaning t m 4604) (meaning t m 4736) source

theorem rule30059 (p1976 p2027 p2462 p3365 p3690 p4315 p4320 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p3365) ∨ (¬ p4320) ∨ p2462 ∨ (¬ p3690)) : (¬ p1976) ∨ (p2027) ∨ (p2462) ∨ (¬ p3365) ∨ (¬ p3690) ∨ (¬ p4315) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial30059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory19315 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9)
  exact rule30059 (meaning t m 1976) (meaning t m 2027) (meaning t m 2462) (meaning t m 3365) (meaning t m 3690) (meaning t m 4315) (meaning t m 4320) source

theorem rule30061 (p2005 p2027 p2307 p2387 p2588 p2766 p4347 : Prop) (h : (¬ p2588) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p2005) ∨ (¬ p2307) ∨ (¬ p4347) ∨ p2766) : (¬ p2005) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (p2766) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial30061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory19317 t (m.theta 0 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule30061 (meaning t m 2005) (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2588) (meaning t m 2766) (meaning t m 4347) source

theorem rule30062 (p2139 p2958 p4786 : Prop) (h : (¬ p2958) ∨ (¬ p4786) ∨ p2139) : (p2139) ∨ (¬ p2958) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial30062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2139) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory19318 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5)
  exact rule30062 (meaning t m 2139) (meaning t m 2958) (meaning t m 4786) source

theorem rule30067 (p1987 p2027 p2417 p2699 p2922 p2946 p3379 p3414 p3553 p4315 p4668 : Prop) (h : (¬ p2417) ∨ p2699 ∨ p2027 ∨ (¬ p4668) ∨ (¬ p3379) ∨ (¬ p1987) ∨ (¬ p4315) ∨ (¬ p3553) ∨ (¬ p2946) ∨ (¬ p2922) ∨ (¬ p3414)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2417) ∨ (p2699) ∨ (¬ p2922) ∨ (¬ p2946) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4315) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial30067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory19323 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule30067 (meaning t m 1987) (meaning t m 2027) (meaning t m 2417) (meaning t m 2699) (meaning t m 2922) (meaning t m 2946) (meaning t m 3379) (meaning t m 3414) (meaning t m 3553) (meaning t m 4315) (meaning t m 4668) source

theorem rule30071 (p2023 p2166 p2873 p4494 : Prop) (h : (¬ p2166) ∨ p2873 ∨ (¬ p2023) ∨ p4494) : (¬ p2023) ∨ (¬ p2166) ∨ (p2873) ∨ (p4494) := by
  classical
  tauto

theorem initial30071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2023)) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2873) ∨ (meaning t m 4494) := by
  have source := ElevenTheory.theory19327 t (m.theta 1 5) (m.theta 1 8) (m.theta 5 8)
  exact rule30071 (meaning t m 2023) (meaning t m 2166) (meaning t m 2873) (meaning t m 4494) source

theorem rule30073 (p1995 p2027 p2997 p3097 p3238 p3737 p4031 p4094 p4198 : Prop) (h : (¬ p3238) ∨ (¬ p1995) ∨ (¬ p4198) ∨ (¬ p4031) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p3737) ∨ p2997 ∨ (¬ p4094)) : (¬ p1995) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3238) ∨ (¬ p3737) ∨ (¬ p4031) ∨ (¬ p4094) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial30073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4094)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory19329 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 10) (m.theta 6 7)
  exact rule30073 (meaning t m 1995) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3238) (meaning t m 3737) (meaning t m 4031) (meaning t m 4094) (meaning t m 4198) source

theorem rule30083 (p1998 p2027 p2363 p2699 p3093 p3309 p3325 p4348 : Prop) (h : p2027 ∨ (¬ p3093) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p4348) ∨ p2699 ∨ (¬ p3309) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2363) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3325) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial30083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory19339 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule30083 (meaning t m 1998) (meaning t m 2027) (meaning t m 2363) (meaning t m 2699) (meaning t m 3093) (meaning t m 3309) (meaning t m 3325) (meaning t m 4348) source

theorem rule30091 (p2027 p2166 p2255 p2313 p2667 p2946 p3146 p3412 p4107 p4154 p4669 : Prop) (h : (¬ p2255) ∨ (¬ p3412) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p4154) ∨ (¬ p2667) ∨ (¬ p2313) ∨ (¬ p2166) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p4107)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2255) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3412) ∨ (¬ p4107) ∨ (¬ p4154) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial30091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory19347 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule30091 (meaning t m 2027) (meaning t m 2166) (meaning t m 2255) (meaning t m 2313) (meaning t m 2667) (meaning t m 2946) (meaning t m 3146) (meaning t m 3412) (meaning t m 4107) (meaning t m 4154) (meaning t m 4669) source

theorem rule30094 (p1988 p2027 p2363 p2383 p2641 p2688 p3266 p3567 : Prop) (h : (¬ p2363) ∨ (¬ p3567) ∨ p2688 ∨ p2027 ∨ (¬ p2641) ∨ (¬ p1988) ∨ (¬ p2383) ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p3266) ∨ (¬ p3567) := by
  classical
  tauto

theorem initial30094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3567)) := by
  have source := ElevenTheory.theory19350 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule30094 (meaning t m 1988) (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 2641) (meaning t m 2688) (meaning t m 3266) (meaning t m 3567) source

theorem rule30096 (p2027 p2264 p2685 p2696 p3238 p3452 p3880 p4733 p4905 : Prop) (h : (¬ p3880) ∨ (¬ p2685) ∨ (¬ p4905) ∨ (¬ p4733) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4733) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial30096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory19352 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8)
  exact rule30096 (meaning t m 2027) (meaning t m 2264) (meaning t m 2685) (meaning t m 2696) (meaning t m 3238) (meaning t m 3452) (meaning t m 3880) (meaning t m 4733) (meaning t m 4905) source

theorem rule30098 (p1986 p2027 p2352 p2598 p2780 p3008 p4358 : Prop) (h : (¬ p1986) ∨ (¬ p2780) ∨ (¬ p2352) ∨ (¬ p2598) ∨ p3008 ∨ p2027 ∨ (¬ p4358)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (p3008) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial30098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory19354 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 8)
  exact rule30098 (meaning t m 1986) (meaning t m 2027) (meaning t m 2352) (meaning t m 2598) (meaning t m 2780) (meaning t m 3008) (meaning t m 4358) source

theorem rule30100 (p2264 p2881 p3699 : Prop) (h : (¬ p2264) ∨ (¬ p3699) ∨ p2881) : (¬ p2264) ∨ (p2881) ∨ (¬ p3699) := by
  classical
  tauto

theorem initial30100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (meaning t m 2881) ∨ (¬ (meaning t m 3699)) := by
  have source := ElevenTheory.theory19356 (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule30100 (meaning t m 2264) (meaning t m 2881) (meaning t m 3699) source

theorem rule30101 (p2696 p2753 p3583 p4313 : Prop) (h : (¬ p3583) ∨ (¬ p4313) ∨ (¬ p2753) ∨ (¬ p2696)) : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3583) ∨ (¬ p4313) := by
  classical
  tauto

theorem initial30101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4313)) := by
  have source := ElevenTheory.theory19357 (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5)
  exact rule30101 (meaning t m 2696) (meaning t m 2753) (meaning t m 3583) (meaning t m 4313) source

theorem rule30104 (p1994 p2027 p2622 p2651 p2707 p2743 p3414 p4325 : Prop) (h : (¬ p2651) ∨ (¬ p1994) ∨ p2622 ∨ (¬ p3414) ∨ p2027 ∨ (¬ p4325) ∨ (¬ p2707) ∨ (¬ p2743)) : (¬ p1994) ∨ (p2027) ∨ (p2622) ∨ (¬ p2651) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3414) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial30104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory19360 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7)
  exact rule30104 (meaning t m 1994) (meaning t m 2027) (meaning t m 2622) (meaning t m 2651) (meaning t m 2707) (meaning t m 2743) (meaning t m 3414) (meaning t m 4325) source

theorem rule30109 (p1975 p2027 p2114 p2295 p2737 p2774 p3365 p4328 : Prop) (h : (¬ p4328) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p2737) ∨ p2114 ∨ (¬ p1975) ∨ (¬ p2295)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2295) ∨ (¬ p2737) ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial30109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory19365 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule30109 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2295) (meaning t m 2737) (meaning t m 2774) (meaning t m 3365) (meaning t m 4328) source

theorem rule30110 (p1986 p2027 p2169 p3584 p3737 p3989 p5514 : Prop) (h : (¬ p3737) ∨ p2169 ∨ (¬ p3989) ∨ p2027 ∨ (¬ p1986) ∨ (¬ p3584) ∨ (¬ p5514)) : (¬ p1986) ∨ (p2027) ∨ (p2169) ∨ (¬ p3584) ∨ (¬ p3737) ∨ (¬ p3989) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial30110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory19366 t (m.theta 2 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 10) (m.theta 6 8)
  exact rule30110 (meaning t m 1986) (meaning t m 2027) (meaning t m 2169) (meaning t m 3584) (meaning t m 3737) (meaning t m 3989) (meaning t m 5514) source

theorem rule30115 (p1975 p2027 p2295 p2331 p2657 p2688 p2727 : Prop) (h : (¬ p2295) ∨ (¬ p2657) ∨ p2688 ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2727) ∨ (¬ p2331)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) := by
  classical
  tauto

theorem initial30115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) := by
  have source := ElevenTheory.theory19371 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule30115 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) source

theorem rule30118 (p2373 p3156 p4241 : Prop) (h : (¬ p2373) ∨ (¬ p4241) ∨ p3156) : (¬ p2373) ∨ (p3156) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial30118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2373)) ∨ (meaning t m 3156) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory19374 (m.theta 3 5) (m.theta 4 5) (m.theta 5 8)
  exact rule30118 (meaning t m 2373) (meaning t m 3156) (meaning t m 4241) source

theorem rule30127 (p2027 p2264 p2528 p2737 p2807 p2811 p3055 p3453 p4030 p4261 p4438 p4734 : Prop) (h : (¬ p4438) ∨ (¬ p4261) ∨ (¬ p2811) ∨ (¬ p4734) ∨ (¬ p2528) ∨ (¬ p3453) ∨ (¬ p4030) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p3055) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2528) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3055) ∨ (¬ p3453) ∨ (¬ p4030) ∨ (¬ p4261) ∨ (¬ p4438) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial30127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3453)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory19383 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule30127 (meaning t m 2027) (meaning t m 2264) (meaning t m 2528) (meaning t m 2737) (meaning t m 2807) (meaning t m 2811) (meaning t m 3055) (meaning t m 3453) (meaning t m 4030) (meaning t m 4261) (meaning t m 4438) (meaning t m 4734) source

theorem rule30128 (p1982 p2027 p2114 p2177 p2307 p2459 p2779 p2829 : Prop) (h : (¬ p2307) ∨ p2027 ∨ (¬ p2779) ∨ (¬ p2459) ∨ p2114 ∨ (¬ p1982) ∨ (¬ p2177) ∨ (¬ p2829)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p2779) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial30128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory19384 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule30128 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2177) (meaning t m 2307) (meaning t m 2459) (meaning t m 2779) (meaning t m 2829) source

theorem rule30132 (p2417 p2449 p3740 : Prop) (h : (¬ p3740) ∨ (¬ p2449) ∨ p2417) : (p2417) ∨ (¬ p2449) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial30132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2417) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory19388 (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule30132 (meaning t m 2417) (meaning t m 2449) (meaning t m 3740) source

theorem rule30133 (p2470 p3355 p4045 : Prop) (h : (¬ p4045) ∨ (¬ p3355) ∨ p2470) : (p2470) ∨ (¬ p3355) ∨ (¬ p4045) := by
  classical
  tauto

theorem initial30133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2470) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 4045)) := by
  have source := ElevenTheory.theory19389 (m.theta 0 4) (m.theta 4 8) (m.theta 4 9)
  exact rule30133 (meaning t m 2470) (meaning t m 3355) (meaning t m 4045) source

theorem rule30136 (p2027 p2531 p3641 p3684 p5433 p5569 : Prop) (h : (¬ p2531) ∨ p2027 ∨ (¬ p5569) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p5433)) : (p2027) ∨ (¬ p2531) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p5433) ∨ (¬ p5569) := by
  classical
  tauto

theorem initial30136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 5433)) ∨ (¬ (meaning t m 5569)) := by
  have source := ElevenTheory.theory19392 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 10) (m.theta 5 8)
  exact rule30136 (meaning t m 2027) (meaning t m 2531) (meaning t m 3641) (meaning t m 3684) (meaning t m 5433) (meaning t m 5569) source

theorem rule30138 (p2027 p2751 p3073 p3177 p3857 p3859 p3877 : Prop) (h : (¬ p3177) ∨ p2027 ∨ (¬ p3859) ∨ (¬ p3877) ∨ (¬ p3857) ∨ (¬ p2751) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2751) ∨ (¬ p3073) ∨ (¬ p3177) ∨ (¬ p3857) ∨ (¬ p3859) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial30138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory19394 t (m.theta 0 8) (m.theta 1 3) (m.theta 1 8) (m.theta 2 3) (m.theta 3 8) (m.theta 8 9)
  exact rule30138 (meaning t m 2027) (meaning t m 2751) (meaning t m 3073) (meaning t m 3177) (meaning t m 3857) (meaning t m 3859) (meaning t m 3877) source

theorem rule30143 (p2748 p3136 p3662 : Prop) (h : (¬ p3662) ∨ (¬ p2748) ∨ (¬ p3136)) : (¬ p2748) ∨ (¬ p3136) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial30143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory19399 (m.theta 1 3) (m.theta 2 3) (m.theta 3 5)
  exact rule30143 (meaning t m 2748) (meaning t m 3136) (meaning t m 3662) source

theorem rule30146 (p2027 p3038 p3093 p3631 p3821 p4760 p5206 : Prop) (h : (¬ p3093) ∨ (¬ p4760) ∨ (¬ p3821) ∨ (¬ p3631) ∨ (¬ p5206) ∨ (¬ p3038) ∨ p2027) : (p2027) ∨ (¬ p3038) ∨ (¬ p3093) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4760) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial30146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4760)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory19402 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 3) (m.theta 1 6) (m.theta 1 7) (m.theta 7 9)
  exact rule30146 (meaning t m 2027) (meaning t m 3038) (meaning t m 3093) (meaning t m 3631) (meaning t m 3821) (meaning t m 4760) (meaning t m 5206) source

theorem rule30150 (p1998 p2027 p2396 p2997 p3690 p3747 p3969 p5558 : Prop) (h : p2027 ∨ (¬ p3690) ∨ (¬ p3969) ∨ (¬ p2396) ∨ (¬ p3747) ∨ (¬ p1998) ∨ p2997 ∨ (¬ p5558)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3690) ∨ (¬ p3747) ∨ (¬ p3969) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial30150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory19406 t (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule30150 (meaning t m 1998) (meaning t m 2027) (meaning t m 2396) (meaning t m 2997) (meaning t m 3690) (meaning t m 3747) (meaning t m 3969) (meaning t m 5558) source

theorem rule30152 (p4288 p5600 p5693 : Prop) (h : (¬ p5693) ∨ (¬ p4288) ∨ p5600) : (¬ p4288) ∨ (p5600) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial30152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4288)) ∨ (meaning t m 5600) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory19408 (m.theta 1 8) (m.theta 3 8) (m.theta 8 10)
  exact rule30152 (meaning t m 4288) (meaning t m 5600) (meaning t m 5693) source

theorem rule30153 (p2027 p2387 p2406 p2598 p2785 p2982 p3590 p3688 p4347 p4450 p4737 : Prop) (h : (¬ p3688) ∨ (¬ p4450) ∨ (¬ p2785) ∨ (¬ p4737) ∨ (¬ p3590) ∨ (¬ p2598) ∨ (¬ p2406) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p2982) ∨ (¬ p2387)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2406) ∨ (¬ p2598) ∨ (¬ p2785) ∨ (¬ p2982) ∨ (¬ p3590) ∨ (¬ p3688) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial30153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory19409 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule30153 (meaning t m 2027) (meaning t m 2387) (meaning t m 2406) (meaning t m 2598) (meaning t m 2785) (meaning t m 2982) (meaning t m 3590) (meaning t m 3688) (meaning t m 4347) (meaning t m 4450) (meaning t m 4737) source

theorem rule30161 (p2027 p2241 p2449 p2534 p3027 p3055 p3874 p3950 p4736 : Prop) (h : (¬ p3027) ∨ (¬ p4736) ∨ (¬ p2241) ∨ (¬ p2534) ∨ (¬ p3950) ∨ (¬ p3874) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2534) ∨ (¬ p3027) ∨ (¬ p3055) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial30161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory19417 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule30161 (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 2534) (meaning t m 3027) (meaning t m 3055) (meaning t m 3874) (meaning t m 3950) (meaning t m 4736) source

theorem rule30172 (p1986 p2027 p2462 p2761 p3366 p3367 p3425 p4425 p5159 p5228 : Prop) (h : (¬ p1986) ∨ (¬ p3425) ∨ (¬ p5228) ∨ (¬ p3367) ∨ (¬ p5159) ∨ p2462 ∨ (¬ p2761) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p3366)) : (¬ p1986) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p3425) ∨ (¬ p4425) ∨ (¬ p5159) ∨ (¬ p5228) := by
  classical
  tauto

theorem initial30172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5159)) ∨ (¬ (meaning t m 5228)) := by
  have source := ElevenTheory.theory19428 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 2 9) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule30172 (meaning t m 1986) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 3366) (meaning t m 3367) (meaning t m 3425) (meaning t m 4425) (meaning t m 5159) (meaning t m 5228) source

theorem rule30173 (p2103 p3439 p4353 : Prop) (h : (¬ p3439) ∨ (¬ p4353) ∨ p2103) : (p2103) ∨ (¬ p3439) ∨ (¬ p4353) := by
  classical
  tauto

theorem initial30173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2103) ∨ (¬ (meaning t m 3439)) ∨ (¬ (meaning t m 4353)) := by
  have source := ElevenTheory.theory19429 (m.theta 0 8) (m.theta 1 8) (m.theta 2 8)
  exact rule30173 (meaning t m 2103) (meaning t m 3439) (meaning t m 4353) source

theorem rule30174 (p2027 p2563 p2881 p3551 p3872 p4533 p4984 : Prop) (h : p2027 ∨ (¬ p2563) ∨ (¬ p4533) ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p4984) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p3872) ∨ (¬ p4533) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial30174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4533)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory19430 t (m.theta 0 5) (m.theta 0 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule30174 (meaning t m 2027) (meaning t m 2563) (meaning t m 2881) (meaning t m 3551) (meaning t m 3872) (meaning t m 4533) (meaning t m 4984) source

theorem rule30176 (p3309 p3319 p4187 : Prop) (h : (¬ p3309) ∨ (¬ p4187) ∨ p3319) : (¬ p3309) ∨ (p3319) ∨ (¬ p4187) := by
  classical
  tauto

theorem initial30176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3309)) ∨ (meaning t m 3319) ∨ (¬ (meaning t m 4187)) := by
  have source := ElevenTheory.theory19432 (m.theta 1 6) (m.theta 6 7) (m.theta 6 9)
  exact rule30176 (meaning t m 3309) (meaning t m 3319) (meaning t m 4187) source

theorem rule30179 (p2027 p2476 p3083 p3093 p3097 p3309 p3574 p4718 p5193 : Prop) (h : (¬ p5193) ∨ (¬ p3093) ∨ (¬ p3574) ∨ (¬ p2476) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3083) ∨ p2027 ∨ (¬ p4718)) : (p2027) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p4718) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial30179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4718)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory19435 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7)
  exact rule30179 (meaning t m 2027) (meaning t m 2476) (meaning t m 3083) (meaning t m 3093) (meaning t m 3097) (meaning t m 3309) (meaning t m 3574) (meaning t m 4718) (meaning t m 5193) source

theorem rule30180 (p2027 p3093 p3319 p3365 p3461 p3877 p4736 p5123 p5600 : Prop) (h : (¬ p3877) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p5600) ∨ (¬ p4736) ∨ (¬ p3461) ∨ (¬ p5123) ∨ (¬ p3319) ∨ (¬ p3093)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3365) ∨ (¬ p3461) ∨ (¬ p3877) ∨ (¬ p4736) ∨ (¬ p5123) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial30180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory19436 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule30180 (meaning t m 2027) (meaning t m 3093) (meaning t m 3319) (meaning t m 3365) (meaning t m 3461) (meaning t m 3877) (meaning t m 4736) (meaning t m 5123) (meaning t m 5600) source

theorem rule30182 (p2427 p2901 p3879 : Prop) (h : (¬ p2901) ∨ (¬ p3879) ∨ p2427) : (p2427) ∨ (¬ p2901) ∨ (¬ p3879) := by
  classical
  tauto

theorem initial30182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2427) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3879)) := by
  have source := ElevenTheory.theory19438 (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule30182 (meaning t m 2427) (meaning t m 2901) (meaning t m 3879) source

theorem rule30184 (p2027 p2132 p2254 p2588 p2657 p2707 p3574 p3583 p3589 p4473 : Prop) (h : (¬ p2657) ∨ (¬ p4473) ∨ (¬ p2132) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p3589) ∨ (¬ p3583) ∨ (¬ p3574) ∨ (¬ p2588) ∨ (¬ p2707)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2254) ∨ (¬ p2588) ∨ (¬ p2657) ∨ (¬ p2707) ∨ (¬ p3574) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4473) := by
  classical
  tauto

theorem initial30184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4473)) := by
  have source := ElevenTheory.theory19440 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule30184 (meaning t m 2027) (meaning t m 2132) (meaning t m 2254) (meaning t m 2588) (meaning t m 2657) (meaning t m 2707) (meaning t m 3574) (meaning t m 3583) (meaning t m 3589) (meaning t m 4473) source

theorem rule30186 (p1982 p2027 p2177 p2274 p2284 p2388 p2459 : Prop) (h : (¬ p1982) ∨ (¬ p2274) ∨ p2027 ∨ p2388 ∨ (¬ p2177) ∨ (¬ p2284) ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p2459) := by
  classical
  tauto

theorem initial30186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2459)) := by
  have source := ElevenTheory.theory19442 t (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule30186 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 2284) (meaning t m 2388) (meaning t m 2459) source

theorem rule30187 (p1984 p2027 p2169 p2274 p2780 p3822 p3873 p3989 : Prop) (h : p2169 ∨ (¬ p3989) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p2780) ∨ (¬ p2274) ∨ (¬ p3873) ∨ (¬ p3822)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p3873) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial30187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory19443 t (m.theta 0 1) (m.theta 0 2) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30187 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 2274) (meaning t m 2780) (meaning t m 3822) (meaning t m 3873) (meaning t m 3989) source

theorem rule30189 (p2027 p2247 p2274 p2383 p2962 p3742 p3989 p4111 p4521 p4712 : Prop) (h : p2027 ∨ (¬ p2247) ∨ (¬ p3989) ∨ (¬ p4111) ∨ (¬ p4521) ∨ (¬ p2274) ∨ (¬ p2383) ∨ (¬ p3742) ∨ (¬ p2962) ∨ (¬ p4712)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2274) ∨ (¬ p2383) ∨ (¬ p2962) ∨ (¬ p3742) ∨ (¬ p3989) ∨ (¬ p4111) ∨ (¬ p4521) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial30189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory19445 t (m.theta 0 1) (m.theta 0 5) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30189 (meaning t m 2027) (meaning t m 2247) (meaning t m 2274) (meaning t m 2383) (meaning t m 2962) (meaning t m 3742) (meaning t m 3989) (meaning t m 4111) (meaning t m 4521) (meaning t m 4712) source

theorem rule30191 (p2027 p2608 p3367 p3591 p3918 p5221 : Prop) (h : (¬ p5221) ∨ (¬ p3367) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3918) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3367) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p5221) := by
  classical
  tauto

theorem initial30191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 5221)) := by
  have source := ElevenTheory.theory19447 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6)
  exact rule30191 (meaning t m 2027) (meaning t m 2608) (meaning t m 3367) (meaning t m 3591) (meaning t m 3918) (meaning t m 5221) source

theorem rule30192 (p2104 p3166 p4117 p4963 : Prop) (h : (¬ p3166) ∨ (¬ p4963) ∨ (¬ p4117) ∨ (¬ p2104)) : (¬ p2104) ∨ (¬ p3166) ∨ (¬ p4117) ∨ (¬ p4963) := by
  classical
  tauto

theorem initial30192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4963)) := by
  have source := ElevenTheory.theory19448 (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 3 8)
  exact rule30192 (meaning t m 2104) (meaning t m 3166) (meaning t m 4117) (meaning t m 4963) source

theorem rule30193 (p1987 p2027 p2764 p3556 p3645 p3690 p4282 p4315 p4381 : Prop) (h : (¬ p4282) ∨ p2027 ∨ p2764 ∨ (¬ p3645) ∨ (¬ p4381) ∨ (¬ p4315) ∨ (¬ p3556) ∨ (¬ p1987) ∨ (¬ p3690)) : (¬ p1987) ∨ (p2027) ∨ (p2764) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3690) ∨ (¬ p4282) ∨ (¬ p4315) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial30193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory19449 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule30193 (meaning t m 1987) (meaning t m 2027) (meaning t m 2764) (meaning t m 3556) (meaning t m 3645) (meaning t m 3690) (meaning t m 4282) (meaning t m 4315) (meaning t m 4381) source

theorem rule30199 (p2027 p2177 p2230 p2427 p3367 p3425 p3548 p3576 p3759 p4556 p4734 : Prop) (h : (¬ p3759) ∨ (¬ p2177) ∨ (¬ p3548) ∨ (¬ p4556) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3367) ∨ (¬ p3576) ∨ (¬ p2427) ∨ (¬ p4734)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3367) ∨ (¬ p3425) ∨ (¬ p3548) ∨ (¬ p3576) ∨ (¬ p3759) ∨ (¬ p4556) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial30199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory19455 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule30199 (meaning t m 2027) (meaning t m 2177) (meaning t m 2230) (meaning t m 2427) (meaning t m 3367) (meaning t m 3425) (meaning t m 3548) (meaning t m 3576) (meaning t m 3759) (meaning t m 4556) (meaning t m 4734) source

theorem rule30200 (p2027 p2138 p2264 p2737 p2807 p2811 p3690 p4244 p4666 p4734 : Prop) (h : (¬ p2811) ∨ (¬ p2807) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2737) ∨ (¬ p4244) ∨ (¬ p3690) ∨ (¬ p2264) ∨ (¬ p4666)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2264) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4666) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial30200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory19456 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule30200 (meaning t m 2027) (meaning t m 2138) (meaning t m 2264) (meaning t m 2737) (meaning t m 2807) (meaning t m 2811) (meaning t m 3690) (meaning t m 4244) (meaning t m 4666) (meaning t m 4734) source

theorem rule30217 (p1984 p2027 p2191 p2765 p3156 p3555 p3952 : Prop) (h : p2027 ∨ (¬ p3156) ∨ p2765 ∨ (¬ p3952) ∨ (¬ p1984) ∨ (¬ p3555) ∨ (¬ p2191)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2191) ∨ (p2765) ∨ (¬ p3156) ∨ (¬ p3555) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial30217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory19473 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule30217 (meaning t m 1984) (meaning t m 2027) (meaning t m 2191) (meaning t m 2765) (meaning t m 3156) (meaning t m 3555) (meaning t m 3952) source

theorem rule30218 (p2027 p3389 p3555 p3876 p4166 p4322 p4363 p5129 p5190 : Prop) (h : (¬ p5129) ∨ (¬ p5190) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4363) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p4322) ∨ (¬ p4166)) : (p2027) ∨ (¬ p3389) ∨ (¬ p3555) ∨ (¬ p3876) ∨ (¬ p4166) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p5129) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial30218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4166)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 5129)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory19474 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 10) (m.theta 4 7) (m.theta 5 9) (m.theta 9 10)
  exact rule30218 (meaning t m 2027) (meaning t m 3389) (meaning t m 3555) (meaning t m 3876) (meaning t m 4166) (meaning t m 4322) (meaning t m 4363) (meaning t m 5129) (meaning t m 5190) source

theorem rule30221 (p2027 p2104 p2230 p2696 p2982 p3680 p3759 p4749 p5123 p5612 : Prop) (h : (¬ p2696) ∨ (¬ p5612) ∨ (¬ p2104) ∨ (¬ p5123) ∨ (¬ p2230) ∨ (¬ p3680) ∨ (¬ p4749) ∨ (¬ p3759) ∨ p2027 ∨ (¬ p2982)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2230) ∨ (¬ p2696) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p3759) ∨ (¬ p4749) ∨ (¬ p5123) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial30221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory19477 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 4 5) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule30221 (meaning t m 2027) (meaning t m 2104) (meaning t m 2230) (meaning t m 2696) (meaning t m 2982) (meaning t m 3680) (meaning t m 3759) (meaning t m 4749) (meaning t m 5123) (meaning t m 5612) source

theorem rule30223 (p2027 p2331 p2753 p2761 p3346 p3347 p3755 p4117 p4195 p4425 p4658 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p3347) ∨ (¬ p2761) ∨ (¬ p3346) ∨ (¬ p4425) ∨ (¬ p3755) ∨ (¬ p4195) ∨ (¬ p4658) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4117) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3346) ∨ (¬ p3347) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4425) ∨ (¬ p4658) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial30223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4658)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory19479 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule30223 (meaning t m 2027) (meaning t m 2331) (meaning t m 2753) (meaning t m 2761) (meaning t m 3346) (meaning t m 3347) (meaning t m 3755) (meaning t m 4117) (meaning t m 4195) (meaning t m 4425) (meaning t m 4658) (meaning t m 5216) source

theorem rule30224 (p2027 p2313 p2553 p2753 p3204 p3619 p3670 p4137 p4444 p4604 p4870 : Prop) (h : (¬ p3670) ∨ (¬ p4137) ∨ (¬ p2753) ∨ (¬ p4604) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p3204) ∨ (¬ p4870) ∨ (¬ p2553) ∨ (¬ p3619)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2753) ∨ (¬ p3204) ∨ (¬ p3619) ∨ (¬ p3670) ∨ (¬ p4137) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial30224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory19480 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 9) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30224 (meaning t m 2027) (meaning t m 2313) (meaning t m 2553) (meaning t m 2753) (meaning t m 3204) (meaning t m 3619) (meaning t m 3670) (meaning t m 4137) (meaning t m 4444) (meaning t m 4604) (meaning t m 4870) source

theorem rule30226 (p3880 p4119 p4235 : Prop) (h : (¬ p4119) ∨ (¬ p4235) ∨ p3880) : (p3880) ∨ (¬ p4119) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial30226 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3880) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory19482 (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule30226 (meaning t m 3880) (meaning t m 4119) (meaning t m 4235) source

theorem rule30227 (p1982 p2027 p2352 p3008 p3256 p3998 p4170 p5600 : Prop) (h : (¬ p1982) ∨ (¬ p4170) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p5600) ∨ (¬ p2352) ∨ p3008 ∨ (¬ p3998)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2352) ∨ (p3008) ∨ (¬ p3256) ∨ (¬ p3998) ∨ (¬ p4170) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial30227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory19483 t (m.theta 0 8) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule30227 (meaning t m 1982) (meaning t m 2027) (meaning t m 2352) (meaning t m 3008) (meaning t m 3256) (meaning t m 3998) (meaning t m 4170) (meaning t m 5600) source

theorem rule30228 (p2027 p2881 p3286 p3551 p3670 p4107 p4117 p4275 p4425 p4638 p5260 p5454 : Prop) (h : (¬ p5454) ∨ (¬ p3286) ∨ (¬ p4275) ∨ (¬ p5260) ∨ (¬ p4107) ∨ (¬ p3670) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p2881) ∨ (¬ p4638) ∨ (¬ p4425)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3286) ∨ (¬ p3551) ∨ (¬ p3670) ∨ (¬ p4107) ∨ (¬ p4117) ∨ (¬ p4275) ∨ (¬ p4425) ∨ (¬ p4638) ∨ (¬ p5260) ∨ (¬ p5454) := by
  classical
  tauto

theorem initial30228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 5260)) ∨ (¬ (meaning t m 5454)) := by
  have source := ElevenTheory.theory19484 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 2 9) (m.theta 3 9) (m.theta 4 9) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule30228 (meaning t m 2027) (meaning t m 2881) (meaning t m 3286) (meaning t m 3551) (meaning t m 3670) (meaning t m 4107) (meaning t m 4117) (meaning t m 4275) (meaning t m 4425) (meaning t m 4638) (meaning t m 5260) (meaning t m 5454) source

theorem rule30230 (p1997 p2027 p2509 p2850 p3222 p3498 p5160 : Prop) (h : (¬ p1997) ∨ (¬ p5160) ∨ (¬ p2850) ∨ p2027 ∨ p3498 ∨ (¬ p3222) ∨ (¬ p2509)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2509) ∨ (¬ p2850) ∨ (¬ p3222) ∨ (p3498) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial30230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3222)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory19486 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 4 9)
  exact rule30230 (meaning t m 1997) (meaning t m 2027) (meaning t m 2509) (meaning t m 2850) (meaning t m 3222) (meaning t m 3498) (meaning t m 5160) source

theorem rule30233 (p2027 p3055 p3093 p3319 p3461 p3874 p4286 p4736 p5123 : Prop) (h : (¬ p3874) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p3055) ∨ (¬ p4736) ∨ (¬ p3461) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p4286)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p4736) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial30233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory19489 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule30233 (meaning t m 2027) (meaning t m 3055) (meaning t m 3093) (meaning t m 3319) (meaning t m 3461) (meaning t m 3874) (meaning t m 4286) (meaning t m 4736) (meaning t m 5123) source

theorem rule30243 (p2027 p2441 p3051 p3527 p3644 p4539 p4909 : Prop) (h : p2027 ∨ (¬ p2441) ∨ (¬ p4539) ∨ (¬ p3644) ∨ (¬ p3527) ∨ (¬ p4909) ∨ (¬ p3051)) : (p2027) ∨ (¬ p2441) ∨ (¬ p3051) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p4539) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial30243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4539)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory19499 t (m.theta 0 5) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule30243 (meaning t m 2027) (meaning t m 2441) (meaning t m 3051) (meaning t m 3527) (meaning t m 3644) (meaning t m 4539) (meaning t m 4909) source

theorem rule30245 (p2027 p2247 p2598 p2911 p3201 p3324 p4154 p4503 p4733 : Prop) (h : (¬ p3201) ∨ (¬ p4733) ∨ (¬ p2911) ∨ (¬ p4503) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3324) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4503) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial30245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory19501 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8)
  exact rule30245 (meaning t m 2027) (meaning t m 2247) (meaning t m 2598) (meaning t m 2911) (meaning t m 3201) (meaning t m 3324) (meaning t m 4154) (meaning t m 4503) (meaning t m 4733) source

theorem rule30249 (p2027 p2352 p2573 p3954 p3979 p4379 p5119 p5190 p5387 : Prop) (h : (¬ p5190) ∨ (¬ p5387) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p4379) ∨ (¬ p3979) ∨ (¬ p3954) ∨ (¬ p2352) ∨ (¬ p5119)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3954) ∨ (¬ p3979) ∨ (¬ p4379) ∨ (¬ p5119) ∨ (¬ p5190) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial30249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5190)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory19505 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 9) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule30249 (meaning t m 2027) (meaning t m 2352) (meaning t m 2573) (meaning t m 3954) (meaning t m 3979) (meaning t m 4379) (meaning t m 5119) (meaning t m 5190) (meaning t m 5387) source

theorem rule30253 (p2027 p2144 p2220 p3583 p3694 p4737 : Prop) (h : (¬ p2144) ∨ (¬ p3694) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p3583) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial30253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory19509 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 8)
  exact rule30253 (meaning t m 2027) (meaning t m 2144) (meaning t m 2220) (meaning t m 3583) (meaning t m 3694) (meaning t m 4737) source

theorem rule30255 (p3449 p3834 p4351 : Prop) (h : (¬ p3834) ∨ (¬ p4351) ∨ (¬ p3449)) : (¬ p3449) ∨ (¬ p3834) ∨ (¬ p4351) := by
  classical
  tauto

theorem initial30255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4351)) := by
  have source := ElevenTheory.theory19511 (m.theta 0 1) (m.theta 1 8) (m.theta 1 9)
  exact rule30255 (meaning t m 3449) (meaning t m 3834) (meaning t m 4351) source

theorem rule30257 (p1987 p2027 p2287 p2737 p2785 p3323 p3688 p3946 : Prop) (h : (¬ p1987) ∨ p2287 ∨ (¬ p3688) ∨ (¬ p2785) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p3946) ∨ (¬ p3323)) : (¬ p1987) ∨ (p2027) ∨ (p2287) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3323) ∨ (¬ p3688) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial30257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory19513 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 9)
  exact rule30257 (meaning t m 1987) (meaning t m 2027) (meaning t m 2287) (meaning t m 2737) (meaning t m 2785) (meaning t m 3323) (meaning t m 3688) (meaning t m 3946) source

theorem rule30258 (p2027 p2440 p3343 p4385 p4882 p4952 : Prop) (h : (¬ p4952) ∨ (¬ p2440) ∨ (¬ p4882) ∨ p2027 ∨ (¬ p3343) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3343) ∨ (¬ p4385) ∨ (¬ p4882) ∨ (¬ p4952) := by
  classical
  tauto

theorem initial30258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4882)) ∨ (¬ (meaning t m 4952)) := by
  have source := ElevenTheory.theory19514 t (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9)
  exact rule30258 (meaning t m 2027) (meaning t m 2440) (meaning t m 3343) (meaning t m 4385) (meaning t m 4882) (meaning t m 4952) source

theorem rule30259 (p1999 p2027 p2202 p2475 p3083 p3319 p3574 p3660 p3923 p4113 : Prop) (h : (¬ p3319) ∨ (¬ p3083) ∨ (¬ p4113) ∨ (¬ p3574) ∨ (¬ p3923) ∨ (¬ p2475) ∨ p2202 ∨ (¬ p1999) ∨ (¬ p3660) ∨ p2027) : (¬ p1999) ∨ (p2027) ∨ (p2202) ∨ (¬ p2475) ∨ (¬ p3083) ∨ (¬ p3319) ∨ (¬ p3574) ∨ (¬ p3660) ∨ (¬ p3923) ∨ (¬ p4113) := by
  classical
  tauto

theorem initial30259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4113)) := by
  have source := ElevenTheory.theory19515 t (m.theta 0 8) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9)
  exact rule30259 (meaning t m 1999) (meaning t m 2027) (meaning t m 2202) (meaning t m 2475) (meaning t m 3083) (meaning t m 3319) (meaning t m 3574) (meaning t m 3660) (meaning t m 3923) (meaning t m 4113) source

theorem rule30260 (p2027 p2901 p3497 p3516 p3691 p4132 p4668 : Prop) (h : (¬ p3497) ∨ (¬ p4668) ∨ (¬ p2901) ∨ p2027 ∨ (¬ p3516) ∨ (¬ p4132) ∨ (¬ p3691)) : (p2027) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p4132) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial30260 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory19516 t (m.theta 0 7) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9)
  exact rule30260 (meaning t m 2027) (meaning t m 2901) (meaning t m 3497) (meaning t m 3516) (meaning t m 3691) (meaning t m 4132) (meaning t m 4668) source

theorem rule30264 (p1987 p2027 p2287 p2295 p2313 p2737 p2785 p3688 : Prop) (h : (¬ p2785) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2737) ∨ (¬ p1987) ∨ (¬ p3688) ∨ p2287) : (¬ p1987) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial30264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory19520 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule30264 (meaning t m 1987) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 2313) (meaning t m 2737) (meaning t m 2785) (meaning t m 3688) source

theorem rule30266 (p1975 p2027 p2493 p2509 p2553 p2842 p3641 : Prop) (h : (¬ p2553) ∨ (¬ p1975) ∨ (¬ p2493) ∨ p2027 ∨ p2842 ∨ (¬ p3641) ∨ (¬ p2509)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2553) ∨ (p2842) ∨ (¬ p3641) := by
  classical
  tauto

theorem initial30266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3641)) := by
  have source := ElevenTheory.theory19522 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule30266 (meaning t m 1975) (meaning t m 2027) (meaning t m 2493) (meaning t m 2509) (meaning t m 2553) (meaning t m 2842) (meaning t m 3641) source

theorem rule30276 (p2027 p2138 p3166 p3256 p3758 p3989 p4348 p4503 p4786 : Prop) (h : (¬ p3989) ∨ (¬ p4786) ∨ (¬ p4503) ∨ (¬ p3758) ∨ (¬ p3166) ∨ (¬ p2138) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3256)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial30276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory19532 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule30276 (meaning t m 2027) (meaning t m 2138) (meaning t m 3166) (meaning t m 3256) (meaning t m 3758) (meaning t m 3989) (meaning t m 4348) (meaning t m 4503) (meaning t m 4786) source

theorem rule30280 (p2005 p2027 p2588 p2633 p3548 p3631 p4107 : Prop) (h : (¬ p3548) ∨ (¬ p3631) ∨ p2633 ∨ (¬ p2005) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p4107)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2588) ∨ (p2633) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial30280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory19536 t (m.theta 1 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule30280 (meaning t m 2005) (meaning t m 2027) (meaning t m 2588) (meaning t m 2633) (meaning t m 3548) (meaning t m 3631) (meaning t m 4107) source

theorem rule30285 (p1975 p2027 p2274 p2766 p3266 p3744 p4191 : Prop) (h : (¬ p4191) ∨ (¬ p1975) ∨ (¬ p2274) ∨ p2766 ∨ (¬ p3266) ∨ p2027 ∨ (¬ p3744)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3744) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial30285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory19541 t (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30285 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2766) (meaning t m 3266) (meaning t m 3744) (meaning t m 4191) source

theorem rule30287 (p1999 p2027 p2633 p3125 p3941 p3989 p5580 : Prop) (h : (¬ p1999) ∨ (¬ p3125) ∨ (¬ p3989) ∨ p2027 ∨ p2633 ∨ (¬ p3941) ∨ (¬ p5580)) : (¬ p1999) ∨ (p2027) ∨ (p2633) ∨ (¬ p3125) ∨ (¬ p3941) ∨ (¬ p3989) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial30287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory19543 t (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10)
  exact rule30287 (meaning t m 1999) (meaning t m 2027) (meaning t m 2633) (meaning t m 3125) (meaning t m 3941) (meaning t m 3989) (meaning t m 5580) source

theorem rule30290 (p2027 p2657 p3366 p3399 p3555 p3631 p3644 p3683 p3876 p4236 p4377 p4668 : Prop) (h : p2027 ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p2657) ∨ (¬ p3876) ∨ (¬ p3683) ∨ (¬ p4377) ∨ (¬ p4236) ∨ (¬ p3631) ∨ (¬ p3644) ∨ (¬ p3366) ∨ (¬ p4668)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3631) ∨ (¬ p3644) ∨ (¬ p3683) ∨ (¬ p3876) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial30290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory19546 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule30290 (meaning t m 2027) (meaning t m 2657) (meaning t m 3366) (meaning t m 3399) (meaning t m 3555) (meaning t m 3631) (meaning t m 3644) (meaning t m 3683) (meaning t m 3876) (meaning t m 4236) (meaning t m 4377) (meaning t m 4668) source

theorem rule30291 (p2027 p2139 p2761 p3055 p3516 p3584 p4137 p4444 p4604 p4988 : Prop) (h : (¬ p3584) ∨ (¬ p2139) ∨ (¬ p4137) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p4988) ∨ (¬ p3516) ∨ (¬ p2761) ∨ (¬ p4444) ∨ (¬ p4604)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2761) ∨ (¬ p3055) ∨ (¬ p3516) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial30291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory19547 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 7) (m.theta 2 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30291 (meaning t m 2027) (meaning t m 2139) (meaning t m 2761) (meaning t m 3055) (meaning t m 3516) (meaning t m 3584) (meaning t m 4137) (meaning t m 4444) (meaning t m 4604) (meaning t m 4988) source

theorem rule30293 (p2011 p2027 p2388 p3506 p3755 p4315 p4322 : Prop) (h : p2388 ∨ (¬ p3755) ∨ (¬ p2011) ∨ (¬ p4322) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p3506)) : (¬ p2011) ∨ (p2027) ∨ (p2388) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4315) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial30293 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory19549 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule30293 (meaning t m 2011) (meaning t m 2027) (meaning t m 2388) (meaning t m 3506) (meaning t m 3755) (meaning t m 4315) (meaning t m 4322) source

theorem rule30294 (p1976 p2027 p2202 p2440 p3055 p3343 p5160 : Prop) (h : p2202 ∨ (¬ p1976) ∨ (¬ p3343) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p5160) ∨ (¬ p3055)) : (¬ p1976) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3055) ∨ (¬ p3343) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial30294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory19550 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9)
  exact rule30294 (meaning t m 1976) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3055) (meaning t m 3343) (meaning t m 5160) source

theorem rule30298 (p1976 p2027 p3008 p3055 p3343 p3574 p5160 : Prop) (h : (¬ p5160) ∨ (¬ p1976) ∨ p3008 ∨ p2027 ∨ (¬ p3574) ∨ (¬ p3055) ∨ (¬ p3343)) : (¬ p1976) ∨ (p2027) ∨ (p3008) ∨ (¬ p3055) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial30298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory19554 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9)
  exact rule30298 (meaning t m 1976) (meaning t m 2027) (meaning t m 3008) (meaning t m 3055) (meaning t m 3343) (meaning t m 3574) (meaning t m 5160) source

theorem rule30300 (p2012 p2027 p2241 p2699 p2727 p3506 p4425 p5176 : Prop) (h : (¬ p2727) ∨ (¬ p5176) ∨ (¬ p4425) ∨ (¬ p2241) ∨ p2027 ∨ p2699 ∨ (¬ p2012) ∨ (¬ p3506)) : (¬ p2012) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p3506) ∨ (¬ p4425) ∨ (¬ p5176) := by
  classical
  tauto

theorem initial30300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5176)) := by
  have source := ElevenTheory.theory19556 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 9) (m.theta 9 10)
  exact rule30300 (meaning t m 2012) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2727) (meaning t m 3506) (meaning t m 4425) (meaning t m 5176) source

theorem rule30308 (p2027 p2608 p3276 p3355 p3519 p3555 p4376 p4385 p4418 p4444 p5059 : Prop) (h : (¬ p3355) ∨ (¬ p4418) ∨ (¬ p3276) ∨ (¬ p4376) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p3519) ∨ (¬ p4385) ∨ (¬ p5059) ∨ (¬ p4444) ∨ p2027) : (p2027) ∨ (¬ p2608) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3519) ∨ (¬ p3555) ∨ (¬ p4376) ∨ (¬ p4385) ∨ (¬ p4418) ∨ (¬ p4444) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial30308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory19564 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 5) (m.theta 4 9) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30308 (meaning t m 2027) (meaning t m 2608) (meaning t m 3276) (meaning t m 3355) (meaning t m 3519) (meaning t m 3555) (meaning t m 4376) (meaning t m 4385) (meaning t m 4418) (meaning t m 4444) (meaning t m 5059) source

theorem rule30310 (p3670 p3680 p5026 : Prop) (h : (¬ p3670) ∨ (¬ p5026) ∨ p3680) : (¬ p3670) ∨ (p3680) ∨ (¬ p5026) := by
  classical
  tauto

theorem initial30310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3670)) ∨ (meaning t m 3680) ∨ (¬ (meaning t m 5026)) := by
  have source := ElevenTheory.theory19566 (m.theta 2 9) (m.theta 5 9) (m.theta 9 10)
  exact rule30310 (meaning t m 3670) (meaning t m 3680) (meaning t m 5026) source

theorem rule30311 (p2027 p2241 p2274 p2313 p2727 p3343 p3744 p5021 p5322 : Prop) (h : (¬ p5322) ∨ (¬ p2241) ∨ (¬ p5021) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p2727) ∨ (¬ p2274) ∨ (¬ p3744) ∨ (¬ p3343)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3744) ∨ (¬ p5021) ∨ (¬ p5322) := by
  classical
  tauto

theorem initial30311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 5021)) ∨ (¬ (meaning t m 5322)) := by
  have source := ElevenTheory.theory19567 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule30311 (meaning t m 2027) (meaning t m 2241) (meaning t m 2274) (meaning t m 2313) (meaning t m 2727) (meaning t m 3343) (meaning t m 3744) (meaning t m 5021) (meaning t m 5322) source

theorem rule30312 (p2027 p2573 p2663 p3343 p3425 p3574 p3659 p4332 p4348 p4786 : Prop) (h : (¬ p4348) ∨ (¬ p3659) ∨ (¬ p4332) ∨ (¬ p3343) ∨ (¬ p2573) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p4786) ∨ (¬ p3574) ∨ (¬ p2663)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p3343) ∨ (¬ p3425) ∨ (¬ p3574) ∨ (¬ p3659) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial30312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory19568 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9)
  exact rule30312 (meaning t m 2027) (meaning t m 2573) (meaning t m 2663) (meaning t m 3343) (meaning t m 3425) (meaning t m 3574) (meaning t m 3659) (meaning t m 4332) (meaning t m 4348) (meaning t m 4786) source

theorem rule30313 (p2027 p2780 p3166 p3256 p3266 p3822 p4260 p4786 p4831 : Prop) (h : (¬ p4260) ∨ p2027 ∨ (¬ p4786) ∨ (¬ p4831) ∨ (¬ p2780) ∨ (¬ p3256) ∨ (¬ p3166) ∨ (¬ p3266) ∨ (¬ p3822)) : (p2027) ∨ (¬ p2780) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3822) ∨ (¬ p4260) ∨ (¬ p4786) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial30313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory19569 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 8) (m.theta 6 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule30313 (meaning t m 2027) (meaning t m 2780) (meaning t m 3166) (meaning t m 3256) (meaning t m 3266) (meaning t m 3822) (meaning t m 4260) (meaning t m 4786) (meaning t m 4831) source

theorem rule30315 (p1976 p2027 p2579 p2938 p3483 p3905 p3985 p4137 p4244 : Prop) (h : (¬ p1976) ∨ (¬ p4244) ∨ p2938 ∨ (¬ p3985) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p3905) ∨ (¬ p2579) ∨ (¬ p3483)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2579) ∨ (p2938) ∨ (¬ p3483) ∨ (¬ p3905) ∨ (¬ p3985) ∨ (¬ p4137) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial30315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory19571 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 2 6) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9)
  exact rule30315 (meaning t m 1976) (meaning t m 2027) (meaning t m 2579) (meaning t m 2938) (meaning t m 3483) (meaning t m 3905) (meaning t m 3985) (meaning t m 4137) (meaning t m 4244) source

theorem rule30316 (p2027 p2247 p2459 p2911 p3389 p3662 p4208 p5059 p5190 : Prop) (h : (¬ p3662) ∨ (¬ p5190) ∨ (¬ p4208) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p2459) ∨ (¬ p5059) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p5059) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial30316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 5059)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory19572 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule30316 (meaning t m 2027) (meaning t m 2247) (meaning t m 2459) (meaning t m 2911) (meaning t m 3389) (meaning t m 3662) (meaning t m 4208) (meaning t m 5059) (meaning t m 5190) source

theorem rule30323 (p2027 p2417 p2780 p2829 p3389 p3570 p3588 p3657 p3873 p4898 p5190 : Prop) (h : (¬ p5190) ∨ (¬ p2829) ∨ (¬ p3657) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p4898) ∨ (¬ p3873) ∨ (¬ p3389) ∨ (¬ p3570) ∨ (¬ p3588)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3389) ∨ (¬ p3570) ∨ (¬ p3588) ∨ (¬ p3657) ∨ (¬ p3873) ∨ (¬ p4898) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial30323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4898)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory19579 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule30323 (meaning t m 2027) (meaning t m 2417) (meaning t m 2780) (meaning t m 2829) (meaning t m 3389) (meaning t m 3570) (meaning t m 3588) (meaning t m 3657) (meaning t m 3873) (meaning t m 4898) (meaning t m 5190) source

theorem rule30325 (p2027 p2248 p2946 p3146 p3156 p3591 p3923 p5118 p5580 : Prop) (h : (¬ p5118) ∨ (¬ p3156) ∨ (¬ p2248) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p2946) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p5580)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial30325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory19581 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule30325 (meaning t m 2027) (meaning t m 2248) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3591) (meaning t m 3923) (meaning t m 5118) (meaning t m 5580) source

theorem rule30327 (p2027 p2156 p2406 p3952 p4109 p4700 p4814 : Prop) (h : (¬ p2406) ∨ (¬ p4700) ∨ (¬ p4109) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p4814) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2406) ∨ (¬ p3952) ∨ (¬ p4109) ∨ (¬ p4700) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial30327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory19583 t (m.theta 0 5) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule30327 (meaning t m 2027) (meaning t m 2156) (meaning t m 2406) (meaning t m 3952) (meaning t m 4109) (meaning t m 4700) (meaning t m 4814) source

theorem rule30329 (p1988 p2027 p2114 p2749 p2952 p2992 p3286 p3680 p4039 : Prop) (h : p2027 ∨ (¬ p2952) ∨ p2114 ∨ (¬ p3286) ∨ (¬ p2992) ∨ (¬ p4039) ∨ (¬ p2749) ∨ (¬ p1988) ∨ (¬ p3680)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2749) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3286) ∨ (¬ p3680) ∨ (¬ p4039) := by
  classical
  tauto

theorem initial30329 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4039)) := by
  have source := ElevenTheory.theory19585 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule30329 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2749) (meaning t m 2952) (meaning t m 2992) (meaning t m 3286) (meaning t m 3680) (meaning t m 4039) source

theorem rule30333 (p2027 p2132 p2619 p2753 p3379 p3834 p3969 p4321 p5119 p5216 : Prop) (h : (¬ p3834) ∨ (¬ p2619) ∨ (¬ p4321) ∨ (¬ p2753) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p5216) ∨ (¬ p5119) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p3969) ∨ (¬ p4321) ∨ (¬ p5119) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial30333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory19589 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 2 5) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule30333 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 2753) (meaning t m 3379) (meaning t m 3834) (meaning t m 3969) (meaning t m 4321) (meaning t m 5119) (meaning t m 5216) source

theorem rule30335 (p2027 p2449 p2589 p2685 p2696 p2753 p3347 p3744 p4110 p4625 p5216 : Prop) (h : (¬ p3347) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p2685) ∨ (¬ p4110) ∨ (¬ p2696) ∨ (¬ p2449) ∨ (¬ p2589) ∨ (¬ p3744) ∨ (¬ p4625)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2589) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4625) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial30335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory19591 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule30335 (meaning t m 2027) (meaning t m 2449) (meaning t m 2589) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3347) (meaning t m 3744) (meaning t m 4110) (meaning t m 4625) (meaning t m 5216) source

theorem rule30339 (p2027 p2255 p2264 p2459 p2579 p2662 p2807 p4111 p4137 p4604 : Prop) (h : (¬ p4137) ∨ (¬ p2264) ∨ (¬ p2579) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2662) ∨ (¬ p2807) ∨ (¬ p2255) ∨ (¬ p4111)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p2807) ∨ (¬ p4111) ∨ (¬ p4137) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial30339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory19595 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule30339 (meaning t m 2027) (meaning t m 2255) (meaning t m 2264) (meaning t m 2459) (meaning t m 2579) (meaning t m 2662) (meaning t m 2807) (meaning t m 4111) (meaning t m 4137) (meaning t m 4604) source

theorem rule30340 (p2027 p2253 p2264 p2459 p2807 p3055 p3584 p4137 p4604 p4736 : Prop) (h : (¬ p3055) ∨ (¬ p4736) ∨ (¬ p4137) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p4604) ∨ (¬ p2253) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p3584)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial30340 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory19596 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule30340 (meaning t m 2027) (meaning t m 2253) (meaning t m 2264) (meaning t m 2459) (meaning t m 2807) (meaning t m 3055) (meaning t m 3584) (meaning t m 4137) (meaning t m 4604) (meaning t m 4736) source

theorem rule30343 (p1998 p2027 p2241 p2264 p2699 p3707 p3833 p4429 p5284 : Prop) (h : (¬ p2241) ∨ p2699 ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p5284) ∨ (¬ p3833) ∨ (¬ p3707) ∨ (¬ p4429)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (p2699) ∨ (¬ p3707) ∨ (¬ p3833) ∨ (¬ p4429) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial30343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3833)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory19599 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 3 7) (m.theta 3 9) (m.theta 7 8) (m.theta 9 10)
  exact rule30343 (meaning t m 1998) (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 2699) (meaning t m 3707) (meaning t m 3833) (meaning t m 4429) (meaning t m 5284) source

theorem rule30344 (p2027 p2136 p3286 p3506 p3646 p3950 p3989 p4347 p4381 p4786 : Prop) (h : (¬ p3989) ∨ (¬ p3506) ∨ (¬ p3286) ∨ (¬ p2136) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p4347) ∨ (¬ p4786) ∨ (¬ p3950) ∨ (¬ p4381)) : (p2027) ∨ (¬ p2136) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p4347) ∨ (¬ p4381) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial30344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory19600 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 9) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30344 (meaning t m 2027) (meaning t m 2136) (meaning t m 3286) (meaning t m 3506) (meaning t m 3646) (meaning t m 3950) (meaning t m 3989) (meaning t m 4347) (meaning t m 4381) (meaning t m 4786) source

theorem rule30345 (p2027 p2745 p2996 p3434 p3947 p4781 : Prop) (h : (¬ p2745) ∨ p2027 ∨ (¬ p4781) ∨ (¬ p3947) ∨ (¬ p2996) ∨ (¬ p3434)) : (p2027) ∨ (¬ p2745) ∨ (¬ p2996) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial30345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory19601 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 9)
  exact rule30345 (meaning t m 2027) (meaning t m 2745) (meaning t m 2996) (meaning t m 3434) (meaning t m 3947) (meaning t m 4781) source

theorem rule30352 (p1982 p2027 p2122 p2177 p2459 p2611 p2774 : Prop) (h : p2611 ∨ (¬ p2774) ∨ (¬ p2177) ∨ (¬ p2122) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2459) ∨ (p2611) ∨ (¬ p2774) := by
  classical
  tauto

theorem initial30352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) := by
  have source := ElevenTheory.theory19608 t (m.theta 0 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule30352 (meaning t m 1982) (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2459) (meaning t m 2611) (meaning t m 2774) source

theorem rule30357 (p2027 p2122 p2396 p2589 p2774 p3692 p3880 p3950 p4729 : Prop) (h : (¬ p3950) ∨ (¬ p2122) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p2396) ∨ (¬ p2774) ∨ (¬ p4729)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2589) ∨ (¬ p2774) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3950) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial30357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory19613 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule30357 (meaning t m 2027) (meaning t m 2122) (meaning t m 2396) (meaning t m 2589) (meaning t m 2774) (meaning t m 3692) (meaning t m 3880) (meaning t m 3950) (meaning t m 4729) source

theorem rule30364 (p2027 p2138 p2307 p2737 p2811 p3791 p3987 p4243 p4322 p4363 p4734 p4826 : Prop) (h : (¬ p2138) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p4363) ∨ (¬ p4734) ∨ (¬ p4826) ∨ (¬ p2307) ∨ (¬ p3987) ∨ (¬ p4322) ∨ (¬ p4243) ∨ (¬ p3791)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2307) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3791) ∨ (¬ p3987) ∨ (¬ p4243) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p4734) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial30364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory19620 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule30364 (meaning t m 2027) (meaning t m 2138) (meaning t m 2307) (meaning t m 2737) (meaning t m 2811) (meaning t m 3791) (meaning t m 3987) (meaning t m 4243) (meaning t m 4322) (meaning t m 4363) (meaning t m 4734) (meaning t m 4826) source

theorem rule30369 (p3324 p3568 p3955 : Prop) (h : (¬ p3955) ∨ (¬ p3568) ∨ p3324) : (p3324) ∨ (¬ p3568) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial30369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3324) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory19625 (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30369 (meaning t m 3324) (meaning t m 3568) (meaning t m 3955) source

theorem rule30370 (p2027 p3093 p3266 p3292 p3319 p3366 p3452 p4236 p4330 p4376 p5284 : Prop) (h : p2027 ∨ (¬ p4330) ∨ (¬ p4236) ∨ (¬ p3093) ∨ (¬ p3452) ∨ (¬ p4376) ∨ (¬ p3319) ∨ (¬ p3292) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p5284)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3319) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p4236) ∨ (¬ p4330) ∨ (¬ p4376) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial30370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory19626 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 3 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30370 (meaning t m 2027) (meaning t m 3093) (meaning t m 3266) (meaning t m 3292) (meaning t m 3319) (meaning t m 3366) (meaning t m 3452) (meaning t m 4236) (meaning t m 4330) (meaning t m 4376) (meaning t m 5284) source

theorem rule30371 (p2027 p2230 p2387 p2668 p2787 p2870 p3246 p3362 p3698 p4037 p4625 : Prop) (h : (¬ p2387) ∨ (¬ p2787) ∨ (¬ p2668) ∨ (¬ p4625) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p4037) ∨ (¬ p3362) ∨ (¬ p3246) ∨ (¬ p2230) ∨ (¬ p3698)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2787) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3362) ∨ (¬ p3698) ∨ (¬ p4037) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial30371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory19627 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 2 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule30371 (meaning t m 2027) (meaning t m 2230) (meaning t m 2387) (meaning t m 2668) (meaning t m 2787) (meaning t m 2870) (meaning t m 3246) (meaning t m 3362) (meaning t m 3698) (meaning t m 4037) (meaning t m 4625) source

theorem rule30372 (p2027 p3276 p3355 p3555 p3744 p4173 p4444 p4604 p5190 : Prop) (h : (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p4173) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p4444)) : (p2027) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial30372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory19628 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 4 9) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30372 (meaning t m 2027) (meaning t m 3276) (meaning t m 3355) (meaning t m 3555) (meaning t m 3744) (meaning t m 4173) (meaning t m 4444) (meaning t m 4604) (meaning t m 5190) source

theorem rule30374 (p2027 p2098 p2191 p2192 p2534 p3369 p3609 p3646 p4158 p4733 : Prop) (h : p2027 ∨ (¬ p4158) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p4733) ∨ (¬ p3609) ∨ (¬ p3646) ∨ (¬ p3369) ∨ (¬ p2098) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2534) ∨ (¬ p3369) ∨ (¬ p3609) ∨ (¬ p3646) ∨ (¬ p4158) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial30374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4158)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory19630 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 2 8) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule30374 (meaning t m 2027) (meaning t m 2098) (meaning t m 2191) (meaning t m 2192) (meaning t m 2534) (meaning t m 3369) (meaning t m 3609) (meaning t m 3646) (meaning t m 4158) (meaning t m 4733) source

theorem rule30375 (p1987 p2027 p2138 p2633 p2696 p3486 p3570 p4243 : Prop) (h : (¬ p3570) ∨ p2633 ∨ (¬ p4243) ∨ (¬ p3486) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p2696) ∨ (¬ p2138)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2138) ∨ (p2633) ∨ (¬ p2696) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial30375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory19631 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule30375 (meaning t m 1987) (meaning t m 2027) (meaning t m 2138) (meaning t m 2633) (meaning t m 2696) (meaning t m 3486) (meaning t m 3570) (meaning t m 4243) source

theorem rule30376 (p1990 p2027 p2233 p2341 p3564 p3581 p3644 p3744 p5201 : Prop) (h : (¬ p2341) ∨ p2233 ∨ (¬ p1990) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p5201) ∨ (¬ p3644) ∨ (¬ p3581) ∨ (¬ p3744)) : (¬ p1990) ∨ (p2027) ∨ (p2233) ∨ (¬ p2341) ∨ (¬ p3564) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p3744) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial30376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory19632 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8)
  exact rule30376 (meaning t m 1990) (meaning t m 2027) (meaning t m 2233) (meaning t m 2341) (meaning t m 3564) (meaning t m 3581) (meaning t m 3644) (meaning t m 3744) (meaning t m 5201) source

theorem rule30384 (p1982 p2027 p2608 p2699 p2737 p3005 p3256 : Prop) (h : p2027 ∨ (¬ p2608) ∨ (¬ p1982) ∨ (¬ p3256) ∨ p2699 ∨ (¬ p3005) ∨ (¬ p2737)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p3256) := by
  classical
  tauto

theorem initial30384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) := by
  have source := ElevenTheory.theory19640 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 8 9)
  exact rule30384 (meaning t m 1982) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2737) (meaning t m 3005) (meaning t m 3256) source

theorem rule30391 (p2027 p2493 p2509 p2819 p4432 p5225 : Prop) (h : (¬ p2493) ∨ (¬ p2509) ∨ p2027 ∨ (¬ p5225) ∨ (¬ p4432) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2819) ∨ (¬ p4432) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial30391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory19647 t (m.theta 1 4) (m.theta 2 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule30391 (meaning t m 2027) (meaning t m 2493) (meaning t m 2509) (meaning t m 2819) (meaning t m 4432) (meaning t m 5225) source

theorem rule30397 (p2005 p2027 p2493 p2997 p3193 p3323 p3568 p4022 : Prop) (h : (¬ p4022) ∨ (¬ p3568) ∨ p2997 ∨ (¬ p2493) ∨ p2027 ∨ (¬ p3323) ∨ (¬ p2005) ∨ (¬ p3193)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2493) ∨ (p2997) ∨ (¬ p3193) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4022) := by
  classical
  tauto

theorem initial30397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4022)) := by
  have source := ElevenTheory.theory19653 t (m.theta 1 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 9)
  exact rule30397 (meaning t m 2005) (meaning t m 2027) (meaning t m 2493) (meaning t m 2997) (meaning t m 3193) (meaning t m 3323) (meaning t m 3568) (meaning t m 4022) source

theorem rule30398 (p2007 p2027 p2534 p2545 p2810 p3005 p3256 : Prop) (h : (¬ p3256) ∨ (¬ p2810) ∨ (¬ p2007) ∨ p2545 ∨ p2027 ∨ (¬ p2534) ∨ (¬ p3005)) : (¬ p2007) ∨ (p2027) ∨ (¬ p2534) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3256) := by
  classical
  tauto

theorem initial30398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) := by
  have source := ElevenTheory.theory19654 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule30398 (meaning t m 2007) (meaning t m 2027) (meaning t m 2534) (meaning t m 2545) (meaning t m 2810) (meaning t m 3005) (meaning t m 3256) source

theorem rule30399 (p2015 p2027 p2573 p2914 p3540 p3888 p4435 : Prop) (h : (¬ p2015) ∨ p2027 ∨ (¬ p4435) ∨ (¬ p3540) ∨ (¬ p2573) ∨ p2914 ∨ (¬ p3888)) : (¬ p2015) ∨ (p2027) ∨ (¬ p2573) ∨ (p2914) ∨ (¬ p3540) ∨ (¬ p3888) ∨ (¬ p4435) := by
  classical
  tauto

theorem initial30399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4435)) := by
  have source := ElevenTheory.theory19655 t (m.theta 0 4) (m.theta 1 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 10)
  exact rule30399 (meaning t m 2015) (meaning t m 2027) (meaning t m 2573) (meaning t m 2914) (meaning t m 3540) (meaning t m 3888) (meaning t m 4435) source

theorem rule30400 (p1998 p2027 p2264 p2608 p2685 p2699 p2737 : Prop) (h : (¬ p1998) ∨ (¬ p2608) ∨ p2027 ∨ p2699 ∨ (¬ p2264) ∨ (¬ p2737) ∨ (¬ p2685)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2608) ∨ (¬ p2685) ∨ (p2699) ∨ (¬ p2737) := by
  classical
  tauto

theorem initial30400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2685)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2737)) := by
  have source := ElevenTheory.theory19656 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8)
  exact rule30400 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2608) (meaning t m 2685) (meaning t m 2699) (meaning t m 2737) source

theorem rule30405 (p2027 p2459 p3322 p3767 p4133 p4191 p4456 : Prop) (h : p2027 ∨ (¬ p3322) ∨ (¬ p2459) ∨ (¬ p4456) ∨ (¬ p4191) ∨ (¬ p3767) ∨ (¬ p4133)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3322) ∨ (¬ p3767) ∨ (¬ p4133) ∨ (¬ p4191) ∨ (¬ p4456) := by
  classical
  tauto

theorem initial30405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4456)) := by
  have source := ElevenTheory.theory19661 t (m.theta 0 9) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule30405 (meaning t m 2027) (meaning t m 2459) (meaning t m 3322) (meaning t m 3767) (meaning t m 4133) (meaning t m 4191) (meaning t m 4456) source

theorem rule30408 (p2027 p2299 p2662 p3083 p3540 p4404 p4712 : Prop) (h : (¬ p4712) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2662) ∨ (¬ p3083) ∨ (¬ p4404) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2662) ∨ (¬ p3083) ∨ (¬ p3540) ∨ (¬ p4404) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial30408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory19664 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule30408 (meaning t m 2027) (meaning t m 2299) (meaning t m 2662) (meaning t m 3083) (meaning t m 3540) (meaning t m 4404) (meaning t m 4712) source

theorem rule30409 (p1979 p2027 p2177 p2462 p3551 p3952 p4107 p4204 p4283 : Prop) (h : (¬ p2177) ∨ p2027 ∨ p2462 ∨ (¬ p1979) ∨ (¬ p4107) ∨ (¬ p3952) ∨ (¬ p4204) ∨ (¬ p4283) ∨ (¬ p3551)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2177) ∨ (p2462) ∨ (¬ p3551) ∨ (¬ p3952) ∨ (¬ p4107) ∨ (¬ p4204) ∨ (¬ p4283) := by
  classical
  tauto

theorem initial30409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4283)) := by
  have source := ElevenTheory.theory19665 t (m.theta 0 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule30409 (meaning t m 1979) (meaning t m 2027) (meaning t m 2177) (meaning t m 2462) (meaning t m 3551) (meaning t m 3952) (meaning t m 4107) (meaning t m 4204) (meaning t m 4283) source

theorem rule30412 (p2027 p2220 p2797 p3519 p3694 p4116 p4392 p4399 p4975 : Prop) (h : (¬ p2797) ∨ (¬ p4392) ∨ (¬ p4975) ∨ (¬ p4399) ∨ (¬ p4116) ∨ (¬ p3519) ∨ p2027 ∨ (¬ p3694) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2797) ∨ (¬ p3519) ∨ (¬ p3694) ∨ (¬ p4116) ∨ (¬ p4392) ∨ (¬ p4399) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial30412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory19668 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 4) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 6) (m.theta 5 8)
  exact rule30412 (meaning t m 2027) (meaning t m 2220) (meaning t m 2797) (meaning t m 3519) (meaning t m 3694) (meaning t m 4116) (meaning t m 4392) (meaning t m 4399) (meaning t m 4975) source

theorem rule30414 (p2027 p2138 p2247 p2744 p3366 p3399 p4075 p4322 p4385 p4826 : Prop) (h : (¬ p2138) ∨ (¬ p4075) ∨ (¬ p3399) ∨ (¬ p4826) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p4075) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial30414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory19670 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 5) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule30414 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3399) (meaning t m 4075) (meaning t m 4322) (meaning t m 4385) (meaning t m 4826) source

theorem rule30419 (p1988 p2027 p2307 p2344 p3323 p3461 p3568 : Prop) (h : (¬ p3568) ∨ p2344 ∨ (¬ p2307) ∨ (¬ p3323) ∨ (¬ p3461) ∨ p2027 ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2307) ∨ (p2344) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial30419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory19675 t (m.theta 0 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule30419 (meaning t m 1988) (meaning t m 2027) (meaning t m 2307) (meaning t m 2344) (meaning t m 3323) (meaning t m 3461) (meaning t m 3568) source

theorem rule30420 (p2177 p2318 p2341 : Prop) (h : (¬ p2177) ∨ (¬ p2318) ∨ p2341) : (¬ p2177) ∨ (¬ p2318) ∨ (p2341) := by
  classical
  tauto

theorem initial30420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2318)) ∨ (meaning t m 2341) := by
  have source := ElevenTheory.theory19676 (m.theta 0 7) (m.theta 6 7) (m.theta 7 8)
  exact rule30420 (meaning t m 2177) (meaning t m 2318) (meaning t m 2341) source

theorem rule30423 (p1995 p2027 p2373 p2765 p3369 p3379 p4110 p4120 : Prop) (h : (¬ p2373) ∨ p2027 ∨ (¬ p4120) ∨ p2765 ∨ (¬ p4110) ∨ (¬ p1995) ∨ (¬ p3369) ∨ (¬ p3379)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2373) ∨ (p2765) ∨ (¬ p3369) ∨ (¬ p3379) ∨ (¬ p4110) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial30423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory19679 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule30423 (meaning t m 1995) (meaning t m 2027) (meaning t m 2373) (meaning t m 2765) (meaning t m 3369) (meaning t m 3379) (meaning t m 4110) (meaning t m 4120) source

theorem rule30424 (p2027 p2499 p2518 p2588 p4157 p4405 : Prop) (h : (¬ p2499) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p4157) ∨ (¬ p2518)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2588) ∨ (¬ p4157) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial30424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory19680 t (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule30424 (meaning t m 2027) (meaning t m 2499) (meaning t m 2518) (meaning t m 2588) (meaning t m 4157) (meaning t m 4405) source

theorem rule30425 (p2027 p2881 p2891 p3553 p4386 p4960 : Prop) (h : (¬ p2891) ∨ (¬ p4960) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p4386) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3553) ∨ (¬ p4386) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial30425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory19681 t (m.theta 1 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule30425 (meaning t m 2027) (meaning t m 2881) (meaning t m 2891) (meaning t m 3553) (meaning t m 4386) (meaning t m 4960) source

theorem rule30427 (p2027 p2248 p2946 p3156 p3193 p3452 p3969 p4425 p5119 : Prop) (h : (¬ p2248) ∨ (¬ p3193) ∨ (¬ p4425) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p5119) ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial30427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory19683 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule30427 (meaning t m 2027) (meaning t m 2248) (meaning t m 2946) (meaning t m 3156) (meaning t m 3193) (meaning t m 3452) (meaning t m 3969) (meaning t m 4425) (meaning t m 5119) source

theorem rule30433 (p2027 p2363 p2785 p3857 p3914 p4197 p5586 : Prop) (h : (¬ p4197) ∨ (¬ p3914) ∨ (¬ p2785) ∨ (¬ p3857) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p5586)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2785) ∨ (¬ p3857) ∨ (¬ p3914) ∨ (¬ p4197) ∨ (¬ p5586) := by
  classical
  tauto

theorem initial30433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 5586)) := by
  have source := ElevenTheory.theory19689 t (m.theta 0 6) (m.theta 0 8) (m.theta 2 6) (m.theta 6 10) (m.theta 6 8) (m.theta 8 9)
  exact rule30433 (meaning t m 2027) (meaning t m 2363) (meaning t m 2785) (meaning t m 3857) (meaning t m 3914) (meaning t m 4197) (meaning t m 5586) source

end SunPrize.SMT
