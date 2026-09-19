import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory022
import SunPrize.Certificate.Theory023
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule17605 (p1997 p2027 p2534 p2542 p3146 p3578 p4256 : Prop) (h : (¬ p2542) ∨ p3578 ∨ (¬ p3146) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2534) ∨ (¬ p4256)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2542) ∨ (¬ p3146) ∨ (p3578) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial17605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory6877 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule17605 (meaning t m 1997) (meaning t m 2027) (meaning t m 2534) (meaning t m 2542) (meaning t m 3146) (meaning t m 3578) (meaning t m 4256) source

theorem rule17607 (p1981 p2027 p2323 p2641 p2668 p3166 p4360 : Prop) (h : (¬ p2641) ∨ (¬ p1981) ∨ (¬ p3166) ∨ (¬ p2668) ∨ p2027 ∨ p2323 ∨ (¬ p4360)) : (¬ p1981) ∨ (p2027) ∨ (p2323) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3166) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial17607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory6879 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8)
  exact rule17607 (meaning t m 1981) (meaning t m 2027) (meaning t m 2323) (meaning t m 2641) (meaning t m 2668) (meaning t m 3166) (meaning t m 4360) source

theorem rule17608 (p1997 p2027 p2542 p2766 p3644 p3742 p4348 : Prop) (h : (¬ p4348) ∨ p2766 ∨ (¬ p1997) ∨ (¬ p2542) ∨ (¬ p3644) ∨ (¬ p3742) ∨ p2027) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (p2766) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial17608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory6880 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule17608 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2766) (meaning t m 3644) (meaning t m 3742) (meaning t m 4348) source

theorem rule17609 (p1987 p2027 p2662 p2810 p3540 p3644 p3982 p5558 : Prop) (h : p2027 ∨ (¬ p3540) ∨ p3982 ∨ (¬ p5558) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p1987) ∨ (¬ p3644)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (p3982) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial17609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory6881 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10)
  exact rule17609 (meaning t m 1987) (meaning t m 2027) (meaning t m 2662) (meaning t m 2810) (meaning t m 3540) (meaning t m 3644) (meaning t m 3982) (meaning t m 5558) source

theorem rule17612 (p1994 p2027 p2459 p2633 p2651 p3172 p4118 : Prop) (h : (¬ p4118) ∨ p2633 ∨ (¬ p2651) ∨ (¬ p1994) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p3172)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2651) ∨ (¬ p3172) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial17612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory6884 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17612 (meaning t m 1994) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 2651) (meaning t m 3172) (meaning t m 4118) source

theorem rule17615 (p1987 p2027 p2651 p2764 p2810 p3292 p4425 p5171 : Prop) (h : (¬ p5171) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p2810) ∨ (¬ p3292) ∨ (¬ p2651) ∨ (¬ p4425) ∨ p2764) : (¬ p1987) ∨ (p2027) ∨ (¬ p2651) ∨ (p2764) ∨ (¬ p2810) ∨ (¬ p3292) ∨ (¬ p4425) ∨ (¬ p5171) := by
  classical
  tauto

theorem initial17615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5171)) := by
  have source := ElevenTheory.theory6887 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 9) (m.theta 9 10)
  exact rule17615 (meaning t m 1987) (meaning t m 2027) (meaning t m 2651) (meaning t m 2764) (meaning t m 2810) (meaning t m 3292) (meaning t m 4425) (meaning t m 5171) source

theorem rule17616 (p1992 p2027 p2247 p2608 p2633 p2996 p3644 p3740 : Prop) (h : (¬ p1992) ∨ (¬ p3644) ∨ (¬ p3740) ∨ p2027 ∨ (¬ p2996) ∨ p2633 ∨ (¬ p2247) ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2608) ∨ (p2633) ∨ (¬ p2996) ∨ (¬ p3644) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial17616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory6888 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule17616 (meaning t m 1992) (meaning t m 2027) (meaning t m 2247) (meaning t m 2608) (meaning t m 2633) (meaning t m 2996) (meaning t m 3644) (meaning t m 3740) source

theorem rule17617 (p1982 p2027 p2114 p2137 p2156 p2187 p2363 p2839 : Prop) (h : (¬ p2839) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2156) ∨ p2114 ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2137)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2839) := by
  classical
  tauto

theorem initial17617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2839)) := by
  have source := ElevenTheory.theory6889 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule17617 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 2839) source

theorem rule17620 (p1998 p2027 p2688 p2881 p3027 p3516 p3690 p4066 : Prop) (h : p2688 ∨ (¬ p4066) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p1998) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (p2688) ∨ (¬ p2881) ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4066) := by
  classical
  tauto

theorem initial17620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4066)) := by
  have source := ElevenTheory.theory6892 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17620 (meaning t m 1998) (meaning t m 2027) (meaning t m 2688) (meaning t m 2881) (meaning t m 3027) (meaning t m 3516) (meaning t m 3690) (meaning t m 4066) source

theorem rule17623 (p1975 p2027 p2246 p2264 p2299 p2331 p2388 p3662 p4156 : Prop) (h : (¬ p4156) ∨ (¬ p2331) ∨ (¬ p3662) ∨ p2027 ∨ p2388 ∨ (¬ p2246) ∨ (¬ p1975) ∨ (¬ p2299) ∨ (¬ p2264)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2331) ∨ (p2388) ∨ (¬ p3662) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial17623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory6895 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17623 (meaning t m 1975) (meaning t m 2027) (meaning t m 2246) (meaning t m 2264) (meaning t m 2299) (meaning t m 2331) (meaning t m 2388) (meaning t m 3662) (meaning t m 4156) source

theorem rule17626 (p1998 p2027 p2688 p2881 p2951 p2992 p3516 p3690 p4988 : Prop) (h : (¬ p2951) ∨ p2027 ∨ p2688 ∨ (¬ p4988) ∨ (¬ p3690) ∨ (¬ p2992) ∨ (¬ p3516) ∨ (¬ p2881) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (p2688) ∨ (¬ p2881) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial17626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory6898 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17626 (meaning t m 1998) (meaning t m 2027) (meaning t m 2688) (meaning t m 2881) (meaning t m 2951) (meaning t m 2992) (meaning t m 3516) (meaning t m 3690) (meaning t m 4988) source

theorem rule17632 (p2011 p2027 p2373 p2765 p3212 p4110 p4120 : Prop) (h : (¬ p3212) ∨ (¬ p4120) ∨ p2027 ∨ (¬ p2373) ∨ p2765 ∨ (¬ p2011) ∨ (¬ p4110)) : (¬ p2011) ∨ (p2027) ∨ (¬ p2373) ∨ (p2765) ∨ (¬ p3212) ∨ (¬ p4110) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial17632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory6904 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 5 9)
  exact rule17632 (meaning t m 2011) (meaning t m 2027) (meaning t m 2373) (meaning t m 2765) (meaning t m 3212) (meaning t m 4110) (meaning t m 4120) source

theorem rule17633 (p1982 p2027 p2114 p2137 p2459 p2839 p2881 p3051 : Prop) (h : (¬ p2137) ∨ p2114 ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2839)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2459) ∨ (¬ p2839) ∨ (¬ p2881) ∨ (¬ p3051) := by
  classical
  tauto

theorem initial17633 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) := by
  have source := ElevenTheory.theory6905 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule17633 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2459) (meaning t m 2839) (meaning t m 2881) (meaning t m 3051) source

theorem rule17634 (p1988 p2027 p2148 p2972 p3051 p3486 p3680 : Prop) (h : (¬ p3486) ∨ (¬ p1988) ∨ (¬ p2972) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p3051) ∨ p2148) : (¬ p1988) ∨ (p2027) ∨ (p2148) ∨ (¬ p2972) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial17634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory6906 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule17634 (meaning t m 1988) (meaning t m 2027) (meaning t m 2148) (meaning t m 2972) (meaning t m 3051) (meaning t m 3486) (meaning t m 3680) source

theorem rule17635 (p1977 p2027 p2352 p2588 p2997 p3324 p4154 : Prop) (h : p2997 ∨ (¬ p2352) ∨ (¬ p4154) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p3324)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3324) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial17635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory6907 t (m.theta 1 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule17635 (meaning t m 1977) (meaning t m 2027) (meaning t m 2352) (meaning t m 2588) (meaning t m 2997) (meaning t m 3324) (meaning t m 4154) source

theorem rule17639 (p1998 p2027 p2114 p2137 p2220 p2839 p3146 p4348 : Prop) (h : p2027 ∨ (¬ p1998) ∨ (¬ p3146) ∨ (¬ p2220) ∨ (¬ p4348) ∨ p2114 ∨ (¬ p2839) ∨ (¬ p2137)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2220) ∨ (¬ p2839) ∨ (¬ p3146) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial17639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory6911 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17639 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2220) (meaning t m 2839) (meaning t m 3146) (meaning t m 4348) source

theorem rule17642 (p2533 p3747 p4192 : Prop) (h : (¬ p2533) ∨ (¬ p3747) ∨ p4192) : (¬ p2533) ∨ (¬ p3747) ∨ (p4192) := by
  classical
  tauto

theorem initial17642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 3747)) ∨ (meaning t m 4192) := by
  have source := ElevenTheory.theory6914 (m.theta 5 7) (m.theta 5 8) (m.theta 5 9)
  exact rule17642 (meaning t m 2533) (meaning t m 3747) (meaning t m 4192) source

theorem rule17643 (p2001 p3128 p3692 p4604 : Prop) (h : (¬ p3692) ∨ p3128 ∨ (¬ p2001) ∨ p4604) : (¬ p2001) ∨ (p3128) ∨ (¬ p3692) ∨ (p4604) := by
  classical
  tauto

theorem initial17643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3692)) ∨ (meaning t m 4604) := by
  have source := ElevenTheory.theory6915 t (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule17643 (meaning t m 2001) (meaning t m 3128) (meaning t m 3692) (meaning t m 4604) source

theorem rule17644 (p2000 p2355 p3540 p4653 : Prop) (h : (¬ p3540) ∨ (¬ p2000) ∨ p4653 ∨ p2355) : (¬ p2000) ∨ (p2355) ∨ (¬ p3540) ∨ (p4653) := by
  classical
  tauto

theorem initial17644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 3540)) ∨ (meaning t m 4653) := by
  have source := ElevenTheory.theory6916 t (m.theta 0 4) (m.theta 3 7) (m.theta 4 7)
  exact rule17644 (meaning t m 2000) (meaning t m 2355) (meaning t m 3540) (meaning t m 4653) source

theorem rule17645 (p1978 p2027 p2766 p3556 p3941 p4119 p4348 p5568 : Prop) (h : (¬ p3556) ∨ (¬ p1978) ∨ (¬ p4348) ∨ p2027 ∨ p2766 ∨ (¬ p3941) ∨ (¬ p4119) ∨ (¬ p5568)) : (¬ p1978) ∨ (p2027) ∨ (p2766) ∨ (¬ p3556) ∨ (¬ p3941) ∨ (¬ p4119) ∨ (¬ p4348) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial17645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory6917 t (m.theta 0 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule17645 (meaning t m 1978) (meaning t m 2027) (meaning t m 2766) (meaning t m 3556) (meaning t m 3941) (meaning t m 4119) (meaning t m 4348) (meaning t m 5568) source

theorem rule17646 (p1975 p2027 p2406 p2409 p2440 p2553 p3016 : Prop) (h : (¬ p2440) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p3016) ∨ (¬ p2406) ∨ p2409) : (¬ p1975) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2440) ∨ (¬ p2553) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial17646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory6918 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule17646 (meaning t m 1975) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2440) (meaning t m 2553) (meaning t m 3016) source

theorem rule17647 (p1999 p2027 p2611 p2696 p3506 p3755 p4191 : Prop) (h : (¬ p1999) ∨ p2611 ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3755) ∨ (¬ p3506) ∨ (¬ p4191)) : (¬ p1999) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial17647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory6919 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule17647 (meaning t m 1999) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 3506) (meaning t m 3755) (meaning t m 4191) source

theorem rule17648 (p2020 p2027 p2611 p2668 p2696 p2797 p3979 : Prop) (h : (¬ p3979) ∨ p2027 ∨ (¬ p2797) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2668) ∨ (¬ p2020)) : (¬ p2020) ∨ (p2027) ∨ (p2611) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3979) := by
  classical
  tauto

theorem initial17648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3979)) := by
  have source := ElevenTheory.theory6920 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 10)
  exact rule17648 (meaning t m 2020) (meaning t m 2027) (meaning t m 2611) (meaning t m 2668) (meaning t m 2696) (meaning t m 2797) (meaning t m 3979) source

theorem rule17649 (p1986 p2027 p2764 p3684 p3692 p3880 p4444 : Prop) (h : (¬ p4444) ∨ (¬ p3880) ∨ (¬ p3692) ∨ (¬ p1986) ∨ p2764 ∨ p2027 ∨ (¬ p3684)) : (¬ p1986) ∨ (p2027) ∨ (p2764) ∨ (¬ p3684) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6921 t (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17649 (meaning t m 1986) (meaning t m 2027) (meaning t m 2764) (meaning t m 3684) (meaning t m 3692) (meaning t m 3880) (meaning t m 4444) source

theorem rule17650 (p1975 p2027 p2114 p2241 p2295 p2641 p3954 : Prop) (h : (¬ p2241) ∨ p2027 ∨ (¬ p1975) ∨ p2114 ∨ (¬ p3954) ∨ (¬ p2295) ∨ (¬ p2641)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial17650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory6922 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7)
  exact rule17650 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2241) (meaning t m 2295) (meaning t m 2641) (meaning t m 3954) source

theorem rule17651 (p1975 p2027 p2373 p2765 p3955 p3969 p4110 p5580 : Prop) (h : (¬ p3955) ∨ (¬ p2373) ∨ (¬ p5580) ∨ (¬ p3969) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p4110) ∨ p2765) : (¬ p1975) ∨ (p2027) ∨ (¬ p2373) ∨ (p2765) ∨ (¬ p3955) ∨ (¬ p3969) ∨ (¬ p4110) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial17651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory6923 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule17651 (meaning t m 1975) (meaning t m 2027) (meaning t m 2373) (meaning t m 2765) (meaning t m 3955) (meaning t m 3969) (meaning t m 4110) (meaning t m 5580) source

theorem rule17654 (p3292 p3987 p4036 p4038 p4190 : Prop) (h : (¬ p3987) ∨ (¬ p3292) ∨ (¬ p4038) ∨ (¬ p4036) ∨ (¬ p4190)) : (¬ p3292) ∨ (¬ p3987) ∨ (¬ p4036) ∨ (¬ p4038) ∨ (¬ p4190) := by
  classical
  tauto

theorem initial17654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4036)) ∨ (¬ (meaning t m 4038)) ∨ (¬ (meaning t m 4190)) := by
  have source := ElevenTheory.theory6926 (m.theta 0 3) (m.theta 0 6) (m.theta 0 9) (m.theta 3 9) (m.theta 6 9)
  exact rule17654 (meaning t m 3292) (meaning t m 3987) (meaning t m 4036) (meaning t m 4038) (meaning t m 4190) source

theorem rule17655 (p1978 p2027 p2299 p2563 p2633 p3646 p4235 p4275 : Prop) (h : (¬ p1978) ∨ (¬ p3646) ∨ (¬ p2299) ∨ p2633 ∨ (¬ p2563) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p4275)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2563) ∨ (p2633) ∨ (¬ p3646) ∨ (¬ p4235) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial17655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory6927 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17655 (meaning t m 1978) (meaning t m 2027) (meaning t m 2299) (meaning t m 2563) (meaning t m 2633) (meaning t m 3646) (meaning t m 4235) (meaning t m 4275) source

theorem rule17656 (p1994 p2027 p2427 p3578 p3880 p4112 p4129 p4391 : Prop) (h : (¬ p2427) ∨ (¬ p4391) ∨ (¬ p4112) ∨ p3578 ∨ p2027 ∨ (¬ p1994) ∨ (¬ p4129) ∨ (¬ p3880)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2427) ∨ (p3578) ∨ (¬ p3880) ∨ (¬ p4112) ∨ (¬ p4129) ∨ (¬ p4391) := by
  classical
  tauto

theorem initial17656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4391)) := by
  have source := ElevenTheory.theory6928 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 10)
  exact rule17656 (meaning t m 1994) (meaning t m 2027) (meaning t m 2427) (meaning t m 3578) (meaning t m 3880) (meaning t m 4112) (meaning t m 4129) (meaning t m 4391) source

theorem rule17657 (p2000 p2027 p2579 p2588 p2764 p4107 p4381 : Prop) (h : (¬ p4107) ∨ (¬ p2000) ∨ (¬ p2588) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p4381) ∨ p2764) : (¬ p2000) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (p2764) ∨ (¬ p4107) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial17657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory6929 t (m.theta 0 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17657 (meaning t m 2000) (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 2764) (meaning t m 4107) (meaning t m 4381) source

theorem rule17658 (p1994 p2027 p2192 p2210 p2630 p2699 p3758 p4392 : Prop) (h : (¬ p2210) ∨ (¬ p1994) ∨ p2699 ∨ (¬ p3758) ∨ (¬ p2192) ∨ (¬ p4392) ∨ p2027 ∨ (¬ p2630)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2630) ∨ (p2699) ∨ (¬ p3758) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial17658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory6930 t (m.theta 0 1) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 5 6)
  exact rule17658 (meaning t m 1994) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2630) (meaning t m 2699) (meaning t m 3758) (meaning t m 4392) source

theorem rule17663 (p1993 p2027 p2098 p2622 p3365 p3609 p4118 : Prop) (h : (¬ p3609) ∨ (¬ p1993) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p2098) ∨ (¬ p4118) ∨ p2622) : (¬ p1993) ∨ (p2027) ∨ (¬ p2098) ∨ (p2622) ∨ (¬ p3365) ∨ (¬ p3609) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial17663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory6935 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule17663 (meaning t m 1993) (meaning t m 2027) (meaning t m 2098) (meaning t m 2622) (meaning t m 3365) (meaning t m 3609) (meaning t m 4118) source

theorem rule17668 (p1978 p3646 p3818 p4518 : Prop) (h : (¬ p3646) ∨ (¬ p1978) ∨ p3818 ∨ p4518) : (¬ p1978) ∨ (¬ p3646) ∨ (p3818) ∨ (p4518) := by
  classical
  tauto

theorem initial17668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (¬ (meaning t m 3646)) ∨ (meaning t m 3818) ∨ (meaning t m 4518) := by
  have source := ElevenTheory.theory6940 t (m.theta 0 5) (m.theta 1 6) (m.theta 5 6)
  exact rule17668 (meaning t m 1978) (meaning t m 3646) (meaning t m 3818) (meaning t m 4518) source

theorem rule17671 (p1997 p2027 p2406 p2633 p3125 p3193 p3989 p4022 p4138 : Prop) (h : (¬ p4138) ∨ p2633 ∨ (¬ p2406) ∨ (¬ p3989) ∨ (¬ p3125) ∨ (¬ p1997) ∨ (¬ p4022) ∨ p2027 ∨ (¬ p3193)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2406) ∨ (p2633) ∨ (¬ p3125) ∨ (¬ p3193) ∨ (¬ p3989) ∨ (¬ p4022) ∨ (¬ p4138) := by
  classical
  tauto

theorem initial17671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4138)) := by
  have source := ElevenTheory.theory6943 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8)
  exact rule17671 (meaning t m 1997) (meaning t m 2027) (meaning t m 2406) (meaning t m 2633) (meaning t m 3125) (meaning t m 3193) (meaning t m 3989) (meaning t m 4022) (meaning t m 4138) source

theorem rule17672 (p2005 p2027 p2598 p2633 p3422 p3425 p3659 : Prop) (h : (¬ p3659) ∨ p2633 ∨ (¬ p2005) ∨ (¬ p3425) ∨ (¬ p2598) ∨ (¬ p3422) ∨ p2027) : (¬ p2005) ∨ (p2027) ∨ (¬ p2598) ∨ (p2633) ∨ (¬ p3422) ∨ (¬ p3425) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial17672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory6944 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 6) (m.theta 7 8)
  exact rule17672 (meaning t m 2005) (meaning t m 2027) (meaning t m 2598) (meaning t m 2633) (meaning t m 3422) (meaning t m 3425) (meaning t m 3659) source

theorem rule17673 (p1997 p2027 p2114 p2230 p3201 p3367 p3540 : Prop) (h : (¬ p3201) ∨ (¬ p3540) ∨ p2114 ∨ (¬ p3367) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2230) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial17673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory6945 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule17673 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2230) (meaning t m 3201) (meaning t m 3367) (meaning t m 3540) source

theorem rule17674 (p2005 p2027 p2622 p2774 p2819 p3365 p3956 : Prop) (h : p2622 ∨ (¬ p3365) ∨ (¬ p2005) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2819) ∨ (¬ p2774)) : (¬ p2005) ∨ (p2027) ∨ (p2622) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3365) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial17674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory6946 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 4 6) (m.theta 6 8)
  exact rule17674 (meaning t m 2005) (meaning t m 2027) (meaning t m 2622) (meaning t m 2774) (meaning t m 2819) (meaning t m 3365) (meaning t m 3956) source

theorem rule17675 (p1983 p2027 p2449 p2622 p3365 p3819 p4063 p4391 : Prop) (h : p2622 ∨ (¬ p2449) ∨ (¬ p3819) ∨ (¬ p1983) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4391) ∨ (¬ p4063)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2449) ∨ (p2622) ∨ (¬ p3365) ∨ (¬ p3819) ∨ (¬ p4063) ∨ (¬ p4391) := by
  classical
  tauto

theorem initial17675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4063)) ∨ (¬ (meaning t m 4391)) := by
  have source := ElevenTheory.theory6947 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 10) (m.theta 7 9)
  exact rule17675 (meaning t m 1983) (meaning t m 2027) (meaning t m 2449) (meaning t m 2622) (meaning t m 3365) (meaning t m 3819) (meaning t m 4063) (meaning t m 4391) source

theorem rule17679 (p1998 p2027 p2717 p2766 p3266 p3821 p3959 p4381 : Prop) (h : p2027 ∨ p2766 ∨ (¬ p1998) ∨ (¬ p2717) ∨ (¬ p3959) ∨ (¬ p3266) ∨ (¬ p4381) ∨ (¬ p3821)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2717) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3821) ∨ (¬ p3959) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial17679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory6951 t (m.theta 0 7) (m.theta 2 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule17679 (meaning t m 1998) (meaning t m 2027) (meaning t m 2717) (meaning t m 2766) (meaning t m 3266) (meaning t m 3821) (meaning t m 3959) (meaning t m 4381) source

theorem rule17682 (p1980 p2633 p3324 p4133 : Prop) (h : (¬ p3324) ∨ p2633 ∨ (¬ p1980) ∨ p4133) : (¬ p1980) ∨ (p2633) ∨ (¬ p3324) ∨ (p4133) := by
  classical
  tauto

theorem initial17682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3324)) ∨ (meaning t m 4133) := by
  have source := ElevenTheory.theory6954 t (m.theta 3 6) (m.theta 6 8) (m.theta 7 8)
  exact rule17682 (meaning t m 1980) (meaning t m 2633) (meaning t m 3324) (meaning t m 4133) source

theorem rule17686 (p2017 p2027 p2241 p2699 p2901 p2992 p4129 : Prop) (h : (¬ p2241) ∨ p2699 ∨ p2027 ∨ (¬ p2992) ∨ (¬ p2901) ∨ (¬ p2017) ∨ (¬ p4129)) : (¬ p2017) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4129) := by
  classical
  tauto

theorem initial17686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2017)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4129)) := by
  have source := ElevenTheory.theory6958 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 10)
  exact rule17686 (meaning t m 2017) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2901) (meaning t m 2992) (meaning t m 4129) source

theorem rule17687 (p1985 p2027 p2459 p2633 p2901 p3497 p3692 : Prop) (h : (¬ p3692) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p1985) ∨ p2633) : (¬ p1985) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial17687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory6959 t (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17687 (meaning t m 1985) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 2901) (meaning t m 3497) (meaning t m 3692) source

theorem rule17688 (p1975 p2027 p2202 p2563 p3156 p3737 p3955 p4153 p4328 p4329 p4441 : Prop) (h : p2027 ∨ (¬ p4441) ∨ (¬ p2563) ∨ p2202 ∨ (¬ p1975) ∨ (¬ p4329) ∨ (¬ p3955) ∨ (¬ p3156) ∨ (¬ p4153) ∨ (¬ p4328) ∨ (¬ p3737)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3156) ∨ (¬ p3737) ∨ (¬ p3955) ∨ (¬ p4153) ∨ (¬ p4328) ∨ (¬ p4329) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial17688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 4329)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory6960 t (m.theta 2 6) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 10) (m.theta 6 7) (m.theta 6 8)
  exact rule17688 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 3156) (meaning t m 3737) (meaning t m 3955) (meaning t m 4153) (meaning t m 4328) (meaning t m 4329) (meaning t m 4441) source

theorem rule17690 (p1978 p2027 p2427 p3556 p3880 p3982 p5568 : Prop) (h : p3982 ∨ (¬ p1978) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2427) ∨ (¬ p3880) ∨ (¬ p5568)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3880) ∨ (p3982) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial17690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3880)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory6962 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 10)
  exact rule17690 (meaning t m 1978) (meaning t m 2027) (meaning t m 2427) (meaning t m 3556) (meaning t m 3880) (meaning t m 3982) (meaning t m 5568) source

theorem rule17692 (p1994 p2027 p2630 p2946 p3292 p3871 p4315 : Prop) (h : p3871 ∨ (¬ p3292) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p2630) ∨ (¬ p4315)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2946) ∨ (¬ p3292) ∨ (p3871) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial17692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3292)) ∨ (meaning t m 3871) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory6964 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 9)
  exact rule17692 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2946) (meaning t m 3292) (meaning t m 3871) (meaning t m 4315) source

theorem rule17693 (p1998 p2027 p2114 p2264 p2707 p3434 p3947 : Prop) (h : (¬ p2707) ∨ (¬ p2264) ∨ (¬ p1998) ∨ (¬ p3434) ∨ p2027 ∨ p2114 ∨ (¬ p3947)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2264) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial17693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory6965 t (m.theta 1 2) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17693 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2264) (meaning t m 2707) (meaning t m 3434) (meaning t m 3947) source

theorem rule17695 (p2009 p2027 p2373 p3043 p3969 p4948 p5590 : Prop) (h : p3043 ∨ (¬ p2009) ∨ (¬ p4948) ∨ (¬ p5590) ∨ p2027 ∨ (¬ p2373) ∨ (¬ p3969)) : (¬ p2009) ∨ (p2027) ∨ (¬ p2373) ∨ (p3043) ∨ (¬ p3969) ∨ (¬ p4948) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial17695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2009)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory6967 t (m.theta 0 8) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 10)
  exact rule17695 (meaning t m 2009) (meaning t m 2027) (meaning t m 2373) (meaning t m 3043) (meaning t m 3969) (meaning t m 4948) (meaning t m 5590) source

theorem rule17696 (p1979 p2027 p2373 p3043 p3661 p3696 p3998 p4948 p5600 : Prop) (h : p3043 ∨ (¬ p5600) ∨ (¬ p4948) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p1979) ∨ (¬ p3696) ∨ (¬ p3998) ∨ (¬ p3661)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2373) ∨ (p3043) ∨ (¬ p3661) ∨ (¬ p3696) ∨ (¬ p3998) ∨ (¬ p4948) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial17696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory6968 t (m.theta 0 8) (m.theta 3 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 10)
  exact rule17696 (meaning t m 1979) (meaning t m 2027) (meaning t m 2373) (meaning t m 3043) (meaning t m 3661) (meaning t m 3696) (meaning t m 3998) (meaning t m 4948) (meaning t m 5600) source

theorem rule17697 (p2373 p2427 p3747 : Prop) (h : (¬ p2427) ∨ (¬ p3747) ∨ p2373) : (p2373) ∨ (¬ p2427) ∨ (¬ p3747) := by
  classical
  tauto

theorem initial17697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2373) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3747)) := by
  have source := ElevenTheory.theory6969 (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule17697 (meaning t m 2373) (meaning t m 2427) (meaning t m 3747) source

theorem rule17698 (p1990 p2027 p2192 p2459 p2633 p3645 p3692 p4120 : Prop) (h : (¬ p3645) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p4120) ∨ (¬ p1990) ∨ p2633 ∨ (¬ p3692) ∨ (¬ p2459)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial17698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory6970 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17698 (meaning t m 1990) (meaning t m 2027) (meaning t m 2192) (meaning t m 2459) (meaning t m 2633) (meaning t m 3645) (meaning t m 3692) (meaning t m 4120) source

theorem rule17699 (p2132 p3577 p3587 p3820 : Prop) (h : (¬ p2132) ∨ (¬ p3587) ∨ (¬ p3577) ∨ (¬ p3820)) : (¬ p2132) ∨ (¬ p3577) ∨ (¬ p3587) ∨ (¬ p3820) := by
  classical
  tauto

theorem initial17699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 3820)) := by
  have source := ElevenTheory.theory6971 (m.theta 0 2) (m.theta 0 7) (m.theta 2 5) (m.theta 2 7)
  exact rule17699 (meaning t m 2132) (meaning t m 3577) (meaning t m 3587) (meaning t m 3820) source

theorem rule17701 (p1994 p2027 p2169 p2274 p2313 p2386 p3574 p3989 : Prop) (h : (¬ p2313) ∨ (¬ p2386) ∨ (¬ p3989) ∨ (¬ p1994) ∨ (¬ p3574) ∨ p2027 ∨ p2169 ∨ (¬ p2274)) : (¬ p1994) ∨ (p2027) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p3574) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial17701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory6973 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule17701 (meaning t m 1994) (meaning t m 2027) (meaning t m 2169) (meaning t m 2274) (meaning t m 2313) (meaning t m 2386) (meaning t m 3574) (meaning t m 3989) source

theorem rule17702 (p2007 p2027 p2608 p2630 p2699 p2737 p3343 p4045 : Prop) (h : (¬ p3343) ∨ (¬ p2007) ∨ (¬ p4045) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p2630) ∨ p2699 ∨ p2027) : (¬ p2007) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p2630) ∨ (p2699) ∨ (¬ p2737) ∨ (¬ p3343) ∨ (¬ p4045) := by
  classical
  tauto

theorem initial17702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4045)) := by
  have source := ElevenTheory.theory6974 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9)
  exact rule17702 (meaning t m 2007) (meaning t m 2027) (meaning t m 2608) (meaning t m 2630) (meaning t m 2699) (meaning t m 2737) (meaning t m 3343) (meaning t m 4045) source

theorem rule17705 (p1975 p2027 p2553 p2611 p2630 p2696 p3016 : Prop) (h : p2611 ∨ (¬ p1975) ∨ (¬ p3016) ∨ (¬ p2630) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p2553)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (p2611) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial17705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory6977 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule17705 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2611) (meaning t m 2630) (meaning t m 2696) (meaning t m 3016) source

theorem rule17706 (p1985 p2027 p2611 p2774 p2901 p3914 p4153 p5717 : Prop) (h : (¬ p5717) ∨ p2611 ∨ (¬ p2774) ∨ (¬ p3914) ∨ p2027 ∨ (¬ p1985) ∨ (¬ p2901) ∨ (¬ p4153)) : (¬ p1985) ∨ (p2027) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p2901) ∨ (¬ p3914) ∨ (¬ p4153) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial17706 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory6978 t (m.theta 0 2) (m.theta 2 6) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 10)
  exact rule17706 (meaning t m 1985) (meaning t m 2027) (meaning t m 2611) (meaning t m 2774) (meaning t m 2901) (meaning t m 3914) (meaning t m 4153) (meaning t m 5717) source

theorem rule17708 (p1988 p2027 p2114 p2737 p3005 p3256 p3266 : Prop) (h : (¬ p1988) ∨ p2027 ∨ p2114 ∨ (¬ p2737) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3005)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial17708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory6980 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17708 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 3005) (meaning t m 3256) (meaning t m 3266) source

theorem rule17709 (p2024 p2027 p2765 p2982 p3680 p4110 p5284 : Prop) (h : (¬ p5284) ∨ p2027 ∨ (¬ p2982) ∨ (¬ p2024) ∨ p2765 ∨ (¬ p4110) ∨ (¬ p3680)) : (¬ p2024) ∨ (p2027) ∨ (p2765) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4110) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial17709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2024)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory6981 t (m.theta 3 9) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule17709 (meaning t m 2024) (meaning t m 2027) (meaning t m 2765) (meaning t m 2982) (meaning t m 3680) (meaning t m 4110) (meaning t m 5284) source

theorem rule17710 (p1975 p2027 p2295 p2611 p2797 p3286 p4035 p4117 : Prop) (h : p2027 ∨ p2611 ∨ (¬ p2797) ∨ (¬ p4117) ∨ (¬ p4035) ∨ (¬ p3286) ∨ (¬ p1975) ∨ (¬ p2295)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2611) ∨ (¬ p2797) ∨ (¬ p3286) ∨ (¬ p4035) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial17710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory6982 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 7)
  exact rule17710 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2611) (meaning t m 2797) (meaning t m 3286) (meaning t m 4035) (meaning t m 4117) source

theorem rule17714 (p1984 p2027 p2202 p2247 p2563 p3952 p4111 p4700 : Prop) (h : p2202 ∨ (¬ p1984) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p2247) ∨ (¬ p4111) ∨ (¬ p4700)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2247) ∨ (¬ p2563) ∨ (¬ p3952) ∨ (¬ p4111) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial17714 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory6986 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule17714 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2247) (meaning t m 2563) (meaning t m 3952) (meaning t m 4111) (meaning t m 4700) source

theorem rule17715 (p1988 p2027 p2114 p2137 p2761 p2839 p3051 p3246 : Prop) (h : p2114 ∨ (¬ p2137) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p2839) ∨ (¬ p3246) ∨ (¬ p1988) ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2761) ∨ (¬ p2839) ∨ (¬ p3051) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial17715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory6987 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17715 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2761) (meaning t m 2839) (meaning t m 3051) (meaning t m 3246) source

theorem rule17718 (p1975 p2027 p2114 p2299 p2911 p3367 p3389 p3759 : Prop) (h : (¬ p3367) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p3759) ∨ p2114 ∨ (¬ p2911) ∨ (¬ p1975) ∨ (¬ p2299)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory6990 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17718 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2299) (meaning t m 2911) (meaning t m 3367) (meaning t m 3389) (meaning t m 3759) source

theorem rule17720 (p1985 p2027 p2191 p2765 p2891 p3156 p3952 : Prop) (h : (¬ p2891) ∨ (¬ p1985) ∨ p2027 ∨ (¬ p3952) ∨ p2765 ∨ (¬ p3156) ∨ (¬ p2191)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2191) ∨ (p2765) ∨ (¬ p2891) ∨ (¬ p3156) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial17720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory6992 t (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule17720 (meaning t m 1985) (meaning t m 2027) (meaning t m 2191) (meaning t m 2765) (meaning t m 2891) (meaning t m 3156) (meaning t m 3952) source

theorem rule17721 (p1998 p2027 p2114 p2470 p2528 p3367 p3759 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p2528) ∨ p2114 ∨ (¬ p2470) ∨ (¬ p3759)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial17721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory6993 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17721 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2470) (meaning t m 2528) (meaning t m 3367) (meaning t m 3759) (meaning t m 4348) source

theorem rule17722 (p1988 p2027 p2114 p2307 p2396 p2761 p2779 p2829 : Prop) (h : p2027 ∨ p2114 ∨ (¬ p2761) ∨ (¬ p2829) ∨ (¬ p2779) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2779) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial17722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory6994 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17722 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2307) (meaning t m 2396) (meaning t m 2761) (meaning t m 2779) (meaning t m 2829) source

theorem rule17724 (p1984 p2247 p2622 p2745 : Prop) (h : (¬ p1984) ∨ (¬ p2247) ∨ p2622 ∨ p2745) : (¬ p1984) ∨ (¬ p2247) ∨ (p2622) ∨ (p2745) := by
  classical
  tauto

theorem initial17724 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2622) ∨ (meaning t m 2745) := by
  have source := ElevenTheory.theory6996 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3)
  exact rule17724 (meaning t m 1984) (meaning t m 2247) (meaning t m 2622) (meaning t m 2745) source

theorem rule17725 (p1975 p2027 p2299 p2470 p2542 p2545 p2589 p4404 : Prop) (h : (¬ p2299) ∨ (¬ p4404) ∨ (¬ p2589) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p1975) ∨ p2545 ∨ (¬ p2470)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2470) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2589) ∨ (¬ p4404) := by
  classical
  tauto

theorem initial17725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 4404)) := by
  have source := ElevenTheory.theory6997 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule17725 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2470) (meaning t m 2542) (meaning t m 2545) (meaning t m 2589) (meaning t m 4404) source

theorem rule17726 (p1985 p2027 p2114 p2911 p3367 p3389 p3570 p3759 : Prop) (h : (¬ p3367) ∨ (¬ p1985) ∨ p2027 ∨ (¬ p2911) ∨ p2114 ∨ (¬ p3759) ∨ (¬ p3389) ∨ (¬ p3570)) : (¬ p1985) ∨ (p2027) ∨ (p2114) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3570) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory6998 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule17726 (meaning t m 1985) (meaning t m 2027) (meaning t m 2114) (meaning t m 2911) (meaning t m 3367) (meaning t m 3389) (meaning t m 3570) (meaning t m 3759) source

theorem rule17729 (p1984 p2027 p2169 p2247 p2363 p4118 p4360 : Prop) (h : (¬ p2247) ∨ (¬ p1984) ∨ (¬ p4360) ∨ p2169 ∨ (¬ p4118) ∨ p2027 ∨ (¬ p2363)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p4118) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial17729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory7001 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule17729 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 2247) (meaning t m 2363) (meaning t m 4118) (meaning t m 4360) source

theorem rule17730 (p1987 p2027 p2997 p3189 p3568 p3877 p4154 : Prop) (h : p2997 ∨ p2027 ∨ (¬ p1987) ∨ (¬ p3568) ∨ (¬ p3877) ∨ (¬ p3189) ∨ (¬ p4154)) : (¬ p1987) ∨ (p2027) ∨ (p2997) ∨ (¬ p3189) ∨ (¬ p3568) ∨ (¬ p3877) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial17730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory7002 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7)
  exact rule17730 (meaning t m 1987) (meaning t m 2027) (meaning t m 2997) (meaning t m 3189) (meaning t m 3568) (meaning t m 3877) (meaning t m 4154) source

theorem rule17731 (p1981 p2027 p2187 p2409 p2493 p3564 p3946 p4356 : Prop) (h : (¬ p2493) ∨ p2027 ∨ (¬ p3946) ∨ (¬ p3564) ∨ p2409 ∨ (¬ p4356) ∨ (¬ p2187) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (p2409) ∨ (¬ p2493) ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial17731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory7003 t (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule17731 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2409) (meaning t m 2493) (meaning t m 3564) (meaning t m 3946) (meaning t m 4356) source

theorem rule17732 (p1991 p2027 p2355 p2996 p3073 p3172 p3859 p4118 : Prop) (h : p2027 ∨ p2355 ∨ (¬ p1991) ∨ (¬ p4118) ∨ (¬ p2996) ∨ (¬ p3859) ∨ (¬ p3172) ∨ (¬ p3073)) : (¬ p1991) ∨ (p2027) ∨ (p2355) ∨ (¬ p2996) ∨ (¬ p3073) ∨ (¬ p3172) ∨ (¬ p3859) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial17732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory7004 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 8) (m.theta 3 7) (m.theta 3 8) (m.theta 8 9)
  exact rule17732 (meaning t m 1991) (meaning t m 2027) (meaning t m 2355) (meaning t m 2996) (meaning t m 3073) (meaning t m 3172) (meaning t m 3859) (meaning t m 4118) source

theorem rule17733 (p2005 p2027 p2388 p2573 p3027 p3540 p3579 p3662 : Prop) (h : p2027 ∨ (¬ p2005) ∨ (¬ p2573) ∨ (¬ p3027) ∨ p2388 ∨ (¬ p3579) ∨ (¬ p3662) ∨ (¬ p3540)) : (¬ p2005) ∨ (p2027) ∨ (p2388) ∨ (¬ p2573) ∨ (¬ p3027) ∨ (¬ p3540) ∨ (¬ p3579) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial17733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory7005 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7)
  exact rule17733 (meaning t m 2005) (meaning t m 2027) (meaning t m 2388) (meaning t m 2573) (meaning t m 3027) (meaning t m 3540) (meaning t m 3579) (meaning t m 3662) source

theorem rule17734 (p2005 p2027 p2383 p2542 p2545 p2584 p2589 p3956 : Prop) (h : p2027 ∨ (¬ p2005) ∨ p2545 ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2584) ∨ (¬ p2383) ∨ (¬ p3956)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2383) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2584) ∨ (¬ p2589) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial17734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory7006 t (m.theta 0 4) (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule17734 (meaning t m 2005) (meaning t m 2027) (meaning t m 2383) (meaning t m 2542) (meaning t m 2545) (meaning t m 2584) (meaning t m 2589) (meaning t m 3956) source

theorem rule17735 (p1997 p2027 p2284 p2388 p3051 p3646 p4235 : Prop) (h : (¬ p2284) ∨ p2388 ∨ (¬ p3646) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial17735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7007 t (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule17735 (meaning t m 1997) (meaning t m 2027) (meaning t m 2284) (meaning t m 2388) (meaning t m 3051) (meaning t m 3646) (meaning t m 4235) source

theorem rule17739 (p1975 p2027 p2274 p2406 p2409 p2962 p3654 p3744 p4109 : Prop) (h : (¬ p2274) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p2406) ∨ (¬ p3654) ∨ (¬ p4109) ∨ p2409 ∨ (¬ p2962)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p4109) := by
  classical
  tauto

theorem initial17739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4109)) := by
  have source := ElevenTheory.theory7011 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule17739 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2406) (meaning t m 2409) (meaning t m 2962) (meaning t m 3654) (meaning t m 3744) (meaning t m 4109) source

theorem rule17740 (p2005 p2027 p2295 p2388 p2588 p2641 p3662 : Prop) (h : (¬ p2588) ∨ (¬ p2295) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p2005) ∨ (¬ p2641) ∨ p2388) : (¬ p2005) ∨ (p2027) ∨ (¬ p2295) ∨ (p2388) ∨ (¬ p2588) ∨ (¬ p2641) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial17740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory7012 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule17740 (meaning t m 2005) (meaning t m 2027) (meaning t m 2295) (meaning t m 2388) (meaning t m 2588) (meaning t m 2641) (meaning t m 3662) source

theorem rule17749 (p3055 p4419 p4730 : Prop) (h : p4730 ∨ (¬ p3055) ∨ (¬ p4419)) : (¬ p3055) ∨ (¬ p4419) ∨ (p4730) := by
  classical
  tauto

theorem initial17749 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4419)) ∨ (meaning t m 4730) := by
  have source := ElevenTheory.theory7021 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4)
  exact rule17749 (meaning t m 3055) (meaning t m 4419) (meaning t m 4730) source

theorem rule17752 (p1987 p2027 p2299 p2313 p2667 p2766 p4195 p4348 : Prop) (h : p2027 ∨ p2766 ∨ (¬ p2667) ∨ (¬ p2313) ∨ (¬ p4348) ∨ (¬ p1987) ∨ (¬ p2299) ∨ (¬ p4195)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (p2766) ∨ (¬ p4195) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial17752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory7024 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule17752 (meaning t m 1987) (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2667) (meaning t m 2766) (meaning t m 4195) (meaning t m 4348) source

theorem rule17753 (p2010 p2027 p2331 p2545 p2657 p3201 p3584 p3984 : Prop) (h : (¬ p2657) ∨ p2545 ∨ p2027 ∨ (¬ p3584) ∨ (¬ p2331) ∨ (¬ p2010) ∨ (¬ p3201) ∨ (¬ p3984)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2331) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p3201) ∨ (¬ p3584) ∨ (¬ p3984) := by
  classical
  tauto

theorem initial17753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3984)) := by
  have source := ElevenTheory.theory7025 t (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7)
  exact rule17753 (meaning t m 2010) (meaning t m 2027) (meaning t m 2331) (meaning t m 2545) (meaning t m 2657) (meaning t m 3201) (meaning t m 3584) (meaning t m 3984) source

theorem rule17755 (p1985 p2027 p2542 p2545 p2563 p2870 p3758 : Prop) (h : (¬ p1985) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p2563) ∨ p2545 ∨ (¬ p2870) ∨ (¬ p2542)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2563) ∨ (¬ p2870) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial17755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory7027 t (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule17755 (meaning t m 1985) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2563) (meaning t m 2870) (meaning t m 3758) source

theorem rule17756 (p1985 p2027 p2406 p2409 p2563 p2870 p3758 : Prop) (h : (¬ p1985) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p2563) ∨ p2409 ∨ (¬ p2870) ∨ (¬ p2406)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2563) ∨ (¬ p2870) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial17756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory7028 t (m.theta 1 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule17756 (meaning t m 1985) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2563) (meaning t m 2870) (meaning t m 3758) source

theorem rule17757 (p1987 p2027 p2406 p2409 p2696 p3055 p3684 : Prop) (h : p2409 ∨ p2027 ∨ (¬ p2406) ∨ (¬ p3055) ∨ (¬ p2696) ∨ (¬ p1987) ∨ (¬ p3684)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial17757 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory7029 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5)
  exact rule17757 (meaning t m 1987) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2696) (meaning t m 3055) (meaning t m 3684) source

theorem rule17761 (p1984 p2027 p2247 p2766 p2996 p3553 p4348 : Prop) (h : (¬ p3553) ∨ (¬ p1984) ∨ p2766 ∨ (¬ p4348) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2996)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2766) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial17761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory7033 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule17761 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2766) (meaning t m 2996) (meaning t m 3553) (meaning t m 4348) source

theorem rule17762 (p1985 p2027 p2114 p2264 p2655 p2807 p3367 p3570 p3759 : Prop) (h : p2114 ∨ (¬ p3759) ∨ p2027 ∨ (¬ p2655) ∨ (¬ p3367) ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p1985) ∨ (¬ p3570)) : (¬ p1985) ∨ (p2027) ∨ (p2114) ∨ (¬ p2264) ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p3367) ∨ (¬ p3570) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory7034 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule17762 (meaning t m 1985) (meaning t m 2027) (meaning t m 2114) (meaning t m 2264) (meaning t m 2655) (meaning t m 2807) (meaning t m 3367) (meaning t m 3570) (meaning t m 3759) source

theorem rule17763 (p1997 p2027 p2187 p2387 p2765 p3051 p4198 p4235 : Prop) (h : (¬ p1997) ∨ p2765 ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p4198) ∨ (¬ p2387) ∨ (¬ p2187) ∨ p2027) : (¬ p1997) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (p2765) ∨ (¬ p3051) ∨ (¬ p4198) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial17763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7035 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule17763 (meaning t m 1997) (meaning t m 2027) (meaning t m 2187) (meaning t m 2387) (meaning t m 2765) (meaning t m 3051) (meaning t m 4198) (meaning t m 4235) source

theorem rule17765 (p2022 p2027 p2264 p2545 p3027 p3551 p4111 : Prop) (h : (¬ p3551) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p2022) ∨ p2545) : (¬ p2022) ∨ (p2027) ∨ (¬ p2264) ∨ (p2545) ∨ (¬ p3027) ∨ (¬ p3551) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial17765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2022)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory7037 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule17765 (meaning t m 2022) (meaning t m 2027) (meaning t m 2264) (meaning t m 2545) (meaning t m 3027) (meaning t m 3551) (meaning t m 4111) source

theorem rule17766 (p1982 p2027 p2114 p2761 p3367 p3516 p3759 p4444 p5201 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p5201) ∨ p2114 ∨ (¬ p3516) ∨ (¬ p2761) ∨ (¬ p4444)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2761) ∨ (¬ p3367) ∨ (¬ p3516) ∨ (¬ p3759) ∨ (¬ p4444) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial17766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory7038 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 2 4) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule17766 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2761) (meaning t m 3367) (meaning t m 3516) (meaning t m 3759) (meaning t m 4444) (meaning t m 5201) source

theorem rule17768 (p1998 p2027 p2545 p2881 p2901 p2992 p4111 : Prop) (h : (¬ p1998) ∨ (¬ p4111) ∨ p2545 ∨ p2027 ∨ (¬ p2881) ∨ (¬ p2992) ∨ (¬ p2901)) : (¬ p1998) ∨ (p2027) ∨ (p2545) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial17768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory7040 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule17768 (meaning t m 1998) (meaning t m 2027) (meaning t m 2545) (meaning t m 2881) (meaning t m 2901) (meaning t m 2992) (meaning t m 4111) source

theorem rule17769 (p1980 p2027 p2331 p2545 p2810 p3005 p3172 : Prop) (h : (¬ p1980) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2810) ∨ (¬ p3172) ∨ (¬ p3005) ∨ p2545) : (¬ p1980) ∨ (p2027) ∨ (¬ p2331) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3172) := by
  classical
  tauto

theorem initial17769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3172)) := by
  have source := ElevenTheory.theory7041 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8)
  exact rule17769 (meaning t m 1980) (meaning t m 2027) (meaning t m 2331) (meaning t m 2545) (meaning t m 2810) (meaning t m 3005) (meaning t m 3172) source

theorem rule17773 (p1990 p2027 p2114 p2295 p2331 p2737 p2811 p3097 : Prop) (h : (¬ p2737) ∨ p2027 ∨ p2114 ∨ (¬ p2811) ∨ (¬ p3097) ∨ (¬ p1990) ∨ (¬ p2295) ∨ (¬ p2331)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial17773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory7045 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule17773 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2295) (meaning t m 2331) (meaning t m 2737) (meaning t m 2811) (meaning t m 3097) source

theorem rule17774 (p1982 p2027 p2114 p2230 p2373 p3146 p3367 p3759 : Prop) (h : p2114 ∨ (¬ p1982) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p3367) ∨ (¬ p2230) ∨ (¬ p3759) ∨ (¬ p2373)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory7046 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule17774 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2230) (meaning t m 2373) (meaning t m 3146) (meaning t m 3367) (meaning t m 3759) source

theorem rule17775 (p1990 p2027 p2230 p2409 p2476 p2518 p2563 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p1990) ∨ (¬ p2476) ∨ (¬ p2518) ∨ p2409) : (¬ p1990) ∨ (p2027) ∨ (¬ p2230) ∨ (p2409) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2563) := by
  classical
  tauto

theorem initial17775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2563)) := by
  have source := ElevenTheory.theory7047 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule17775 (meaning t m 1990) (meaning t m 2027) (meaning t m 2230) (meaning t m 2409) (meaning t m 2476) (meaning t m 2518) (meaning t m 2563) source

theorem rule17776 (p1975 p2027 p2114 p2417 p3367 p3389 p3759 p4107 : Prop) (h : (¬ p2417) ∨ (¬ p3759) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p3389) ∨ p2114 ∨ (¬ p1975) ∨ (¬ p4107)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2417) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial17776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory7048 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule17776 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2417) (meaning t m 3367) (meaning t m 3389) (meaning t m 3759) (meaning t m 4107) source

theorem rule17777 (p1985 p2027 p2427 p2459 p2633 p3497 p3692 p4241 : Prop) (h : (¬ p3497) ∨ p2027 ∨ (¬ p1985) ∨ (¬ p4241) ∨ (¬ p2427) ∨ (¬ p3692) ∨ p2633 ∨ (¬ p2459)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial17777 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory7049 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17777 (meaning t m 1985) (meaning t m 2027) (meaning t m 2427) (meaning t m 2459) (meaning t m 2633) (meaning t m 3497) (meaning t m 3692) (meaning t m 4241) source

theorem rule17778 (p1990 p2027 p2563 p3043 p3051 p4032 p4235 : Prop) (h : (¬ p4235) ∨ p2027 ∨ (¬ p3051) ∨ p3043 ∨ (¬ p2563) ∨ (¬ p4032) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p3043) ∨ (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial17778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7050 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule17778 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 3043) (meaning t m 3051) (meaning t m 4032) (meaning t m 4235) source

theorem rule17779 (p1976 p2027 p2633 p3246 p3425 p3570 p4324 : Prop) (h : (¬ p1976) ∨ (¬ p4324) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p3246) ∨ p2633 ∨ (¬ p3570)) : (¬ p1976) ∨ (p2027) ∨ (p2633) ∨ (¬ p3246) ∨ (¬ p3425) ∨ (¬ p3570) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial17779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory7051 t (m.theta 0 2) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17779 (meaning t m 1976) (meaning t m 2027) (meaning t m 2633) (meaning t m 3246) (meaning t m 3425) (meaning t m 3570) (meaning t m 4324) source

theorem rule17780 (p1998 p2027 p2114 p2230 p2427 p2881 p3367 p3759 : Prop) (h : p2114 ∨ p2027 ∨ (¬ p3367) ∨ (¬ p2427) ∨ (¬ p3759) ∨ (¬ p2230) ∨ (¬ p2881) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory7052 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule17780 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2230) (meaning t m 2427) (meaning t m 2881) (meaning t m 3367) (meaning t m 3759) source

theorem rule17781 (p2011 p2027 p2114 p2137 p2839 p2982 p3051 p4235 : Prop) (h : p2027 ∨ p2114 ∨ (¬ p2982) ∨ (¬ p2011) ∨ (¬ p2839) ∨ (¬ p2137) ∨ (¬ p3051) ∨ (¬ p4235)) : (¬ p2011) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2839) ∨ (¬ p2982) ∨ (¬ p3051) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial17781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory7053 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9)
  exact rule17781 (meaning t m 2011) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2839) (meaning t m 2982) (meaning t m 3051) (meaning t m 4235) source

theorem rule17783 (p2006 p2027 p2545 p2657 p2946 p3156 p3694 : Prop) (h : p2545 ∨ (¬ p2006) ∨ (¬ p2657) ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p3694) ∨ p2027) : (¬ p2006) ∨ (p2027) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial17783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory7055 t (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule17783 (meaning t m 2006) (meaning t m 2027) (meaning t m 2545) (meaning t m 2657) (meaning t m 2946) (meaning t m 3156) (meaning t m 3694) source

theorem rule17784 (p1998 p2027 p2427 p2545 p2657 p2881 p2946 p4241 : Prop) (h : p2027 ∨ (¬ p1998) ∨ (¬ p2657) ∨ p2545 ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p4241)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2427) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial17784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory7056 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule17784 (meaning t m 1998) (meaning t m 2027) (meaning t m 2427) (meaning t m 2545) (meaning t m 2657) (meaning t m 2881) (meaning t m 2946) (meaning t m 4241) source

theorem rule17785 (p1980 p2027 p2331 p2545 p3172 p3189 p4111 : Prop) (h : p2027 ∨ p2545 ∨ (¬ p1980) ∨ (¬ p2331) ∨ (¬ p4111) ∨ (¬ p3189) ∨ (¬ p3172)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2331) ∨ (p2545) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial17785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory7057 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8)
  exact rule17785 (meaning t m 1980) (meaning t m 2027) (meaning t m 2331) (meaning t m 2545) (meaning t m 3172) (meaning t m 3189) (meaning t m 4111) source

theorem rule17786 (p1984 p2027 p2743 p2766 p3877 p3954 p4118 : Prop) (h : (¬ p1984) ∨ (¬ p3877) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p4118) ∨ p2766 ∨ (¬ p3954)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2743) ∨ (p2766) ∨ (¬ p3877) ∨ (¬ p3954) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial17786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory7058 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 8 9)
  exact rule17786 (meaning t m 1984) (meaning t m 2027) (meaning t m 2743) (meaning t m 2766) (meaning t m 3877) (meaning t m 3954) (meaning t m 4118) source

theorem rule17787 (p1992 p2027 p2247 p2608 p2766 p4118 p4360 : Prop) (h : p2027 ∨ (¬ p1992) ∨ (¬ p4118) ∨ p2766 ∨ (¬ p4360) ∨ (¬ p2608) ∨ (¬ p2247)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2608) ∨ (p2766) ∨ (¬ p4118) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial17787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory7059 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 8) (m.theta 8 9)
  exact rule17787 (meaning t m 1992) (meaning t m 2027) (meaning t m 2247) (meaning t m 2608) (meaning t m 2766) (meaning t m 4118) (meaning t m 4360) source

theorem rule17788 (p1980 p2027 p2169 p2331 p2363 p3172 p4118 : Prop) (h : p2027 ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p1980) ∨ (¬ p2331) ∨ (¬ p2363) ∨ p2169) : (¬ p1980) ∨ (p2027) ∨ (p2169) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p3172) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial17788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory7060 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule17788 (meaning t m 1980) (meaning t m 2027) (meaning t m 2169) (meaning t m 2331) (meaning t m 2363) (meaning t m 3172) (meaning t m 4118) source

theorem rule17789 (p1998 p2027 p2114 p2737 p2811 p2881 p2901 p2946 : Prop) (h : p2114 ∨ (¬ p2737) ∨ p2027 ∨ (¬ p2811) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p2881) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) := by
  classical
  tauto

theorem initial17789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) := by
  have source := ElevenTheory.theory7061 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule17789 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 2811) (meaning t m 2881) (meaning t m 2901) (meaning t m 2946) source

theorem rule17793 (p1983 p2027 p2114 p2341 p2417 p3367 p3644 p3759 p5201 : Prop) (h : p2027 ∨ (¬ p2341) ∨ (¬ p5201) ∨ (¬ p3367) ∨ (¬ p3759) ∨ p2114 ∨ (¬ p3644) ∨ (¬ p1983) ∨ (¬ p2417)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2341) ∨ (¬ p2417) ∨ (¬ p3367) ∨ (¬ p3644) ∨ (¬ p3759) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial17793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory7065 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17793 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2341) (meaning t m 2417) (meaning t m 3367) (meaning t m 3644) (meaning t m 3759) (meaning t m 5201) source

theorem rule17794 (p1982 p2027 p2114 p2352 p2363 p2573 p3367 p3759 : Prop) (h : (¬ p2573) ∨ (¬ p1982) ∨ (¬ p3759) ∨ (¬ p3367) ∨ p2114 ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2363)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory7066 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule17794 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 3367) (meaning t m 3759) source

theorem rule17795 (p1984 p2027 p2169 p2274 p3549 p3591 p3989 : Prop) (h : p2169 ∨ (¬ p3989) ∨ (¬ p3591) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3549) ∨ (¬ p2274)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial17795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory7067 t (m.theta 0 1) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule17795 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 2274) (meaning t m 3549) (meaning t m 3591) (meaning t m 3989) source

theorem rule17796 (p2098 p3425 p3685 : Prop) (h : (¬ p3685) ∨ (¬ p3425) ∨ (¬ p2098)) : (¬ p2098) ∨ (¬ p3425) ∨ (¬ p3685) := by
  classical
  tauto

theorem initial17796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3685)) := by
  have source := ElevenTheory.theory7068 (m.theta 0 2) (m.theta 2 7) (m.theta 2 8)
  exact rule17796 (meaning t m 2098) (meaning t m 3425) (meaning t m 3685) source

theorem rule17797 (p2331 p3166 p4341 : Prop) (h : (¬ p2331) ∨ (¬ p4341) ∨ p3166) : (¬ p2331) ∨ (p3166) ∨ (¬ p4341) := by
  classical
  tauto

theorem initial17797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (meaning t m 3166) ∨ (¬ (meaning t m 4341)) := by
  have source := ElevenTheory.theory7069 (m.theta 0 3) (m.theta 3 6) (m.theta 3 8)
  exact rule17797 (meaning t m 2331) (meaning t m 3166) (meaning t m 4341) source

theorem rule17798 (p1981 p2027 p2114 p2470 p2528 p3367 p3759 p4347 : Prop) (h : p2114 ∨ (¬ p3759) ∨ (¬ p2470) ∨ (¬ p1981) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p3367) ∨ (¬ p4347)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial17798 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory7070 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule17798 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2470) (meaning t m 2528) (meaning t m 3367) (meaning t m 3759) (meaning t m 4347) source

theorem rule17799 (p1976 p2027 p2545 p2641 p3365 p4111 p4195 : Prop) (h : (¬ p2641) ∨ (¬ p4111) ∨ p2545 ∨ (¬ p1976) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p4195)) : (¬ p1976) ∨ (p2027) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p3365) ∨ (¬ p4111) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial17799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory7071 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule17799 (meaning t m 1976) (meaning t m 2027) (meaning t m 2545) (meaning t m 2641) (meaning t m 3365) (meaning t m 4111) (meaning t m 4195) source

theorem rule17800 (p1984 p2027 p2169 p2295 p3324 p3549 p3591 : Prop) (h : p2027 ∨ (¬ p1984) ∨ (¬ p3591) ∨ p2169 ∨ (¬ p2295) ∨ (¬ p3549) ∨ (¬ p3324)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p2295) ∨ (¬ p3324) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial17800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory7072 t (m.theta 0 1) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule17800 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 2295) (meaning t m 3324) (meaning t m 3549) (meaning t m 3591) source

theorem rule17801 (p1983 p2027 p2114 p2396 p2553 p2573 p3367 p3759 : Prop) (h : (¬ p2553) ∨ (¬ p3367) ∨ (¬ p1983) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2573) ∨ (¬ p3759) ∨ p2114) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory7073 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule17801 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 3367) (meaning t m 3759) source

theorem rule17802 (p1976 p2027 p2138 p2764 p3692 p3694 p4444 : Prop) (h : (¬ p2138) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p3694) ∨ (¬ p3692) ∨ p2764) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (p2764) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory7074 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17802 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2764) (meaning t m 3692) (meaning t m 3694) (meaning t m 4444) source

theorem rule17803 (p1998 p2027 p2766 p2911 p3266 p4278 p4381 : Prop) (h : (¬ p1998) ∨ (¬ p4278) ∨ (¬ p4381) ∨ p2027 ∨ p2766 ∨ (¬ p2911) ∨ (¬ p3266)) : (¬ p1998) ∨ (p2027) ∨ (p2766) ∨ (¬ p2911) ∨ (¬ p3266) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial17803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory7075 t (m.theta 4 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule17803 (meaning t m 1998) (meaning t m 2027) (meaning t m 2766) (meaning t m 2911) (meaning t m 3266) (meaning t m 4278) (meaning t m 4381) source

theorem rule17804 (p1984 p2027 p2545 p2743 p2780 p2810 p2829 p3873 : Prop) (h : (¬ p1984) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p2810) ∨ p2545 ∨ (¬ p3873) ∨ (¬ p2829) ∨ (¬ p2780)) : (¬ p1984) ∨ (p2027) ∨ (p2545) ∨ (¬ p2743) ∨ (¬ p2780) ∨ (¬ p2810) ∨ (¬ p2829) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial17804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory7076 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4)
  exact rule17804 (meaning t m 1984) (meaning t m 2027) (meaning t m 2545) (meaning t m 2743) (meaning t m 2780) (meaning t m 2810) (meaning t m 2829) (meaning t m 3873) source

theorem rule17805 (p1998 p2027 p2114 p2177 p2553 p2573 p3367 p3759 : Prop) (h : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p1998) ∨ (¬ p3759) ∨ (¬ p3367) ∨ p2114 ∨ p2027 ∨ (¬ p2573)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory7077 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule17805 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2177) (meaning t m 2553) (meaning t m 2573) (meaning t m 3367) (meaning t m 3759) source

theorem rule17806 (p1998 p2027 p2114 p2177 p2553 p3367 p3422 : Prop) (h : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p1998) ∨ p2114 ∨ (¬ p3367) ∨ p2027 ∨ (¬ p3422)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3367) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial17806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory7078 t (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule17806 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2177) (meaning t m 2553) (meaning t m 3367) (meaning t m 3422) source

theorem rule17810 (p2156 p3051 p4204 : Prop) (h : (¬ p4204) ∨ (¬ p3051) ∨ p2156) : (p2156) ∨ (¬ p3051) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial17810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2156) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory7082 (m.theta 0 5) (m.theta 5 6) (m.theta 5 7)
  exact rule17810 (meaning t m 2156) (meaning t m 3051) (meaning t m 4204) source

theorem rule17811 (p1984 p2027 p2459 p2633 p3591 p3923 p4347 : Prop) (h : (¬ p3591) ∨ p2633 ∨ p2027 ∨ (¬ p3923) ∨ (¬ p1984) ∨ (¬ p2459) ∨ (¬ p4347)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial17811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory7083 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule17811 (meaning t m 1984) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 3591) (meaning t m 3923) (meaning t m 4347) source

theorem rule17812 (p1985 p2027 p2264 p2355 p3434 p3659 p3690 : Prop) (h : p2355 ∨ (¬ p3434) ∨ (¬ p1985) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p3659) ∨ (¬ p2264)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2264) ∨ (p2355) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial17812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory7084 t (m.theta 2 7) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17812 (meaning t m 1985) (meaning t m 2027) (meaning t m 2264) (meaning t m 2355) (meaning t m 3434) (meaning t m 3659) (meaning t m 3690) source

theorem rule17813 (p1997 p2027 p2997 p3063 p3324 p3549 p3986 p4110 : Prop) (h : p2027 ∨ (¬ p3549) ∨ p2997 ∨ (¬ p4110) ∨ (¬ p3324) ∨ (¬ p3063) ∨ (¬ p3986) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (p2997) ∨ (¬ p3063) ∨ (¬ p3324) ∨ (¬ p3549) ∨ (¬ p3986) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial17813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory7085 t (m.theta 1 6) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule17813 (meaning t m 1997) (meaning t m 2027) (meaning t m 2997) (meaning t m 3063) (meaning t m 3324) (meaning t m 3549) (meaning t m 3986) (meaning t m 4110) source

theorem rule17814 (p1982 p2027 p2470 p2528 p2542 p2545 p3238 p3519 : Prop) (h : (¬ p3519) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p3238) ∨ (¬ p2542) ∨ p2545 ∨ (¬ p2528)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p3238) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial17814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory7086 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule17814 (meaning t m 1982) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2542) (meaning t m 2545) (meaning t m 3238) (meaning t m 3519) source

theorem rule17815 (p1984 p2027 p2122 p2169 p3549 p3591 p4358 : Prop) (h : (¬ p2122) ∨ (¬ p3549) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p1984) ∨ p2169 ∨ (¬ p4358)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2122) ∨ (p2169) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial17815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory7087 t (m.theta 0 1) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule17815 (meaning t m 1984) (meaning t m 2027) (meaning t m 2122) (meaning t m 2169) (meaning t m 3549) (meaning t m 3591) (meaning t m 4358) source

theorem rule17817 (p1990 p2027 p2114 p2132 p2860 p3055 p3367 : Prop) (h : (¬ p1990) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p2132) ∨ p2114 ∨ (¬ p2860)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3055) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial17817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory7089 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6)
  exact rule17817 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2132) (meaning t m 2860) (meaning t m 3055) (meaning t m 3367) source

theorem rule17820 (p1982 p2027 p2098 p2114 p2528 p3055 p3367 p5373 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p3367) ∨ (¬ p3055) ∨ (¬ p5373) ∨ p2114 ∨ (¬ p2528) ∨ (¬ p2098)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2098) ∨ (p2114) ∨ (¬ p2528) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial17820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory7092 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8) (m.theta 8 9)
  exact rule17820 (meaning t m 1982) (meaning t m 2027) (meaning t m 2098) (meaning t m 2114) (meaning t m 2528) (meaning t m 3055) (meaning t m 3367) (meaning t m 5373) source

theorem rule17821 (p1998 p2027 p2114 p2717 p3055 p3367 p3471 : Prop) (h : (¬ p1998) ∨ (¬ p2717) ∨ p2027 ∨ p2114 ∨ (¬ p3471) ∨ (¬ p3367) ∨ (¬ p3055)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2717) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3471) := by
  classical
  tauto

theorem initial17821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3471)) := by
  have source := ElevenTheory.theory7093 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 7 8)
  exact rule17821 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2717) (meaning t m 3055) (meaning t m 3367) (meaning t m 3471) source

theorem rule17822 (p1975 p2027 p2114 p2137 p2274 p2383 p2839 p2962 p3989 : Prop) (h : (¬ p1975) ∨ p2114 ∨ (¬ p2383) ∨ (¬ p2962) ∨ (¬ p2137) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p3989)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2274) ∨ (¬ p2383) ∨ (¬ p2839) ∨ (¬ p2962) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial17822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory7094 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule17822 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2274) (meaning t m 2383) (meaning t m 2839) (meaning t m 2962) (meaning t m 3989) source

theorem rule17823 (p1976 p2027 p2764 p3365 p3572 p3947 p4381 : Prop) (h : p2027 ∨ (¬ p3947) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p4381) ∨ p2764 ∨ (¬ p1976)) : (¬ p1976) ∨ (p2027) ∨ (p2764) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial17823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory7095 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17823 (meaning t m 1976) (meaning t m 2027) (meaning t m 2764) (meaning t m 3365) (meaning t m 3572) (meaning t m 3947) (meaning t m 4381) source

theorem rule17824 (p1985 p2027 p2114 p2264 p2737 p2807 p2811 p3570 : Prop) (h : p2114 ∨ (¬ p2737) ∨ p2027 ∨ (¬ p2811) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p1985) ∨ (¬ p3570)) : (¬ p1985) ∨ (p2027) ∨ (p2114) ∨ (¬ p2264) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial17824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory7096 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule17824 (meaning t m 1985) (meaning t m 2027) (meaning t m 2114) (meaning t m 2264) (meaning t m 2737) (meaning t m 2807) (meaning t m 2811) (meaning t m 3570) source

theorem rule17829 (p2027 p2553 p3359 p3422 p4022 p4343 p4620 : Prop) (h : p2027 ∨ (¬ p4343) ∨ (¬ p3359) ∨ (¬ p3422) ∨ (¬ p4022) ∨ (¬ p2553) ∨ (¬ p4620)) : (p2027) ∨ (¬ p2553) ∨ (¬ p3359) ∨ (¬ p3422) ∨ (¬ p4022) ∨ (¬ p4343) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial17829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory7101 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 9)
  exact rule17829 (meaning t m 2027) (meaning t m 2553) (meaning t m 3359) (meaning t m 3422) (meaning t m 4022) (meaning t m 4343) (meaning t m 4620) source

theorem rule17831 (p1988 p2027 p2114 p2470 p2528 p3266 p3367 p3759 : Prop) (h : (¬ p1988) ∨ (¬ p2470) ∨ p2114 ∨ (¬ p2528) ∨ p2027 ∨ (¬ p3759) ∨ (¬ p3367) ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory7103 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17831 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2470) (meaning t m 2528) (meaning t m 3266) (meaning t m 3367) (meaning t m 3759) source

theorem rule17832 (p3879 p4241 : Prop) (h : p4241 ∨ p3879) : (p3879) ∨ (p4241) := by
  classical
  tauto

theorem initial17832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3879) ∨ (meaning t m 4241) := by
  have source := ElevenTheory.theory7104 (m.theta 3 5) (m.theta 4 5)
  exact rule17832 (meaning t m 3879) (meaning t m 4241) source

theorem rule17833 (p1997 p2027 p3051 p3073 p3697 p3818 p3857 p4235 p4317 : Prop) (h : p3818 ∨ (¬ p4235) ∨ (¬ p3073) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p4317) ∨ (¬ p3051) ∨ (¬ p3697) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (¬ p3051) ∨ (¬ p3073) ∨ (¬ p3697) ∨ (p3818) ∨ (¬ p3857) ∨ (¬ p4235) ∨ (¬ p4317) := by
  classical
  tauto

theorem initial17833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3697)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4317)) := by
  have source := ElevenTheory.theory7105 t (m.theta 0 5) (m.theta 0 8) (m.theta 1 6) (m.theta 1 8) (m.theta 4 5) (m.theta 5 7) (m.theta 8 9)
  exact rule17833 (meaning t m 1997) (meaning t m 2027) (meaning t m 3051) (meaning t m 3073) (meaning t m 3697) (meaning t m 3818) (meaning t m 3857) (meaning t m 4235) (meaning t m 4317) source

theorem rule17834 (p1988 p2027 p2114 p2573 p3367 p3461 p3564 p3759 : Prop) (h : p2114 ∨ (¬ p3759) ∨ (¬ p1988) ∨ (¬ p3367) ∨ (¬ p3564) ∨ (¬ p2573) ∨ (¬ p3461) ∨ p2027) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory7106 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule17834 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2573) (meaning t m 3367) (meaning t m 3461) (meaning t m 3564) (meaning t m 3759) source

theorem rule17835 (p1984 p2027 p2247 p2462 p2761 p2996 p4429 p5284 : Prop) (h : p2027 ∨ (¬ p2996) ∨ p2462 ∨ (¬ p5284) ∨ (¬ p2761) ∨ (¬ p1984) ∨ (¬ p2247) ∨ (¬ p4429)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p2996) ∨ (¬ p4429) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial17835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory7107 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 3 9) (m.theta 7 9) (m.theta 9 10)
  exact rule17835 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2462) (meaning t m 2761) (meaning t m 2996) (meaning t m 4429) (meaning t m 5284) source

theorem rule17837 (p1997 p2027 p2114 p3055 p3367 p3471 p4235 p4344 : Prop) (h : (¬ p3367) ∨ (¬ p3055) ∨ p2027 ∨ p2114 ∨ (¬ p3471) ∨ (¬ p1997) ∨ (¬ p4235) ∨ (¬ p4344)) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3471) ∨ (¬ p4235) ∨ (¬ p4344) := by
  classical
  tauto

theorem initial17837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4344)) := by
  have source := ElevenTheory.theory7109 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7)
  exact rule17837 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 3055) (meaning t m 3367) (meaning t m 3471) (meaning t m 4235) (meaning t m 4344) source

theorem rule17841 (p1984 p2027 p2764 p3549 p3591 p4107 p4381 : Prop) (h : p2027 ∨ (¬ p1984) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p3549) ∨ p2764 ∨ (¬ p4381)) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial17841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory7113 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17841 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 3549) (meaning t m 3591) (meaning t m 4107) (meaning t m 4381) source

theorem rule17843 (p1991 p2027 p2766 p2952 p2992 p4118 p4360 : Prop) (h : p2027 ∨ (¬ p1991) ∨ (¬ p2952) ∨ p2766 ∨ (¬ p2992) ∨ (¬ p4118) ∨ (¬ p4360)) : (¬ p1991) ∨ (p2027) ∨ (p2766) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4118) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial17843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory7115 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 8 9)
  exact rule17843 (meaning t m 1991) (meaning t m 2027) (meaning t m 2766) (meaning t m 2952) (meaning t m 2992) (meaning t m 4118) (meaning t m 4360) source

theorem rule17844 (p1979 p2027 p2169 p2363 p2946 p3172 p4118 : Prop) (h : (¬ p2946) ∨ (¬ p1979) ∨ p2169 ∨ (¬ p3172) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p2363)) : (¬ p1979) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial17844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory7116 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule17844 (meaning t m 1979) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2946) (meaning t m 3172) (meaning t m 4118) source

theorem rule17845 (p2010 p2027 p2246 p2264 p2545 p2807 p3644 p4111 : Prop) (h : (¬ p3644) ∨ p2545 ∨ p2027 ∨ (¬ p2246) ∨ (¬ p4111) ∨ (¬ p2010) ∨ (¬ p2264) ∨ (¬ p2807)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (p2545) ∨ (¬ p2807) ∨ (¬ p3644) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial17845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory7117 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule17845 (meaning t m 2010) (meaning t m 2027) (meaning t m 2246) (meaning t m 2264) (meaning t m 2545) (meaning t m 2807) (meaning t m 3644) (meaning t m 4111) source

theorem rule17851 (p1997 p2027 p2284 p2545 p2992 p4110 p4111 : Prop) (h : (¬ p2284) ∨ p2545 ∨ (¬ p4111) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2992) ∨ (¬ p4110)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2284) ∨ (p2545) ∨ (¬ p2992) ∨ (¬ p4110) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial17851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory7123 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule17851 (meaning t m 1997) (meaning t m 2027) (meaning t m 2284) (meaning t m 2545) (meaning t m 2992) (meaning t m 4110) (meaning t m 4111) source

theorem rule17853 (p1984 p2027 p2284 p3497 p3555 p3578 p4173 : Prop) (h : (¬ p4173) ∨ (¬ p3555) ∨ (¬ p3497) ∨ p2027 ∨ p3578 ∨ (¬ p2284) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p3555) ∨ (p3578) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial17853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3555)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory7125 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule17853 (meaning t m 1984) (meaning t m 2027) (meaning t m 2284) (meaning t m 3497) (meaning t m 3555) (meaning t m 3578) (meaning t m 4173) source

theorem rule17856 (p2006 p2027 p2114 p2144 p2156 p3055 p3367 p3758 : Prop) (h : (¬ p3055) ∨ (¬ p2144) ∨ p2027 ∨ (¬ p2156) ∨ p2114 ∨ (¬ p3367) ∨ (¬ p2006) ∨ (¬ p3758)) : (¬ p2006) ∨ (p2027) ∨ (p2114) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial17856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory7128 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6)
  exact rule17856 (meaning t m 2006) (meaning t m 2027) (meaning t m 2114) (meaning t m 2144) (meaning t m 2156) (meaning t m 3055) (meaning t m 3367) (meaning t m 3758) source

theorem rule17859 (p1990 p2027 p2829 p2842 p3564 p3585 p3744 p4390 : Prop) (h : p2842 ∨ (¬ p3744) ∨ (¬ p1990) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p3564) ∨ (¬ p3585) ∨ (¬ p4390)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2829) ∨ (p2842) ∨ (¬ p3564) ∨ (¬ p3585) ∨ (¬ p3744) ∨ (¬ p4390) := by
  classical
  tauto

theorem initial17859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4390)) := by
  have source := ElevenTheory.theory7131 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule17859 (meaning t m 1990) (meaning t m 2027) (meaning t m 2829) (meaning t m 2842) (meaning t m 3564) (meaning t m 3585) (meaning t m 3744) (meaning t m 4390) source

theorem rule17860 (p1990 p2027 p2114 p2573 p3367 p3564 p3744 p3759 : Prop) (h : (¬ p3744) ∨ (¬ p2573) ∨ p2114 ∨ (¬ p3564) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p3759) ∨ (¬ p3367)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3564) ∨ (¬ p3744) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial17860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory7132 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule17860 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2573) (meaning t m 3367) (meaning t m 3564) (meaning t m 3744) (meaning t m 3759) source

theorem rule17862 (p1975 p2027 p2274 p2498 p2545 p3016 p3319 p3744 : Prop) (h : p2027 ∨ (¬ p2498) ∨ (¬ p2274) ∨ (¬ p1975) ∨ (¬ p3016) ∨ (¬ p3744) ∨ p2545 ∨ (¬ p3319)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2498) ∨ (p2545) ∨ (¬ p3016) ∨ (¬ p3319) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial17862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2498)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory7134 t (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule17862 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2498) (meaning t m 2545) (meaning t m 3016) (meaning t m 3319) (meaning t m 3744) source

theorem rule17864 (p1990 p2027 p2295 p2545 p2992 p3097 p4111 p4336 : Prop) (h : p2545 ∨ (¬ p4111) ∨ (¬ p4336) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p3097) ∨ (¬ p2295)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2295) ∨ (p2545) ∨ (¬ p2992) ∨ (¬ p3097) ∨ (¬ p4111) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial17864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory7136 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule17864 (meaning t m 1990) (meaning t m 2027) (meaning t m 2295) (meaning t m 2545) (meaning t m 2992) (meaning t m 3097) (meaning t m 4111) (meaning t m 4336) source

theorem rule17865 (p1984 p2027 p2247 p2545 p2810 p3005 p4360 : Prop) (h : (¬ p1984) ∨ (¬ p3005) ∨ p2545 ∨ (¬ p2810) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4360)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial17865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory7137 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8)
  exact rule17865 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2545) (meaning t m 2810) (meaning t m 3005) (meaning t m 4360) source

theorem rule17866 (p1984 p2027 p2743 p2997 p3568 p3954 p4195 : Prop) (h : (¬ p1984) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3568) ∨ p2997 ∨ (¬ p4195)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2743) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p3954) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial17866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory7138 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7)
  exact rule17866 (meaning t m 1984) (meaning t m 2027) (meaning t m 2743) (meaning t m 2997) (meaning t m 3568) (meaning t m 3954) (meaning t m 4195) source

theorem rule17867 (p1984 p2027 p2860 p3555 p3578 p3694 p4173 : Prop) (h : p3578 ∨ (¬ p3555) ∨ (¬ p4173) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3694) ∨ (¬ p2860)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2860) ∨ (¬ p3555) ∨ (p3578) ∨ (¬ p3694) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial17867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3555)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory7139 t (m.theta 0 1) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8)
  exact rule17867 (meaning t m 1984) (meaning t m 2027) (meaning t m 2860) (meaning t m 3555) (meaning t m 3578) (meaning t m 3694) (meaning t m 4173) source

theorem rule17868 (p1984 p2027 p2138 p2622 p2741 p2797 p2839 p3873 p4154 : Prop) (h : (¬ p4154) ∨ (¬ p2741) ∨ (¬ p1984) ∨ p2622 ∨ (¬ p2797) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p2839) ∨ (¬ p3873)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2138) ∨ (p2622) ∨ (¬ p2741) ∨ (¬ p2797) ∨ (¬ p2839) ∨ (¬ p3873) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial17868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory7140 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6)
  exact rule17868 (meaning t m 1984) (meaning t m 2027) (meaning t m 2138) (meaning t m 2622) (meaning t m 2741) (meaning t m 2797) (meaning t m 2839) (meaning t m 3873) (meaning t m 4154) source

theorem rule17869 (p1998 p2027 p2264 p2622 p2630 p2657 p2807 : Prop) (h : (¬ p1998) ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p2657) ∨ p2027 ∨ p2622 ∨ (¬ p2630)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2807) := by
  classical
  tauto

theorem initial17869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) := by
  have source := ElevenTheory.theory7141 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule17869 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 2807) source

theorem rule17870 (p1997 p2027 p2284 p2545 p2657 p2946 p4110 : Prop) (h : p2545 ∨ (¬ p2657) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2284) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial17870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory7142 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule17870 (meaning t m 1997) (meaning t m 2027) (meaning t m 2284) (meaning t m 2545) (meaning t m 2657) (meaning t m 2946) (meaning t m 4110) source

theorem rule17875 (p1984 p2027 p2388 p3115 p3583 p3954 p4385 : Prop) (h : (¬ p1984) ∨ p2388 ∨ (¬ p3583) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3115) ∨ (¬ p4385)) : (¬ p1984) ∨ (p2027) ∨ (p2388) ∨ (¬ p3115) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial17875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory7147 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 9)
  exact rule17875 (meaning t m 1984) (meaning t m 2027) (meaning t m 2388) (meaning t m 3115) (meaning t m 3583) (meaning t m 3954) (meaning t m 4385) source

theorem rule17877 (p1976 p2027 p2284 p2388 p2737 p3365 p4173 p4874 : Prop) (h : (¬ p1976) ∨ (¬ p2737) ∨ (¬ p3365) ∨ p2388 ∨ p2027 ∨ (¬ p4874) ∨ (¬ p2284) ∨ (¬ p4173)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p4173) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial17877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory7149 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6)
  exact rule17877 (meaning t m 1976) (meaning t m 2027) (meaning t m 2284) (meaning t m 2388) (meaning t m 2737) (meaning t m 3365) (meaning t m 4173) (meaning t m 4874) source

theorem rule17879 (p1988 p2027 p2406 p2409 p2563 p3125 p3461 : Prop) (h : p2409 ∨ (¬ p3461) ∨ (¬ p1988) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2563)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial17879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory7151 t (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule17879 (meaning t m 1988) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2563) (meaning t m 3125) (meaning t m 3461) source

theorem rule17881 (p1984 p2027 p2114 p2247 p2737 p3005 p4360 : Prop) (h : p2027 ∨ p2114 ∨ (¬ p4360) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p2247) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (p2114) ∨ (¬ p2247) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial17881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory7153 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 8)
  exact rule17881 (meaning t m 1984) (meaning t m 2027) (meaning t m 2114) (meaning t m 2247) (meaning t m 2737) (meaning t m 3005) (meaning t m 4360) source

theorem rule17882 (p1985 p2027 p2427 p2873 p2972 p3237 p3680 p4425 : Prop) (h : (¬ p3237) ∨ p2873 ∨ (¬ p2427) ∨ p2027 ∨ (¬ p2972) ∨ (¬ p4425) ∨ (¬ p1985) ∨ (¬ p3680)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2427) ∨ (p2873) ∨ (¬ p2972) ∨ (¬ p3237) ∨ (¬ p3680) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial17882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3237)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory7154 t (m.theta 1 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule17882 (meaning t m 1985) (meaning t m 2027) (meaning t m 2427) (meaning t m 2873) (meaning t m 2972) (meaning t m 3237) (meaning t m 3680) (meaning t m 4425) source

theorem rule17883 (p1975 p2027 p2274 p2545 p2563 p3115 p3413 p4948 : Prop) (h : (¬ p2563) ∨ (¬ p4948) ∨ (¬ p2274) ∨ (¬ p1975) ∨ (¬ p3413) ∨ p2027 ∨ p2545 ∨ (¬ p3115)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2545) ∨ (¬ p2563) ∨ (¬ p3115) ∨ (¬ p3413) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial17883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory7155 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule17883 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2545) (meaning t m 2563) (meaning t m 3115) (meaning t m 3413) (meaning t m 4948) source

theorem rule17884 (p1984 p2027 p2462 p2737 p3365 p3588 p3873 p4324 : Prop) (h : p2027 ∨ (¬ p4324) ∨ (¬ p3873) ∨ (¬ p1984) ∨ p2462 ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3588)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial17884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory7156 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 9)
  exact rule17884 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 2737) (meaning t m 3365) (meaning t m 3588) (meaning t m 3873) (meaning t m 4324) source

theorem rule17885 (p1985 p2027 p2427 p2545 p3019 p3323 p3744 p4110 : Prop) (h : (¬ p2427) ∨ (¬ p3323) ∨ p2545 ∨ p2027 ∨ (¬ p3744) ∨ (¬ p3019) ∨ (¬ p1985) ∨ (¬ p4110)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2427) ∨ (p2545) ∨ (¬ p3019) ∨ (¬ p3323) ∨ (¬ p3744) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial17885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory7157 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule17885 (meaning t m 1985) (meaning t m 2027) (meaning t m 2427) (meaning t m 2545) (meaning t m 3019) (meaning t m 3323) (meaning t m 3744) (meaning t m 4110) source

theorem rule17886 (p2982 p4031 p4323 p4380 : Prop) (h : (¬ p4380) ∨ (¬ p4323) ∨ (¬ p4031) ∨ (¬ p2982)) : (¬ p2982) ∨ (¬ p4031) ∨ (¬ p4323) ∨ (¬ p4380) := by
  classical
  tauto

theorem initial17886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4323)) ∨ (¬ (meaning t m 4380)) := by
  have source := ElevenTheory.theory7158 (m.theta 0 5) (m.theta 0 9) (m.theta 4 5) (m.theta 5 9)
  exact rule17886 (meaning t m 2982) (meaning t m 4031) (meaning t m 4323) (meaning t m 4380) source

theorem rule17887 (p1988 p2027 p2284 p2388 p2982 p3646 p3680 p4031 : Prop) (h : (¬ p3646) ∨ p2388 ∨ (¬ p2982) ∨ p2027 ∨ (¬ p4031) ∨ (¬ p1988) ∨ (¬ p2284) ∨ (¬ p3680)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p2982) ∨ (¬ p3646) ∨ (¬ p3680) ∨ (¬ p4031) := by
  classical
  tauto

theorem initial17887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4031)) := by
  have source := ElevenTheory.theory7159 t (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule17887 (meaning t m 1988) (meaning t m 2027) (meaning t m 2284) (meaning t m 2388) (meaning t m 2982) (meaning t m 3646) (meaning t m 3680) (meaning t m 4031) source

theorem rule17888 (p1983 p2027 p2284 p2388 p3051 p3246 p3646 : Prop) (h : (¬ p1983) ∨ (¬ p2284) ∨ p2027 ∨ p2388 ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3646)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial17888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory7160 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule17888 (meaning t m 1983) (meaning t m 2027) (meaning t m 2284) (meaning t m 2388) (meaning t m 3051) (meaning t m 3246) (meaning t m 3646) source

theorem rule17889 (p2020 p2027 p2220 p2284 p2388 p3646 p3969 : Prop) (h : p2388 ∨ (¬ p2020) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p2220) ∨ (¬ p3969)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p3646) ∨ (¬ p3969) := by
  classical
  tauto

theorem initial17889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3969)) := by
  have source := ElevenTheory.theory7161 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 10)
  exact rule17889 (meaning t m 2020) (meaning t m 2027) (meaning t m 2220) (meaning t m 2284) (meaning t m 2388) (meaning t m 3646) (meaning t m 3969) source

theorem rule17891 (p1984 p2027 p2264 p2462 p3548 p3947 p4366 : Prop) (h : p2027 ∨ (¬ p2264) ∨ (¬ p4366) ∨ (¬ p3548) ∨ (¬ p1984) ∨ p2462 ∨ (¬ p3947)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2264) ∨ (p2462) ∨ (¬ p3548) ∨ (¬ p3947) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial17891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory7163 t (m.theta 0 1) (m.theta 1 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17891 (meaning t m 1984) (meaning t m 2027) (meaning t m 2264) (meaning t m 2462) (meaning t m 3548) (meaning t m 3947) (meaning t m 4366) source

theorem rule17893 (p1975 p2027 p2299 p2341 p2707 p2842 p3577 p3585 : Prop) (h : p2842 ∨ p2027 ∨ (¬ p2341) ∨ (¬ p3585) ∨ (¬ p2299) ∨ (¬ p2707) ∨ (¬ p3577) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2707) ∨ (p2842) ∨ (¬ p3577) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial17893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2707)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory7165 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17893 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 2707) (meaning t m 2842) (meaning t m 3577) (meaning t m 3585) source

theorem rule17894 (p1990 p2027 p2839 p2842 p3483 p3585 p3744 p3985 : Prop) (h : (¬ p1990) ∨ (¬ p2839) ∨ (¬ p3585) ∨ p2027 ∨ p2842 ∨ (¬ p3985) ∨ (¬ p3744) ∨ (¬ p3483)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2839) ∨ (p2842) ∨ (¬ p3483) ∨ (¬ p3585) ∨ (¬ p3744) ∨ (¬ p3985) := by
  classical
  tauto

theorem initial17894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3985)) := by
  have source := ElevenTheory.theory7166 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 9)
  exact rule17894 (meaning t m 1990) (meaning t m 2027) (meaning t m 2839) (meaning t m 2842) (meaning t m 3483) (meaning t m 3585) (meaning t m 3744) (meaning t m 3985) source

theorem rule17895 (p1998 p2027 p2156 p2177 p2274 p2622 p2951 p3136 : Prop) (h : p2027 ∨ p2622 ∨ (¬ p3136) ∨ (¬ p1998) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2951)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (p2622) ∨ (¬ p2951) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial17895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory7167 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule17895 (meaning t m 1998) (meaning t m 2027) (meaning t m 2156) (meaning t m 2177) (meaning t m 2274) (meaning t m 2622) (meaning t m 2951) (meaning t m 3136) source

theorem rule17897 (p1998 p2027 p2177 p2307 p2545 p2641 p3567 p4111 : Prop) (h : (¬ p3567) ∨ p2545 ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2307) ∨ (¬ p2177) ∨ (¬ p1998) ∨ (¬ p4111)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p3567) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial17897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory7169 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule17897 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2545) (meaning t m 2641) (meaning t m 3567) (meaning t m 4111) source

theorem rule17898 (p1992 p2027 p2191 p2608 p2766 p3555 p3692 : Prop) (h : (¬ p2608) ∨ p2027 ∨ (¬ p1992) ∨ p2766 ∨ (¬ p3692) ∨ (¬ p2191) ∨ (¬ p3555)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2608) ∨ (p2766) ∨ (¬ p3555) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial17898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory7170 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 5 8) (m.theta 8 9)
  exact rule17898 (meaning t m 1992) (meaning t m 2027) (meaning t m 2191) (meaning t m 2608) (meaning t m 2766) (meaning t m 3555) (meaning t m 3692) source

theorem rule17899 (p1975 p2027 p2264 p2299 p2545 p2657 p2807 : Prop) (h : (¬ p2807) ∨ (¬ p1975) ∨ (¬ p2264) ∨ p2027 ∨ p2545 ∨ (¬ p2657) ∨ (¬ p2299)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2807) := by
  classical
  tauto

theorem initial17899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) := by
  have source := ElevenTheory.theory7171 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17899 (meaning t m 1975) (meaning t m 2027) (meaning t m 2264) (meaning t m 2299) (meaning t m 2545) (meaning t m 2657) (meaning t m 2807) source

theorem rule17900 (p1984 p2027 p2743 p2765 p3952 p3954 p4315 : Prop) (h : (¬ p1984) ∨ p2027 ∨ p2765 ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4315) ∨ (¬ p2743)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2743) ∨ (p2765) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial17900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory7172 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6)
  exact rule17900 (meaning t m 1984) (meaning t m 2027) (meaning t m 2743) (meaning t m 2765) (meaning t m 3952) (meaning t m 3954) (meaning t m 4315) source

theorem rule17901 (p1984 p2027 p2245 p2545 p2743 p2810 p3172 p3537 p4967 : Prop) (h : (¬ p1984) ∨ (¬ p2743) ∨ (¬ p3172) ∨ (¬ p2245) ∨ p2027 ∨ p2545 ∨ (¬ p4967) ∨ (¬ p2810) ∨ (¬ p3537)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (p2545) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3172) ∨ (¬ p3537) ∨ (¬ p4967) := by
  classical
  tauto

theorem initial17901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 4967)) := by
  have source := ElevenTheory.theory7173 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 3 8)
  exact rule17901 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2545) (meaning t m 2743) (meaning t m 2810) (meaning t m 3172) (meaning t m 3537) (meaning t m 4967) source

theorem rule17903 (p1975 p2027 p2299 p2388 p2911 p3027 p3662 p4066 p4279 : Prop) (h : p2388 ∨ (¬ p1975) ∨ (¬ p3662) ∨ (¬ p4066) ∨ p2027 ∨ (¬ p4279) ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3027)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2388) ∨ (¬ p2911) ∨ (¬ p3027) ∨ (¬ p3662) ∨ (¬ p4066) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial17903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory7175 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17903 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2388) (meaning t m 2911) (meaning t m 3027) (meaning t m 3662) (meaning t m 4066) (meaning t m 4279) source

theorem rule17906 (p1984 p2027 p2499 p2737 p2842 p3365 p3422 p3873 p4257 : Prop) (h : (¬ p1984) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3422) ∨ (¬ p3873) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p4257) ∨ p2842) : (¬ p1984) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2737) ∨ (p2842) ∨ (¬ p3365) ∨ (¬ p3422) ∨ (¬ p3873) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial17906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory7178 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 6)
  exact rule17906 (meaning t m 1984) (meaning t m 2027) (meaning t m 2499) (meaning t m 2737) (meaning t m 2842) (meaning t m 3365) (meaning t m 3422) (meaning t m 3873) (meaning t m 4257) source

theorem rule17909 (p1998 p2027 p2177 p2386 p2553 p2779 p2829 p2842 p3585 : Prop) (h : (¬ p3585) ∨ p2027 ∨ p2842 ∨ (¬ p2829) ∨ (¬ p1998) ∨ (¬ p2553) ∨ (¬ p2386) ∨ (¬ p2177) ∨ (¬ p2779)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2386) ∨ (¬ p2553) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (p2842) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial17909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory7181 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule17909 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2386) (meaning t m 2553) (meaning t m 2779) (meaning t m 2829) (meaning t m 2842) (meaning t m 3585) source

theorem rule17912 (p1983 p2027 p2839 p2842 p2870 p3246 p3585 : Prop) (h : (¬ p1983) ∨ (¬ p2839) ∨ (¬ p3585) ∨ p2842 ∨ p2027 ∨ (¬ p2870) ∨ (¬ p3246)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2839) ∨ (p2842) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial17912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory7184 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9)
  exact rule17912 (meaning t m 1983) (meaning t m 2027) (meaning t m 2839) (meaning t m 2842) (meaning t m 2870) (meaning t m 3246) (meaning t m 3585) source

theorem rule17913 (p2001 p2027 p2842 p3537 p3585 p3609 p3692 : Prop) (h : (¬ p3585) ∨ p2027 ∨ (¬ p2001) ∨ (¬ p3609) ∨ p2842 ∨ (¬ p3692) ∨ (¬ p3537)) : (¬ p2001) ∨ (p2027) ∨ (p2842) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p3609) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial17913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory7185 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule17913 (meaning t m 2001) (meaning t m 2027) (meaning t m 2842) (meaning t m 3537) (meaning t m 3585) (meaning t m 3609) (meaning t m 3692) source

theorem rule17914 (p1988 p2027 p2233 p2396 p2553 p2573 p2761 : Prop) (h : (¬ p2396) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p2553) ∨ p2233 ∨ (¬ p2573) ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (p2233) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2761) := by
  classical
  tauto

theorem initial17914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2761)) := by
  have source := ElevenTheory.theory7186 t (m.theta 0 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule17914 (meaning t m 1988) (meaning t m 2027) (meaning t m 2233) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 2761) source

theorem rule17919 (p1984 p2027 p2764 p3954 p4242 p4340 p4444 : Prop) (h : (¬ p1984) ∨ (¬ p4340) ∨ (¬ p3954) ∨ p2764 ∨ p2027 ∨ (¬ p4444) ∨ (¬ p4242)) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial17919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory7191 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 8) (m.theta 8 9) (m.theta 9 10)
  exact rule17919 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 3954) (meaning t m 4242) (meaning t m 4340) (meaning t m 4444) source

theorem rule17921 (p1981 p2027 p2352 p2622 p2797 p3567 p3654 p4137 : Prop) (h : (¬ p3567) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p3654) ∨ p2622 ∨ (¬ p4137) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2352) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial17921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory7193 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9)
  exact rule17921 (meaning t m 1981) (meaning t m 2027) (meaning t m 2352) (meaning t m 2622) (meaning t m 2797) (meaning t m 3567) (meaning t m 3654) (meaning t m 4137) source

theorem rule17922 (p1983 p2027 p2396 p2553 p2573 p2622 p2630 p2656 : Prop) (h : p2622 ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p1983) ∨ (¬ p2656) ∨ (¬ p2630)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) := by
  classical
  tauto

theorem initial17922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) := by
  have source := ElevenTheory.theory7194 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule17922 (meaning t m 1983) (meaning t m 2027) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) source

theorem rule17923 (p1984 p2027 p2247 p2295 p2588 p2622 p2797 p3564 p4330 p4340 p4360 p4967 : Prop) (h : (¬ p2247) ∨ (¬ p1984) ∨ p2622 ∨ (¬ p2588) ∨ (¬ p4340) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2797) ∨ (¬ p4967) ∨ (¬ p4360) ∨ (¬ p3564)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2295) ∨ (¬ p2588) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4340) ∨ (¬ p4360) ∨ (¬ p4967) := by
  classical
  tauto

theorem initial17923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4967)) := by
  have source := ElevenTheory.theory7195 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 2 8) (m.theta 3 6) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule17923 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2295) (meaning t m 2588) (meaning t m 2622) (meaning t m 2797) (meaning t m 3564) (meaning t m 4330) (meaning t m 4340) (meaning t m 4360) (meaning t m 4967) source

theorem rule17925 (p2001 p2027 p2284 p2373 p2388 p2590 p3125 p4137 : Prop) (h : (¬ p2001) ∨ (¬ p2373) ∨ (¬ p4137) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p3125) ∨ (¬ p2590) ∨ p2388) : (¬ p2001) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2373) ∨ (p2388) ∨ (¬ p2590) ∨ (¬ p3125) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial17925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory7197 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 9)
  exact rule17925 (meaning t m 2001) (meaning t m 2027) (meaning t m 2284) (meaning t m 2373) (meaning t m 2388) (meaning t m 2590) (meaning t m 3125) (meaning t m 4137) source

theorem rule17927 (p1975 p2027 p2331 p2553 p2622 p2630 p2657 p3984 : Prop) (h : p2622 ∨ (¬ p3984) ∨ (¬ p2657) ∨ (¬ p2630) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2331) ∨ (¬ p2553) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3984) := by
  classical
  tauto

theorem initial17927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3984)) := by
  have source := ElevenTheory.theory7199 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule17927 (meaning t m 1975) (meaning t m 2027) (meaning t m 2331) (meaning t m 2553) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 3984) source

theorem rule17928 (p1984 p2027 p2765 p2870 p3486 p3758 p3954 p4874 : Prop) (h : (¬ p3954) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p1984) ∨ p2765 ∨ (¬ p2870) ∨ (¬ p3486) ∨ (¬ p4874)) : (¬ p1984) ∨ (p2027) ∨ (p2765) ∨ (¬ p2870) ∨ (¬ p3486) ∨ (¬ p3758) ∨ (¬ p3954) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial17928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory7200 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule17928 (meaning t m 1984) (meaning t m 2027) (meaning t m 2765) (meaning t m 2870) (meaning t m 3486) (meaning t m 3758) (meaning t m 3954) (meaning t m 4874) source

theorem rule17929 (p1975 p2027 p2299 p2622 p2630 p2911 p2922 p4116 : Prop) (h : p2622 ∨ (¬ p2630) ∨ (¬ p4116) ∨ (¬ p2911) ∨ (¬ p2299) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2922)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial17929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory7201 t (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17929 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2622) (meaning t m 2630) (meaning t m 2911) (meaning t m 2922) (meaning t m 4116) source

theorem rule17930 (p1975 p2027 p2299 p2573 p2622 p2630 p2656 p2911 p3920 : Prop) (h : p2622 ∨ (¬ p2630) ∨ p2027 ∨ (¬ p3920) ∨ (¬ p1975) ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p2656) ∨ (¬ p2573)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2573) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2911) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial17930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory7202 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule17930 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2573) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 2911) (meaning t m 3920) source

theorem rule17931 (p1988 p2027 p2274 p2588 p2765 p3461 p3564 : Prop) (h : (¬ p2588) ∨ p2027 ∨ p2765 ∨ (¬ p1988) ∨ (¬ p2274) ∨ (¬ p3461) ∨ (¬ p3564)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2588) ∨ (p2765) ∨ (¬ p3461) ∨ (¬ p3564) := by
  classical
  tauto

theorem initial17931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) := by
  have source := ElevenTheory.theory7203 t (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule17931 (meaning t m 1988) (meaning t m 2027) (meaning t m 2274) (meaning t m 2588) (meaning t m 2765) (meaning t m 3461) (meaning t m 3564) source

theorem rule17932 (p1992 p2027 p2247 p2608 p2765 p3662 p3952 : Prop) (h : p2765 ∨ (¬ p3952) ∨ (¬ p1992) ∨ (¬ p2247) ∨ (¬ p3662) ∨ (¬ p2608) ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2608) ∨ (p2765) ∨ (¬ p3662) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial17932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory7204 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6)
  exact rule17932 (meaning t m 1992) (meaning t m 2027) (meaning t m 2247) (meaning t m 2608) (meaning t m 2765) (meaning t m 3662) (meaning t m 3952) source

theorem rule17933 (p1992 p2027 p2284 p2388 p2608 p3555 p4173 : Prop) (h : p2027 ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p1992) ∨ p2388 ∨ (¬ p2284)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial17933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory7205 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6)
  exact rule17933 (meaning t m 1992) (meaning t m 2027) (meaning t m 2284) (meaning t m 2388) (meaning t m 2608) (meaning t m 3555) (meaning t m 4173) source

theorem rule17934 (p1992 p2027 p2247 p2608 p2742 p2810 p3008 p3574 : Prop) (h : (¬ p2742) ∨ (¬ p2810) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p1992) ∨ (¬ p2608) ∨ p3008) : (¬ p1992) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2608) ∨ (¬ p2742) ∨ (¬ p2810) ∨ (p3008) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial17934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory7206 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6)
  exact rule17934 (meaning t m 1992) (meaning t m 2027) (meaning t m 2247) (meaning t m 2608) (meaning t m 2742) (meaning t m 2810) (meaning t m 3008) (meaning t m 3574) source

theorem rule17935 (p1992 p2027 p2187 p2608 p2765 p3591 p3923 : Prop) (h : (¬ p3923) ∨ (¬ p1992) ∨ (¬ p2608) ∨ p2765 ∨ (¬ p2187) ∨ p2027 ∨ (¬ p3591)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2608) ∨ (p2765) ∨ (¬ p3591) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial17935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory7207 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 5 6) (m.theta 6 8)
  exact rule17935 (meaning t m 1992) (meaning t m 2027) (meaning t m 2187) (meaning t m 2608) (meaning t m 2765) (meaning t m 3591) (meaning t m 3923) source

theorem rule17938 (p1983 p2027 p2842 p2911 p3201 p3246 p3570 : Prop) (h : (¬ p3246) ∨ p2842 ∨ (¬ p2911) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p3201) ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (p2842) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3246) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial17938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory7210 t (m.theta 2 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17938 (meaning t m 1983) (meaning t m 2027) (meaning t m 2842) (meaning t m 2911) (meaning t m 3201) (meaning t m 3246) (meaning t m 3570) source

theorem rule17942 (p1998 p2027 p2177 p2873 p2891 p3246 p4278 p4710 : Prop) (h : (¬ p2891) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p4710) ∨ p2873 ∨ (¬ p4278) ∨ (¬ p1998) ∨ (¬ p3246)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2873) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p4278) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial17942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory7214 t (m.theta 1 5) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule17942 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2873) (meaning t m 2891) (meaning t m 3246) (meaning t m 4278) (meaning t m 4710) source

theorem rule17945 (p1992 p2027 p2608 p2997 p3097 p3555 p4173 : Prop) (h : p2997 ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p1992) ∨ (¬ p4173)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3555) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial17945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory7217 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7)
  exact rule17945 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2997) (meaning t m 3097) (meaning t m 3555) (meaning t m 4173) source

theorem rule17949 (p1990 p2027 p2220 p2563 p2622 p2630 p2951 p3413 p3880 : Prop) (h : p2027 ∨ (¬ p2951) ∨ (¬ p3413) ∨ (¬ p3880) ∨ p2622 ∨ (¬ p2220) ∨ (¬ p2630) ∨ (¬ p1990) ∨ (¬ p2563)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2563) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2951) ∨ (¬ p3413) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial17949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory7221 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule17949 (meaning t m 1990) (meaning t m 2027) (meaning t m 2220) (meaning t m 2563) (meaning t m 2622) (meaning t m 2630) (meaning t m 2951) (meaning t m 3413) (meaning t m 3880) source

end SunPrize.SMT
