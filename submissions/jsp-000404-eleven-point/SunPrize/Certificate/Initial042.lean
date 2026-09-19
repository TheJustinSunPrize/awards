import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory026
import SunPrize.Certificate.Theory027
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule19129 (p1984 p2027 p3309 p3688 p3818 p3822 p3954 : Prop) (h : (¬ p3822) ∨ (¬ p1984) ∨ (¬ p3688) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3309) ∨ p3818) : (¬ p1984) ∨ (p2027) ∨ (¬ p3309) ∨ (¬ p3688) ∨ (p3818) ∨ (¬ p3822) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial19129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3688)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory8385 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7)
  exact rule19129 (meaning t m 1984) (meaning t m 2027) (meaning t m 3309) (meaning t m 3688) (meaning t m 3818) (meaning t m 3822) (meaning t m 3954) source

theorem rule19135 (p2027 p2589 p2774 p2850 p3475 p3905 p4845 : Prop) (h : (¬ p3475) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p4845) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2774) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p3905) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial19135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory8391 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5)
  exact rule19135 (meaning t m 2027) (meaning t m 2589) (meaning t m 2774) (meaning t m 2850) (meaning t m 3475) (meaning t m 3905) (meaning t m 4845) source

theorem rule19136 (p2027 p2098 p2589 p2850 p3475 p3905 p4968 : Prop) (h : (¬ p2850) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p3475) ∨ (¬ p4968) ∨ (¬ p2589) ∨ (¬ p2098)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p3905) ∨ (¬ p4968) := by
  classical
  tauto

theorem initial19136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4968)) := by
  have source := ElevenTheory.theory8392 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 4 5)
  exact rule19136 (meaning t m 2027) (meaning t m 2098) (meaning t m 2589) (meaning t m 2850) (meaning t m 3475) (meaning t m 3905) (meaning t m 4968) source

theorem rule19137 (p1998 p2027 p2323 p2807 p2881 p3931 p5660 : Prop) (h : p2027 ∨ (¬ p2881) ∨ (¬ p3931) ∨ p2323 ∨ (¬ p1998) ∨ (¬ p2807) ∨ (¬ p5660)) : (¬ p1998) ∨ (p2027) ∨ (p2323) ∨ (¬ p2807) ∨ (¬ p2881) ∨ (¬ p3931) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial19137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory8393 t (m.theta 0 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 10) (m.theta 7 8)
  exact rule19137 (meaning t m 1998) (meaning t m 2027) (meaning t m 2323) (meaning t m 2807) (meaning t m 2881) (meaning t m 3931) (meaning t m 5660) source

theorem rule19139 (p1976 p2027 p2764 p2780 p2829 p4379 p5387 : Prop) (h : (¬ p1976) ∨ (¬ p5387) ∨ (¬ p4379) ∨ p2027 ∨ p2764 ∨ (¬ p2780) ∨ (¬ p2829)) : (¬ p1976) ∨ (p2027) ∨ (p2764) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p4379) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial19139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory8395 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 9) (m.theta 9 10)
  exact rule19139 (meaning t m 1976) (meaning t m 2027) (meaning t m 2764) (meaning t m 2780) (meaning t m 2829) (meaning t m 4379) (meaning t m 5387) source

theorem rule19140 (p1984 p2027 p2780 p2829 p2938 p3583 p3873 p4244 : Prop) (h : p2938 ∨ (¬ p1984) ∨ (¬ p3583) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p3873) ∨ (¬ p4244)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (p2938) ∨ (¬ p3583) ∨ (¬ p3873) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial19140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory8396 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 7)
  exact rule19140 (meaning t m 1984) (meaning t m 2027) (meaning t m 2780) (meaning t m 2829) (meaning t m 2938) (meaning t m 3583) (meaning t m 3873) (meaning t m 4244) source

theorem rule19141 (p1990 p2027 p2156 p2169 p2363 p3692 p4120 : Prop) (h : (¬ p1990) ∨ (¬ p3692) ∨ (¬ p2363) ∨ p2169 ∨ (¬ p2156) ∨ p2027 ∨ (¬ p4120)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial19141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory8397 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule19141 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2169) (meaning t m 2363) (meaning t m 3692) (meaning t m 4120) source

theorem rule19142 (p2005 p2027 p2169 p2363 p2476 p2534 p2573 : Prop) (h : (¬ p2573) ∨ (¬ p2005) ∨ p2027 ∨ (¬ p2363) ∨ p2169 ∨ (¬ p2534) ∨ (¬ p2476)) : (¬ p2005) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2573) := by
  classical
  tauto

theorem initial19142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2573)) := by
  have source := ElevenTheory.theory8398 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule19142 (meaning t m 2005) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2476) (meaning t m 2534) (meaning t m 2573) source

theorem rule19144 (p1984 p2027 p2997 p3483 p3591 p3822 p4026 : Prop) (h : (¬ p1984) ∨ (¬ p3822) ∨ p2997 ∨ p2027 ∨ (¬ p4026) ∨ (¬ p3591) ∨ (¬ p3483)) : (¬ p1984) ∨ (p2027) ∨ (p2997) ∨ (¬ p3483) ∨ (¬ p3591) ∨ (¬ p3822) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial19144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory8400 t (m.theta 0 1) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 9)
  exact rule19144 (meaning t m 1984) (meaning t m 2027) (meaning t m 2997) (meaning t m 3483) (meaning t m 3591) (meaning t m 3822) (meaning t m 4026) source

theorem rule19146 (p1998 p2027 p2352 p2363 p2588 p2997 p4348 : Prop) (h : (¬ p2352) ∨ (¬ p2588) ∨ (¬ p1998) ∨ (¬ p4348) ∨ p2997 ∨ p2027 ∨ (¬ p2363)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial19146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory8402 t (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule19146 (meaning t m 1998) (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2588) (meaning t m 2997) (meaning t m 4348) source

theorem rule19147 (p1994 p2027 p2114 p2737 p2774 p3365 p3574 p4390 : Prop) (h : (¬ p1994) ∨ (¬ p3365) ∨ (¬ p3574) ∨ p2027 ∨ p2114 ∨ (¬ p4390) ∨ (¬ p2774) ∨ (¬ p2737)) : (¬ p1994) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p3574) ∨ (¬ p4390) := by
  classical
  tauto

theorem initial19147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4390)) := by
  have source := ElevenTheory.theory8403 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6)
  exact rule19147 (meaning t m 1994) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 2774) (meaning t m 3365) (meaning t m 3574) (meaning t m 4390) source

theorem rule19148 (p2005 p2027 p2114 p3016 p3367 p3389 p3742 p3759 : Prop) (h : (¬ p2005) ∨ p2114 ∨ (¬ p3759) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p3016) ∨ (¬ p3389) ∨ (¬ p3742)) : (¬ p2005) ∨ (p2027) ∨ (p2114) ∨ (¬ p3016) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial19148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory8404 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule19148 (meaning t m 2005) (meaning t m 2027) (meaning t m 2114) (meaning t m 3016) (meaning t m 3367) (meaning t m 3389) (meaning t m 3742) (meaning t m 3759) source

theorem rule19150 (p2007 p2323 p2573 p2663 p4598 : Prop) (h : p2323 ∨ (¬ p2573) ∨ p4598 ∨ (¬ p2007) ∨ (¬ p2663)) : (¬ p2007) ∨ (p2323) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (p4598) := by
  classical
  tauto

theorem initial19150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (meaning t m 4598) := by
  have source := ElevenTheory.theory8406 t (m.theta 0 3) (m.theta 0 4) (m.theta 4 6) (m.theta 4 8)
  exact rule19150 (meaning t m 2007) (meaning t m 2323) (meaning t m 2573) (meaning t m 2663) (meaning t m 4598) source

theorem rule19154 (p2000 p2027 p2202 p2427 p2493 p2579 p3486 p4202 : Prop) (h : p2027 ∨ (¬ p2000) ∨ p2202 ∨ (¬ p2427) ∨ (¬ p2579) ∨ (¬ p2493) ∨ (¬ p4202) ∨ (¬ p3486)) : (¬ p2000) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3486) ∨ (¬ p4202) := by
  classical
  tauto

theorem initial19154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4202)) := by
  have source := ElevenTheory.theory8410 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule19154 (meaning t m 2000) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 2493) (meaning t m 2579) (meaning t m 3486) (meaning t m 4202) source

theorem rule19155 (p1990 p2027 p2284 p2611 p2807 p3136 p3572 p4117 : Prop) (h : (¬ p1990) ∨ (¬ p3572) ∨ (¬ p2807) ∨ (¬ p3136) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p2284) ∨ p2611) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (p2611) ∨ (¬ p2807) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial19155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory8411 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6)
  exact rule19155 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2611) (meaning t m 2807) (meaning t m 3136) (meaning t m 3572) (meaning t m 4117) source

theorem rule19156 (p1979 p2027 p2233 p2810 p3136 p3389 p3742 : Prop) (h : (¬ p3389) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p1979) ∨ p2233 ∨ (¬ p3742)) : (¬ p1979) ∨ (p2027) ∨ (p2233) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p3389) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial19156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory8412 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule19156 (meaning t m 1979) (meaning t m 2027) (meaning t m 2233) (meaning t m 2810) (meaning t m 3136) (meaning t m 3389) (meaning t m 3742) source

theorem rule19157 (p2005 p2027 p2299 p2573 p2766 p3540 p3921 p4348 : Prop) (h : (¬ p3921) ∨ (¬ p4348) ∨ (¬ p3540) ∨ (¬ p2299) ∨ p2766 ∨ (¬ p2573) ∨ p2027 ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2573) ∨ (p2766) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial19157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory8413 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule19157 (meaning t m 2005) (meaning t m 2027) (meaning t m 2299) (meaning t m 2573) (meaning t m 2766) (meaning t m 3540) (meaning t m 3921) (meaning t m 4348) source

theorem rule19158 (p1998 p2027 p2247 p2688 p2881 p2891 p3093 p4512 : Prop) (h : p2688 ∨ (¬ p4512) ∨ (¬ p3093) ∨ (¬ p2891) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3093) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial19158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory8414 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 1 6) (m.theta 5 7) (m.theta 7 8)
  exact rule19158 (meaning t m 1998) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 2881) (meaning t m 2891) (meaning t m 3093) (meaning t m 4512) source

theorem rule19159 (p1997 p2027 p2542 p2598 p2611 p3201 p3742 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p2542) ∨ (¬ p1997) ∨ (¬ p3201) ∨ (¬ p3742) ∨ (¬ p2598)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3201) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial19159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory8415 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule19159 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2598) (meaning t m 2611) (meaning t m 3201) (meaning t m 3742) source

theorem rule19163 (p2005 p2027 p2997 p3016 p3742 p3791 p5503 : Prop) (h : p2997 ∨ p2027 ∨ (¬ p2005) ∨ (¬ p5503) ∨ (¬ p3742) ∨ (¬ p3016) ∨ (¬ p3791)) : (¬ p2005) ∨ (p2027) ∨ (p2997) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3791) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial19163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory8419 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 10)
  exact rule19163 (meaning t m 2005) (meaning t m 2027) (meaning t m 2997) (meaning t m 3016) (meaning t m 3742) (meaning t m 3791) (meaning t m 5503) source

theorem rule19164 (p2000 p2027 p2563 p2764 p3646 p3904 p4322 p4948 : Prop) (h : (¬ p2000) ∨ p2764 ∨ (¬ p2563) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4948) ∨ (¬ p4322)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2563) ∨ (p2764) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4322) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial19164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory8420 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule19164 (meaning t m 2000) (meaning t m 2027) (meaning t m 2563) (meaning t m 2764) (meaning t m 3646) (meaning t m 3904) (meaning t m 4322) (meaning t m 4948) source

theorem rule19165 (p2027 p2247 p2996 p3379 p3487 p4650 : Prop) (h : (¬ p3379) ∨ (¬ p3487) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4650) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial19165 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory8421 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7)
  exact rule19165 (meaning t m 2027) (meaning t m 2247) (meaning t m 2996) (meaning t m 3379) (meaning t m 3487) (meaning t m 4650) source

theorem rule19167 (p1995 p2027 p2169 p2363 p3379 p3860 p4261 : Prop) (h : (¬ p2363) ∨ (¬ p3860) ∨ p2169 ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4261) ∨ (¬ p1995)) : (¬ p1995) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial19167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory8423 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 6 8) (m.theta 8 9)
  exact rule19167 (meaning t m 1995) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 3379) (meaning t m 3860) (meaning t m 4261) source

theorem rule19168 (p2498 p2588 p3309 : Prop) (h : (¬ p2588) ∨ (¬ p3309) ∨ (¬ p2498)) : (¬ p2498) ∨ (¬ p2588) ∨ (¬ p3309) := by
  classical
  tauto

theorem initial19168 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3309)) := by
  have source := ElevenTheory.theory8424 (m.theta 1 6) (m.theta 4 6) (m.theta 6 7)
  exact rule19168 (meaning t m 2498) (meaning t m 2588) (meaning t m 3309) source

theorem rule19169 (p2027 p2505 p2579 p2588 p3309 p5191 : Prop) (h : (¬ p2588) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p5191) ∨ (¬ p2505)) : (p2027) ∨ (¬ p2505) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3309) ∨ (¬ p5191) := by
  classical
  tauto

theorem initial19169 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 5191)) := by
  have source := ElevenTheory.theory8425 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7)
  exact rule19169 (meaning t m 2027) (meaning t m 2505) (meaning t m 2579) (meaning t m 2588) (meaning t m 3309) (meaning t m 5191) source

theorem rule19170 (p1994 p2027 p2630 p2688 p2957 p2958 p3172 p3189 p4315 : Prop) (h : (¬ p1994) ∨ p2027 ∨ (¬ p3189) ∨ (¬ p3172) ∨ p2688 ∨ (¬ p2957) ∨ (¬ p2958) ∨ (¬ p4315) ∨ (¬ p2630)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p2688) ∨ (¬ p2957) ∨ (¬ p2958) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial19170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory8426 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 8)
  exact rule19170 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2688) (meaning t m 2957) (meaning t m 2958) (meaning t m 3172) (meaning t m 3189) (meaning t m 4315) source

theorem rule19171 (p2005 p2027 p2630 p2688 p2992 p3016 p4315 : Prop) (h : (¬ p3016) ∨ (¬ p2005) ∨ p2027 ∨ p2688 ∨ (¬ p2992) ∨ (¬ p2630) ∨ (¬ p4315)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2630) ∨ (p2688) ∨ (¬ p2992) ∨ (¬ p3016) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial19171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory8427 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule19171 (meaning t m 2005) (meaning t m 2027) (meaning t m 2630) (meaning t m 2688) (meaning t m 2992) (meaning t m 3016) (meaning t m 4315) source

theorem rule19172 (p2138 p2774 p4193 : Prop) (h : (¬ p4193) ∨ (¬ p2138) ∨ (¬ p2774)) : (¬ p2138) ∨ (¬ p2774) ∨ (¬ p4193) := by
  classical
  tauto

theorem initial19172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4193)) := by
  have source := ElevenTheory.theory8428 (m.theta 0 2) (m.theta 2 5) (m.theta 2 6)
  exact rule19172 (meaning t m 2138) (meaning t m 2774) (meaning t m 4193) source

theorem rule19173 (p1979 p2027 p2114 p2144 p2156 p2737 p3365 p3952 : Prop) (h : p2027 ∨ p2114 ∨ (¬ p1979) ∨ (¬ p2737) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p3365) ∨ (¬ p3952)) : (¬ p1979) ∨ (p2027) ∨ (p2114) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial19173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory8429 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6)
  exact rule19173 (meaning t m 1979) (meaning t m 2027) (meaning t m 2114) (meaning t m 2144) (meaning t m 2156) (meaning t m 2737) (meaning t m 3365) (meaning t m 3952) source

theorem rule19178 (p2264 p2449 p3657 : Prop) (h : (¬ p2449) ∨ (¬ p3657) ∨ p2264) : (p2264) ∨ (¬ p2449) ∨ (¬ p3657) := by
  classical
  tauto

theorem initial19178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2264) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3657)) := by
  have source := ElevenTheory.theory8434 (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule19178 (meaning t m 2264) (meaning t m 2449) (meaning t m 3657) source

theorem rule19179 (p1994 p2027 p2156 p2766 p3952 p4120 p4347 p4506 p4700 : Prop) (h : p2027 ∨ (¬ p2156) ∨ (¬ p4347) ∨ (¬ p4506) ∨ p2766 ∨ (¬ p4120) ∨ (¬ p1994) ∨ (¬ p4700) ∨ (¬ p3952)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2156) ∨ (p2766) ∨ (¬ p3952) ∨ (¬ p4120) ∨ (¬ p4347) ∨ (¬ p4506) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial19179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4506)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory8435 t (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule19179 (meaning t m 1994) (meaning t m 2027) (meaning t m 2156) (meaning t m 2766) (meaning t m 3952) (meaning t m 4120) (meaning t m 4347) (meaning t m 4506) (meaning t m 4700) source

theorem rule19180 (p1990 p2997 p3549 p4518 : Prop) (h : p2997 ∨ (¬ p3549) ∨ (¬ p1990) ∨ p4518) : (¬ p1990) ∨ (p2997) ∨ (¬ p3549) ∨ (p4518) := by
  classical
  tauto

theorem initial19180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3549)) ∨ (meaning t m 4518) := by
  have source := ElevenTheory.theory8436 t (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule19180 (meaning t m 1990) (meaning t m 2997) (meaning t m 3549) (meaning t m 4518) source

theorem rule19181 (p2011 p2027 p2148 p3051 p3115 p4129 p4386 p4391 : Prop) (h : (¬ p4391) ∨ p2148 ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4129) ∨ (¬ p4386) ∨ (¬ p2011) ∨ (¬ p3115)) : (¬ p2011) ∨ (p2027) ∨ (p2148) ∨ (¬ p3051) ∨ (¬ p3115) ∨ (¬ p4129) ∨ (¬ p4386) ∨ (¬ p4391) := by
  classical
  tauto

theorem initial19181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4391)) := by
  have source := ElevenTheory.theory8437 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 10)
  exact rule19181 (meaning t m 2011) (meaning t m 2027) (meaning t m 2148) (meaning t m 3051) (meaning t m 3115) (meaning t m 4129) (meaning t m 4386) (meaning t m 4391) source

theorem rule19182 (p1990 p2027 p2284 p3623 p3631 p3821 p4283 p4320 : Prop) (h : p2027 ∨ (¬ p1990) ∨ (¬ p4320) ∨ (¬ p2284) ∨ (¬ p3821) ∨ p3623 ∨ (¬ p4283) ∨ (¬ p3631)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (p3623) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4283) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial19182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory8438 t (m.theta 0 7) (m.theta 1 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule19182 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 3623) (meaning t m 3631) (meaning t m 3821) (meaning t m 4283) (meaning t m 4320) source

theorem rule19185 (p3572 p4035 p4429 : Prop) (h : (¬ p4429) ∨ (¬ p3572) ∨ p4035) : (¬ p3572) ∨ (p4035) ∨ (¬ p4429) := by
  classical
  tauto

theorem initial19185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3572)) ∨ (meaning t m 4035) ∨ (¬ (meaning t m 4429)) := by
  have source := ElevenTheory.theory8441 (m.theta 2 3) (m.theta 3 7) (m.theta 3 9)
  exact rule19185 (meaning t m 3572) (meaning t m 4035) (meaning t m 4429) source

theorem rule19186 (p1994 p2027 p2114 p2630 p3037 p3399 p3572 p3954 : Prop) (h : p2114 ∨ (¬ p3572) ∨ (¬ p1994) ∨ (¬ p2630) ∨ (¬ p3399) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3037)) : (¬ p1994) ∨ (p2027) ∨ (p2114) ∨ (¬ p2630) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3572) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial19186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory8442 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule19186 (meaning t m 1994) (meaning t m 2027) (meaning t m 2114) (meaning t m 2630) (meaning t m 3037) (meaning t m 3399) (meaning t m 3572) (meaning t m 3954) source

theorem rule19187 (p1980 p2027 p2114 p2797 p3830 p3853 p3954 p4035 : Prop) (h : p2114 ∨ (¬ p3954) ∨ (¬ p4035) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p1980) ∨ (¬ p3830) ∨ (¬ p3853)) : (¬ p1980) ∨ (p2027) ∨ (p2114) ∨ (¬ p2797) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p3954) ∨ (¬ p4035) := by
  classical
  tauto

theorem initial19187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3853)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4035)) := by
  have source := ElevenTheory.theory8443 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 9) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9)
  exact rule19187 (meaning t m 1980) (meaning t m 2027) (meaning t m 2114) (meaning t m 2797) (meaning t m 3830) (meaning t m 3853) (meaning t m 3954) (meaning t m 4035) source

theorem rule19190 (p2000 p2027 p2579 p2766 p3573 p3979 p4286 p4347 : Prop) (h : (¬ p4347) ∨ p2766 ∨ (¬ p2579) ∨ (¬ p2000) ∨ p2027 ∨ (¬ p3979) ∨ (¬ p3573) ∨ (¬ p4286)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2579) ∨ (p2766) ∨ (¬ p3573) ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial19190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory8446 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule19190 (meaning t m 2000) (meaning t m 2027) (meaning t m 2579) (meaning t m 2766) (meaning t m 3573) (meaning t m 3979) (meaning t m 4286) (meaning t m 4347) source

theorem rule19193 (p3545 p4172 p4988 : Prop) (h : (¬ p4172) ∨ (¬ p4988) ∨ p3545) : (p3545) ∨ (¬ p4172) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial19193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3545) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory8449 (m.theta 0 1) (m.theta 0 5) (m.theta 0 7)
  exact rule19193 (meaning t m 3545) (meaning t m 4172) (meaning t m 4988) source

theorem rule19197 (p1993 p2027 p2396 p2997 p3166 p3414 p3947 : Prop) (h : p2027 ∨ (¬ p3166) ∨ (¬ p2396) ∨ (¬ p3414) ∨ (¬ p1993) ∨ p2997 ∨ (¬ p3947)) : (¬ p1993) ∨ (p2027) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial19197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory8453 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 9)
  exact rule19197 (meaning t m 1993) (meaning t m 2027) (meaning t m 2396) (meaning t m 2997) (meaning t m 3166) (meaning t m 3414) (meaning t m 3947) source

theorem rule19198 (p1997 p2027 p2114 p2542 p2663 p2737 p2811 p3389 p3742 : Prop) (h : (¬ p1997) ∨ p2114 ∨ (¬ p2663) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p2811) ∨ (¬ p2542) ∨ (¬ p3389) ∨ (¬ p3742)) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2542) ∨ (¬ p2663) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3389) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial19198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory8454 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule19198 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2542) (meaning t m 2663) (meaning t m 2737) (meaning t m 2811) (meaning t m 3389) (meaning t m 3742) source

theorem rule19201 (p1994 p2027 p2264 p2611 p2630 p2807 p3659 p4117 p4357 : Prop) (h : (¬ p4357) ∨ (¬ p2807) ∨ p2611 ∨ (¬ p4117) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p2630) ∨ (¬ p3659) ∨ (¬ p2264)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2264) ∨ (p2611) ∨ (¬ p2630) ∨ (¬ p2807) ∨ (¬ p3659) ∨ (¬ p4117) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial19201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory8457 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule19201 (meaning t m 1994) (meaning t m 2027) (meaning t m 2264) (meaning t m 2611) (meaning t m 2630) (meaning t m 2807) (meaning t m 3659) (meaning t m 4117) (meaning t m 4357) source

theorem rule19202 (p1982 p2027 p2220 p2323 p2958 p3256 p3969 p5600 : Prop) (h : p2323 ∨ p2027 ∨ (¬ p2220) ∨ (¬ p3969) ∨ (¬ p5600) ∨ (¬ p2958) ∨ (¬ p1982) ∨ (¬ p3256)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2220) ∨ (p2323) ∨ (¬ p2958) ∨ (¬ p3256) ∨ (¬ p3969) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial19202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory8458 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule19202 (meaning t m 1982) (meaning t m 2027) (meaning t m 2220) (meaning t m 2323) (meaning t m 2958) (meaning t m 3256) (meaning t m 3969) (meaning t m 5600) source

theorem rule19203 (p1982 p2027 p2611 p2807 p3005 p3256 p3572 p4117 : Prop) (h : (¬ p3256) ∨ p2611 ∨ (¬ p1982) ∨ p2027 ∨ (¬ p3005) ∨ (¬ p2807) ∨ (¬ p4117) ∨ (¬ p3572)) : (¬ p1982) ∨ (p2027) ∨ (p2611) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3572) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial19203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory8459 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 8 9)
  exact rule19203 (meaning t m 1982) (meaning t m 2027) (meaning t m 2611) (meaning t m 2807) (meaning t m 3005) (meaning t m 3256) (meaning t m 3572) (meaning t m 4117) source

theorem rule19204 (p1995 p2027 p2997 p3097 p3379 p3555 p4173 : Prop) (h : p2997 ∨ (¬ p1995) ∨ (¬ p3097) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p3555)) : (¬ p1995) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial19204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory8460 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7)
  exact rule19204 (meaning t m 1995) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3379) (meaning t m 3555) (meaning t m 4173) source

theorem rule19205 (p1995 p2027 p2274 p2498 p2588 p2765 p3379 p3555 p4512 : Prop) (h : (¬ p3379) ∨ (¬ p1995) ∨ p2027 ∨ p2765 ∨ (¬ p2274) ∨ (¬ p3555) ∨ (¬ p4512) ∨ (¬ p2588) ∨ (¬ p2498)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2498) ∨ (¬ p2588) ∨ (p2765) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial19205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory8461 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 1 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule19205 (meaning t m 1995) (meaning t m 2027) (meaning t m 2274) (meaning t m 2498) (meaning t m 2588) (meaning t m 2765) (meaning t m 3379) (meaning t m 3555) (meaning t m 4512) source

theorem rule19206 (p1994 p2027 p2177 p2630 p2997 p3553 p3572 : Prop) (h : (¬ p2630) ∨ (¬ p1994) ∨ (¬ p3572) ∨ p2997 ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3553)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2630) ∨ (p2997) ∨ (¬ p3553) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial19206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory8462 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule19206 (meaning t m 1994) (meaning t m 2027) (meaning t m 2177) (meaning t m 2630) (meaning t m 2997) (meaning t m 3553) (meaning t m 3572) source

theorem rule19207 (p1994 p2027 p2630 p3177 p3441 p3877 p4181 p5590 : Prop) (h : p2027 ∨ p3441 ∨ (¬ p4181) ∨ (¬ p5590) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p2630) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p3177) ∨ (p3441) ∨ (¬ p3877) ∨ (¬ p4181) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial19207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3177)) ∨ (meaning t m 3441) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory8463 t (m.theta 0 8) (m.theta 1 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 10)
  exact rule19207 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 3177) (meaning t m 3441) (meaning t m 3877) (meaning t m 4181) (meaning t m 5590) source

theorem rule19208 (p1994 p2202 p3742 p4646 : Prop) (h : p2202 ∨ (¬ p1994) ∨ (¬ p3742) ∨ p4646) : (¬ p1994) ∨ (p2202) ∨ (¬ p3742) ∨ (p4646) := by
  classical
  tauto

theorem initial19208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3742)) ∨ (meaning t m 4646) := by
  have source := ElevenTheory.theory8464 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule19208 (meaning t m 1994) (meaning t m 2202) (meaning t m 3742) (meaning t m 4646) source

theorem rule19210 (p1995 p2027 p2299 p2633 p3379 p3549 p3591 : Prop) (h : (¬ p3591) ∨ (¬ p1995) ∨ p2027 ∨ p2633 ∨ (¬ p2299) ∨ (¬ p3379) ∨ (¬ p3549)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3379) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial19210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory8466 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 6 7) (m.theta 7 8)
  exact rule19210 (meaning t m 1995) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3379) (meaning t m 3549) (meaning t m 3591) source

theorem rule19212 (p2005 p2027 p2264 p2323 p2807 p3422 p3659 p3686 : Prop) (h : p2323 ∨ p2027 ∨ (¬ p2807) ∨ (¬ p3659) ∨ (¬ p2264) ∨ (¬ p2005) ∨ (¬ p3422) ∨ (¬ p3686)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2264) ∨ (p2323) ∨ (¬ p2807) ∨ (¬ p3422) ∨ (¬ p3659) ∨ (¬ p3686) := by
  classical
  tauto

theorem initial19212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3686)) := by
  have source := ElevenTheory.theory8468 t (m.theta 0 3) (m.theta 2 4) (m.theta 2 7) (m.theta 3 7) (m.theta 4 6) (m.theta 7 8)
  exact rule19212 (meaning t m 2005) (meaning t m 2027) (meaning t m 2264) (meaning t m 2323) (meaning t m 2807) (meaning t m 3422) (meaning t m 3659) (meaning t m 3686) source

theorem rule19213 (p1980 p2027 p2177 p2641 p2996 p2997 p3945 p3947 : Prop) (h : p2997 ∨ (¬ p1980) ∨ (¬ p2177) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3945)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (p2997) ∨ (¬ p3945) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial19213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2996)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory8469 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule19213 (meaning t m 1980) (meaning t m 2027) (meaning t m 2177) (meaning t m 2641) (meaning t m 2996) (meaning t m 2997) (meaning t m 3945) (meaning t m 3947) source

theorem rule19214 (p1980 p2027 p2641 p2764 p2996 p3947 p4381 : Prop) (h : (¬ p1980) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p3947) ∨ p2764 ∨ (¬ p4381)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2641) ∨ (p2764) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial19214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory8470 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule19214 (meaning t m 1980) (meaning t m 2027) (meaning t m 2641) (meaning t m 2764) (meaning t m 2996) (meaning t m 3947) (meaning t m 4381) source

theorem rule19215 (p1995 p2027 p2938 p2982 p3379 p3834 p4235 p4388 : Prop) (h : (¬ p2982) ∨ (¬ p1995) ∨ (¬ p3379) ∨ (¬ p3834) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p4388) ∨ p2938) : (¬ p1995) ∨ (p2027) ∨ (p2938) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p4235) ∨ (¬ p4388) := by
  classical
  tauto

theorem initial19215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4388)) := by
  have source := ElevenTheory.theory8471 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 9) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9)
  exact rule19215 (meaning t m 1995) (meaning t m 2027) (meaning t m 2938) (meaning t m 2982) (meaning t m 3379) (meaning t m 3834) (meaning t m 4235) (meaning t m 4388) source

theorem rule19218 (p1998 p2027 p2233 p2437 p2470 p2911 p4256 : Prop) (h : p2233 ∨ p2027 ∨ (¬ p4256) ∨ (¬ p2437) ∨ (¬ p2911) ∨ (¬ p1998) ∨ (¬ p2470)) : (¬ p1998) ∨ (p2027) ∨ (p2233) ∨ (¬ p2437) ∨ (¬ p2470) ∨ (¬ p2911) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial19218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory8474 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule19218 (meaning t m 1998) (meaning t m 2027) (meaning t m 2233) (meaning t m 2437) (meaning t m 2470) (meaning t m 2911) (meaning t m 4256) source

theorem rule19219 (p2007 p2027 p2114 p2534 p2737 p2811 p3166 p3256 : Prop) (h : (¬ p2007) ∨ (¬ p2737) ∨ p2114 ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3256)) : (¬ p2007) ∨ (p2027) ∨ (p2114) ∨ (¬ p2534) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3256) := by
  classical
  tauto

theorem initial19219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) := by
  have source := ElevenTheory.theory8475 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule19219 (meaning t m 2007) (meaning t m 2027) (meaning t m 2114) (meaning t m 2534) (meaning t m 2737) (meaning t m 2811) (meaning t m 3166) (meaning t m 3256) source

theorem rule19220 (p1997 p2027 p2114 p2542 p3367 p3641 p4256 : Prop) (h : p2114 ∨ (¬ p1997) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p4256) ∨ (¬ p3641) ∨ (¬ p3367)) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2542) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial19220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory8476 t (m.theta 1 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule19220 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2542) (meaning t m 3367) (meaning t m 3641) (meaning t m 4256) source

theorem rule19223 (p1976 p2027 p2104 p2766 p3979 p4347 p5612 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3979) ∨ p2766 ∨ (¬ p2104) ∨ (¬ p5612)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2104) ∨ (p2766) ∨ (¬ p3979) ∨ (¬ p4347) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial19223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory8479 t (m.theta 0 2) (m.theta 2 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule19223 (meaning t m 1976) (meaning t m 2027) (meaning t m 2104) (meaning t m 2766) (meaning t m 3979) (meaning t m 4347) (meaning t m 5612) source

theorem rule19224 (p1985 p2027 p2210 p2247 p2688 p3527 p3570 p4431 : Prop) (h : (¬ p4431) ∨ (¬ p3527) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p1985) ∨ (¬ p2210) ∨ (¬ p2247) ∨ p2688) : (¬ p1985) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4431) := by
  classical
  tauto

theorem initial19224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4431)) := by
  have source := ElevenTheory.theory8480 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8)
  exact rule19224 (meaning t m 1985) (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2688) (meaning t m 3527) (meaning t m 3570) (meaning t m 4431) source

theorem rule19225 (p2007 p2177 p2997 p4420 : Prop) (h : (¬ p2177) ∨ (¬ p2007) ∨ p2997 ∨ p4420) : (¬ p2007) ∨ (¬ p2177) ∨ (p2997) ∨ (p4420) := by
  classical
  tauto

theorem initial19225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (meaning t m 4420) := by
  have source := ElevenTheory.theory8481 t (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule19225 (meaning t m 2007) (meaning t m 2177) (meaning t m 2997) (meaning t m 4420) source

theorem rule19226 (p2023 p2027 p2997 p3440 p3461 p3483 p3822 p4321 : Prop) (h : p2997 ∨ (¬ p2023) ∨ (¬ p3440) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4321) ∨ p2027 ∨ (¬ p3461)) : (¬ p2023) ∨ (p2027) ∨ (p2997) ∨ (¬ p3440) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial19226 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2023)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3440)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory8482 t (m.theta 1 8) (m.theta 1 9) (m.theta 2 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule19226 (meaning t m 2023) (meaning t m 2027) (meaning t m 2997) (meaning t m 3440) (meaning t m 3461) (meaning t m 3483) (meaning t m 3822) (meaning t m 4321) source

theorem rule19227 (p2005 p2493 p2842 p5214 : Prop) (h : (¬ p2005) ∨ (¬ p2493) ∨ p2842 ∨ p5214) : (¬ p2005) ∨ (¬ p2493) ∨ (p2842) ∨ (p5214) := by
  classical
  tauto

theorem initial19227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2842) ∨ (meaning t m 5214) := by
  have source := ElevenTheory.theory8483 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 6)
  exact rule19227 (meaning t m 2005) (meaning t m 2493) (meaning t m 2842) (meaning t m 5214) source

theorem rule19229 (p2476 p2510 p2573 : Prop) (h : (¬ p2573) ∨ (¬ p2510) ∨ (¬ p2476)) : (¬ p2476) ∨ (¬ p2510) ∨ (¬ p2573) := by
  classical
  tauto

theorem initial19229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2573)) := by
  have source := ElevenTheory.theory8485 (m.theta 0 4) (m.theta 4 6) (m.theta 4 8)
  exact rule19229 (meaning t m 2476) (meaning t m 2510) (meaning t m 2573) source

theorem rule19230 (p1994 p2027 p2417 p2727 p2914 p2996 p3947 : Prop) (h : p2027 ∨ (¬ p2996) ∨ (¬ p2417) ∨ (¬ p3947) ∨ p2914 ∨ (¬ p1994) ∨ (¬ p2727)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2727) ∨ (p2914) ∨ (¬ p2996) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial19230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory8486 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule19230 (meaning t m 1994) (meaning t m 2027) (meaning t m 2417) (meaning t m 2727) (meaning t m 2914) (meaning t m 2996) (meaning t m 3947) source

theorem rule19234 (p1980 p2622 p2641 p2745 : Prop) (h : (¬ p1980) ∨ p2622 ∨ (¬ p2641) ∨ p2745) : (¬ p1980) ∨ (p2622) ∨ (¬ p2641) ∨ (p2745) := by
  classical
  tauto

theorem initial19234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2745) := by
  have source := ElevenTheory.theory8490 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 6)
  exact rule19234 (meaning t m 1980) (meaning t m 2622) (meaning t m 2641) (meaning t m 2745) source

theorem rule19237 (p1994 p2027 p2764 p3574 p3956 p4347 p4444 : Prop) (h : p2027 ∨ (¬ p4347) ∨ (¬ p4444) ∨ p2764 ∨ (¬ p1994) ∨ (¬ p3956) ∨ (¬ p3574)) : (¬ p1994) ∨ (p2027) ∨ (p2764) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial19237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory8493 t (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19237 (meaning t m 1994) (meaning t m 2027) (meaning t m 2764) (meaning t m 3574) (meaning t m 3956) (meaning t m 4347) (meaning t m 4444) source

theorem rule19241 (p1980 p2027 p2641 p2764 p3662 p4208 p4322 : Prop) (h : (¬ p1980) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p4322) ∨ p2764 ∨ (¬ p4208)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2641) ∨ (p2764) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial19241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory8497 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 9) (m.theta 9 10)
  exact rule19241 (meaning t m 1980) (meaning t m 2027) (meaning t m 2641) (meaning t m 2764) (meaning t m 3662) (meaning t m 4208) (meaning t m 4322) source

theorem rule19246 (p2011 p2027 p2563 p2938 p2972 p4173 p4235 : Prop) (h : (¬ p2563) ∨ p2938 ∨ p2027 ∨ (¬ p4235) ∨ (¬ p2011) ∨ (¬ p2972) ∨ (¬ p4173)) : (¬ p2011) ∨ (p2027) ∨ (¬ p2563) ∨ (p2938) ∨ (¬ p2972) ∨ (¬ p4173) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial19246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory8502 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule19246 (meaning t m 2011) (meaning t m 2027) (meaning t m 2563) (meaning t m 2938) (meaning t m 2972) (meaning t m 4173) (meaning t m 4235) source

theorem rule19263 (p3546 p3548 p3551 : Prop) (h : (¬ p3551) ∨ (¬ p3546) ∨ p3548) : (¬ p3546) ∨ (p3548) ∨ (¬ p3551) := by
  classical
  tauto

theorem initial19263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3546)) ∨ (meaning t m 3548) ∨ (¬ (meaning t m 3551)) := by
  have source := ElevenTheory.theory8519 (m.theta 0 7) (m.theta 1 7) (m.theta 7 8)
  exact rule19263 (meaning t m 3546) (meaning t m 3548) (meaning t m 3551) source

theorem rule19273 (p1981 p2027 p2187 p2323 p2641 p2946 p3662 p3986 : Prop) (h : (¬ p2641) ∨ (¬ p3662) ∨ p2027 ∨ p2323 ∨ (¬ p2946) ∨ (¬ p3986) ∨ (¬ p1981) ∨ (¬ p2187)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (p2323) ∨ (¬ p2641) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3986) := by
  classical
  tauto

theorem initial19273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3986)) := by
  have source := ElevenTheory.theory8529 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule19273 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2323) (meaning t m 2641) (meaning t m 2946) (meaning t m 3662) (meaning t m 3986) source

theorem rule19278 (p1992 p2027 p2764 p3688 p3822 p4107 p4381 : Prop) (h : p2027 ∨ p2764 ∨ (¬ p1992) ∨ (¬ p3688) ∨ (¬ p4381) ∨ (¬ p4107) ∨ (¬ p3822)) : (¬ p1992) ∨ (p2027) ∨ (p2764) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial19278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory8534 t (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule19278 (meaning t m 1992) (meaning t m 2027) (meaning t m 2764) (meaning t m 3688) (meaning t m 3822) (meaning t m 4107) (meaning t m 4381) source

theorem rule19289 (p2588 p4137 p4187 : Prop) (h : (¬ p4137) ∨ (¬ p4187) ∨ p2588) : (p2588) ∨ (¬ p4137) ∨ (¬ p4187) := by
  classical
  tauto

theorem initial19289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2588) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4187)) := by
  have source := ElevenTheory.theory8545 (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule19289 (meaning t m 2588) (meaning t m 4137) (meaning t m 4187) source

theorem rule19290 (p1990 p2027 p2169 p2191 p2192 p2363 p3692 : Prop) (h : (¬ p2192) ∨ (¬ p3692) ∨ p2169 ∨ p2027 ∨ (¬ p2363) ∨ (¬ p1990) ∨ (¬ p2191)) : (¬ p1990) ∨ (p2027) ∨ (p2169) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2363) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial19290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory8546 t (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule19290 (meaning t m 1990) (meaning t m 2027) (meaning t m 2169) (meaning t m 2191) (meaning t m 2192) (meaning t m 2363) (meaning t m 3692) source

theorem rule19294 (p1979 p2027 p2352 p2387 p2588 p2997 p3952 p4356 : Prop) (h : (¬ p3952) ∨ (¬ p4356) ∨ p2027 ∨ (¬ p2588) ∨ p2997 ∨ (¬ p2387) ∨ (¬ p2352) ∨ (¬ p1979)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3952) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial19294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory8550 t (m.theta 0 6) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19294 (meaning t m 1979) (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 2588) (meaning t m 2997) (meaning t m 3952) (meaning t m 4356) source

theorem rule19296 (p1978 p2027 p2352 p2387 p3128 p3461 p3746 p4198 p4425 : Prop) (h : (¬ p4198) ∨ (¬ p1978) ∨ (¬ p2387) ∨ (¬ p3461) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p3746) ∨ p3128 ∨ (¬ p2352)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (p3128) ∨ (¬ p3461) ∨ (¬ p3746) ∨ (¬ p4198) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial19296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3746)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory8552 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule19296 (meaning t m 1978) (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 3128) (meaning t m 3461) (meaning t m 3746) (meaning t m 4198) (meaning t m 4425) source

theorem rule19297 (p1998 p2027 p2264 p2699 p3707 p3830 p4429 p5284 : Prop) (h : p2699 ∨ (¬ p3707) ∨ (¬ p2264) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p4429) ∨ (¬ p5284) ∨ (¬ p3830)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2699) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4429) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial19297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory8553 t (m.theta 0 1) (m.theta 1 9) (m.theta 3 7) (m.theta 3 9) (m.theta 7 8) (m.theta 9 10)
  exact rule19297 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2699) (meaning t m 3707) (meaning t m 3830) (meaning t m 4429) (meaning t m 5284) source

theorem rule19298 (p1998 p2027 p2253 p2264 p2699 p3027 p3286 p3848 : Prop) (h : (¬ p2264) ∨ p2699 ∨ (¬ p1998) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p3286) ∨ (¬ p2253) ∨ (¬ p3848)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2264) ∨ (p2699) ∨ (¬ p3027) ∨ (¬ p3286) ∨ (¬ p3848) := by
  classical
  tauto

theorem initial19298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3848)) := by
  have source := ElevenTheory.theory8554 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 7) (m.theta 3 9) (m.theta 7 8)
  exact rule19298 (meaning t m 1998) (meaning t m 2027) (meaning t m 2253) (meaning t m 2264) (meaning t m 2699) (meaning t m 3027) (meaning t m 3286) (meaning t m 3848) source

theorem rule19299 (p2000 p2027 p2187 p2579 p2997 p3097 p3956 : Prop) (h : (¬ p3956) ∨ p2027 ∨ p2997 ∨ (¬ p3097) ∨ (¬ p2000) ∨ (¬ p2579) ∨ (¬ p2187)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2579) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial19299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory8555 t (m.theta 0 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19299 (meaning t m 2000) (meaning t m 2027) (meaning t m 2187) (meaning t m 2579) (meaning t m 2997) (meaning t m 3097) (meaning t m 3956) source

theorem rule19300 (p4067 p4153 p4386 : Prop) (h : (¬ p4067) ∨ p4386 ∨ (¬ p4153)) : (¬ p4067) ∨ (¬ p4153) ∨ (p4386) := by
  classical
  tauto

theorem initial19300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4153)) ∨ (meaning t m 4386) := by
  have source := ElevenTheory.theory8556 (m.theta 3 5) (m.theta 3 6) (m.theta 3 7)
  exact rule19300 (meaning t m 4067) (meaning t m 4153) (meaning t m 4386) source

theorem rule19305 (p2003 p2247 p2688 p5021 : Prop) (h : p5021 ∨ p2688 ∨ (¬ p2247) ∨ (¬ p2003)) : (¬ p2003) ∨ (¬ p2247) ∨ (p2688) ∨ (p5021) := by
  classical
  tauto

theorem initial19305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (meaning t m 5021) := by
  have source := ElevenTheory.theory8561 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3)
  exact rule19305 (meaning t m 2003) (meaning t m 2247) (meaning t m 2688) (meaning t m 5021) source

theorem rule19306 (p1998 p2027 p2247 p2688 p2911 p2922 p3379 : Prop) (h : p2027 ∨ p2688 ∨ (¬ p1998) ∨ (¬ p3379) ∨ (¬ p2247) ∨ (¬ p2922) ∨ (¬ p2911)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial19306 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory8562 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 4 7) (m.theta 7 8)
  exact rule19306 (meaning t m 1998) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 2911) (meaning t m 2922) (meaning t m 3379) source

theorem rule19307 (p2000 p2210 p2699 p4202 p5191 : Prop) (h : (¬ p2210) ∨ p2699 ∨ (¬ p4202) ∨ p5191 ∨ (¬ p2000)) : (¬ p2000) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p4202) ∨ (p5191) := by
  classical
  tauto

theorem initial19307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 4202)) ∨ (meaning t m 5191) := by
  have source := ElevenTheory.theory8563 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 1 5)
  exact rule19307 (meaning t m 2000) (meaning t m 2210) (meaning t m 2699) (meaning t m 4202) (meaning t m 5191) source

theorem rule19308 (p1976 p2027 p2462 p2588 p3055 p3584 p4107 : Prop) (h : p2462 ∨ (¬ p1976) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3584)) : (¬ p1976) ∨ (p2027) ∨ (p2462) ∨ (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial19308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory8564 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule19308 (meaning t m 1976) (meaning t m 2027) (meaning t m 2462) (meaning t m 2588) (meaning t m 3055) (meaning t m 3584) (meaning t m 4107) source

theorem rule19310 (p1994 p2027 p2462 p2578 p2588 p2667 p2727 p4107 p4154 : Prop) (h : p2462 ∨ (¬ p2578) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p4107) ∨ (¬ p2588) ∨ (¬ p1994) ∨ (¬ p2727) ∨ (¬ p2667)) : (¬ p1994) ∨ (p2027) ∨ (p2462) ∨ (¬ p2578) ∨ (¬ p2588) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p4107) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial19310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory8566 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule19310 (meaning t m 1994) (meaning t m 2027) (meaning t m 2462) (meaning t m 2578) (meaning t m 2588) (meaning t m 2667) (meaning t m 2727) (meaning t m 4107) (meaning t m 4154) source

theorem rule19311 (p1992 p2608 p2699 p5117 p5123 : Prop) (h : p2699 ∨ (¬ p2608) ∨ (¬ p1992) ∨ p5123 ∨ (¬ p5117)) : (¬ p1992) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p5117) ∨ (p5123) := by
  classical
  tauto

theorem initial19311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 5117)) ∨ (meaning t m 5123) := by
  have source := ElevenTheory.theory8567 t (m.theta 0 1) (m.theta 1 2) (m.theta 8 10) (m.theta 9 10)
  exact rule19311 (meaning t m 1992) (meaning t m 2608) (meaning t m 2699) (meaning t m 5117) (meaning t m 5123) source

theorem rule19313 (p2001 p2027 p2622 p2850 p3156 p3212 p3475 p4109 p4208 : Prop) (h : p2622 ∨ (¬ p3475) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p4109) ∨ (¬ p3212) ∨ (¬ p2001) ∨ (¬ p3156) ∨ (¬ p4208)) : (¬ p2001) ∨ (p2027) ∨ (p2622) ∨ (¬ p2850) ∨ (¬ p3156) ∨ (¬ p3212) ∨ (¬ p3475) ∨ (¬ p4109) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial19313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory8569 t (m.theta 0 5) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule19313 (meaning t m 2001) (meaning t m 2027) (meaning t m 2622) (meaning t m 2850) (meaning t m 3156) (meaning t m 3212) (meaning t m 3475) (meaning t m 4109) (meaning t m 4208) source

theorem rule19314 (p1985 p2027 p2247 p2688 p2891 p3212 p4172 p4363 : Prop) (h : (¬ p2247) ∨ p2027 ∨ (¬ p3212) ∨ (¬ p4363) ∨ p2688 ∨ (¬ p2891) ∨ (¬ p4172) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p2891) ∨ (¬ p3212) ∨ (¬ p4172) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial19314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory8570 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 5 7) (m.theta 5 9)
  exact rule19314 (meaning t m 1985) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 2891) (meaning t m 3212) (meaning t m 4172) (meaning t m 4363) source

theorem rule19315 (p1982 p2363 p2997 p4405 : Prop) (h : (¬ p2363) ∨ (¬ p1982) ∨ p2997 ∨ p4405) : (¬ p1982) ∨ (¬ p2363) ∨ (p2997) ∨ (p4405) := by
  classical
  tauto

theorem initial19315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2997) ∨ (meaning t m 4405) := by
  have source := ElevenTheory.theory8571 t (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule19315 (meaning t m 1982) (meaning t m 2363) (meaning t m 2997) (meaning t m 4405) source

theorem rule19316 (p3694 p4119 p4244 : Prop) (h : (¬ p4244) ∨ (¬ p4119) ∨ p3694) : (p3694) ∨ (¬ p4119) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial19316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3694) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory8572 (m.theta 2 5) (m.theta 5 7) (m.theta 5 8)
  exact rule19316 (meaning t m 3694) (meaning t m 4119) (meaning t m 4244) source

theorem rule19317 (p1994 p2027 p2573 p2633 p3540 p3574 p3644 : Prop) (h : (¬ p2573) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p3540) ∨ p2633 ∨ (¬ p3644)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2573) ∨ (p2633) ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial19317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory8573 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule19317 (meaning t m 1994) (meaning t m 2027) (meaning t m 2573) (meaning t m 2633) (meaning t m 3540) (meaning t m 3574) (meaning t m 3644) source

theorem rule19318 (p1994 p2027 p2299 p2573 p2633 p3540 p3574 p3921 : Prop) (h : (¬ p3540) ∨ (¬ p1994) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p2573) ∨ p2633 ∨ (¬ p3921) ∨ (¬ p2299)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2573) ∨ (p2633) ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial19318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory8574 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule19318 (meaning t m 1994) (meaning t m 2027) (meaning t m 2299) (meaning t m 2573) (meaning t m 2633) (meaning t m 3540) (meaning t m 3574) (meaning t m 3921) source

theorem rule19321 (p1994 p2027 p2462 p2573 p3540 p3574 p4278 : Prop) (h : (¬ p2573) ∨ (¬ p3540) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p3574) ∨ p2462 ∨ (¬ p4278)) : (¬ p1994) ∨ (p2027) ∨ (p2462) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial19321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory8577 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule19321 (meaning t m 1994) (meaning t m 2027) (meaning t m 2462) (meaning t m 2573) (meaning t m 3540) (meaning t m 3574) (meaning t m 4278) source

theorem rule19322 (p1990 p2027 p2619 p2696 p2699 p2743 p2839 p3589 p3988 : Prop) (h : (¬ p3589) ∨ p2699 ∨ (¬ p2743) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3988) ∨ (¬ p1990) ∨ (¬ p2619)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2619) ∨ (¬ p2696) ∨ (p2699) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3589) ∨ (¬ p3988) := by
  classical
  tauto

theorem initial19322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3988)) := by
  have source := ElevenTheory.theory8578 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8)
  exact rule19322 (meaning t m 1990) (meaning t m 2027) (meaning t m 2619) (meaning t m 2696) (meaning t m 2699) (meaning t m 2743) (meaning t m 2839) (meaning t m 3589) (meaning t m 3988) source

theorem rule19324 (p1976 p2027 p2122 p2588 p3055 p3584 p3586 : Prop) (h : p2027 ∨ (¬ p1976) ∨ (¬ p3584) ∨ (¬ p2588) ∨ (¬ p3055) ∨ p3586 ∨ (¬ p2122)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (p3586) := by
  classical
  tauto

theorem initial19324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3584)) ∨ (meaning t m 3586) := by
  have source := ElevenTheory.theory8580 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule19324 (meaning t m 1976) (meaning t m 2027) (meaning t m 2122) (meaning t m 2588) (meaning t m 3055) (meaning t m 3584) (meaning t m 3586) source

theorem rule19325 (p1988 p2027 p2323 p2761 p2901 p2946 p3246 : Prop) (h : p2027 ∨ p2323 ∨ (¬ p3246) ∨ (¬ p2901) ∨ (¬ p2761) ∨ (¬ p1988) ∨ (¬ p2946)) : (¬ p1988) ∨ (p2027) ∨ (p2323) ∨ (¬ p2761) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial19325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory8581 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule19325 (meaning t m 1988) (meaning t m 2027) (meaning t m 2323) (meaning t m 2761) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) source

theorem rule19326 (p1998 p2027 p2247 p2264 p2688 p3516 p3545 p3947 : Prop) (h : (¬ p3947) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p1998) ∨ p2688 ∨ (¬ p3516) ∨ (¬ p2264) ∨ (¬ p3545)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2264) ∨ (p2688) ∨ (¬ p3516) ∨ (¬ p3545) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial19326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory8582 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule19326 (meaning t m 1998) (meaning t m 2027) (meaning t m 2247) (meaning t m 2264) (meaning t m 2688) (meaning t m 3516) (meaning t m 3545) (meaning t m 3947) source

theorem rule19327 (p4317 p4496 p4512 : Prop) (h : (¬ p4512) ∨ p4317 ∨ (¬ p4496)) : (p4317) ∨ (¬ p4496) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial19327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4317) ∨ (¬ (meaning t m 4496)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory8583 (m.theta 1 5) (m.theta 1 6) (m.theta 1 8)
  exact rule19327 (meaning t m 4317) (meaning t m 4496) (meaning t m 4512) source

theorem rule19331 (p2427 p3051 p4031 : Prop) (h : (¬ p2427) ∨ (¬ p4031) ∨ p3051) : (¬ p2427) ∨ (p3051) ∨ (¬ p4031) := by
  classical
  tauto

theorem initial19331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (meaning t m 3051) ∨ (¬ (meaning t m 4031)) := by
  have source := ElevenTheory.theory8587 (m.theta 0 5) (m.theta 4 5) (m.theta 5 7)
  exact rule19331 (meaning t m 2427) (meaning t m 3051) (meaning t m 4031) source

theorem rule19333 (p2006 p2027 p2132 p2766 p3425 p3570 p4169 p4348 : Prop) (h : (¬ p2006) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p4348) ∨ (¬ p4169) ∨ p2766 ∨ (¬ p3425) ∨ (¬ p2132)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2132) ∨ (p2766) ∨ (¬ p3425) ∨ (¬ p3570) ∨ (¬ p4169) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial19333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory8589 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule19333 (meaning t m 2006) (meaning t m 2027) (meaning t m 2132) (meaning t m 2766) (meaning t m 3425) (meaning t m 3570) (meaning t m 4169) (meaning t m 4348) source

theorem rule19335 (p1978 p2027 p2274 p2313 p2766 p3989 p4198 p4347 : Prop) (h : (¬ p1978) ∨ (¬ p2313) ∨ (¬ p4198) ∨ (¬ p2274) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p3989) ∨ p2766) : (¬ p1978) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (p2766) ∨ (¬ p3989) ∨ (¬ p4198) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial19335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory8591 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule19335 (meaning t m 1978) (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2766) (meaning t m 3989) (meaning t m 4198) (meaning t m 4347) source

theorem rule19337 (p1978 p2027 p2764 p2860 p3646 p4033 p4191 p4385 : Prop) (h : p2027 ∨ (¬ p3646) ∨ p2764 ∨ (¬ p4191) ∨ (¬ p1978) ∨ (¬ p4385) ∨ (¬ p2860) ∨ (¬ p4033)) : (¬ p1978) ∨ (p2027) ∨ (p2764) ∨ (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4033) ∨ (¬ p4191) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial19337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory8593 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule19337 (meaning t m 1978) (meaning t m 2027) (meaning t m 2764) (meaning t m 2860) (meaning t m 3646) (meaning t m 4033) (meaning t m 4191) (meaning t m 4385) source

theorem rule19338 (p2143 p4032 p5030 p5031 : Prop) (h : (¬ p4032) ∨ (¬ p5030) ∨ (¬ p5031) ∨ (¬ p2143)) : (¬ p2143) ∨ (¬ p4032) ∨ (¬ p5030) ∨ (¬ p5031) := by
  classical
  tauto

theorem initial19338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 5030)) ∨ (¬ (meaning t m 5031)) := by
  have source := ElevenTheory.theory8594 (m.theta 0 5) (m.theta 2 5) (m.theta 2 9) (m.theta 5 9)
  exact rule19338 (meaning t m 2143) (meaning t m 4032) (meaning t m 5030) (meaning t m 5031) source

theorem rule19340 (p1987 p2027 p2299 p2633 p2957 p3097 p3646 p4315 : Prop) (h : (¬ p3097) ∨ (¬ p3646) ∨ (¬ p2957) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p4315) ∨ (¬ p2299) ∨ p2633) : (¬ p1987) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial19340 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory8596 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule19340 (meaning t m 1987) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2957) (meaning t m 3097) (meaning t m 3646) (meaning t m 4315) source

theorem rule19341 (p1992 p2027 p2363 p2608 p2997 p3325 p3860 p4261 : Prop) (h : (¬ p1992) ∨ p2997 ∨ (¬ p3860) ∨ (¬ p3325) ∨ (¬ p2608) ∨ (¬ p4261) ∨ p2027 ∨ (¬ p2363)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (p2997) ∨ (¬ p3325) ∨ (¬ p3860) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial19341 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory8597 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule19341 (meaning t m 1992) (meaning t m 2027) (meaning t m 2363) (meaning t m 2608) (meaning t m 2997) (meaning t m 3325) (meaning t m 3860) (meaning t m 4261) source

theorem rule19343 (p2003 p2027 p2122 p2313 p2766 p4138 p4348 p4358 : Prop) (h : p2766 ∨ (¬ p2003) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p4358) ∨ (¬ p4138) ∨ (¬ p2313)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (p2766) ∨ (¬ p4138) ∨ (¬ p4348) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial19343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory8599 t (m.theta 0 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule19343 (meaning t m 2003) (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2766) (meaning t m 4138) (meaning t m 4348) (meaning t m 4358) source

theorem rule19344 (p2007 p2027 p2409 p3449 p3452 p4181 p4286 : Prop) (h : (¬ p2007) ∨ p2409 ∨ (¬ p3452) ∨ p2027 ∨ (¬ p4286) ∨ (¬ p3449) ∨ (¬ p4181)) : (¬ p2007) ∨ (p2027) ∨ (p2409) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4181) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial19344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory8600 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 4 8) (m.theta 8 10)
  exact rule19344 (meaning t m 2007) (meaning t m 2027) (meaning t m 2409) (meaning t m 3449) (meaning t m 3452) (meaning t m 4181) (meaning t m 4286) source

theorem rule19345 (p2003 p2027 p2299 p2313 p2764 p4348 p4444 : Prop) (h : (¬ p2003) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p2299) ∨ (¬ p4348) ∨ (¬ p4444) ∨ p2764) : (¬ p2003) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (p2764) ∨ (¬ p4348) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial19345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory8601 t (m.theta 0 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19345 (meaning t m 2003) (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2764) (meaning t m 4348) (meaning t m 4444) source

theorem rule19347 (p3192 p3875 p4045 : Prop) (h : (¬ p4045) ∨ (¬ p3192) ∨ p3875) : (¬ p3192) ∨ (p3875) ∨ (¬ p4045) := by
  classical
  tauto

theorem initial19347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3192)) ∨ (meaning t m 3875) ∨ (¬ (meaning t m 4045)) := by
  have source := ElevenTheory.theory8603 (m.theta 4 7) (m.theta 4 8) (m.theta 4 9)
  exact rule19347 (meaning t m 3192) (meaning t m 3875) (meaning t m 4045) source

theorem rule19352 (p1992 p2027 p2274 p2608 p2765 p3549 p3591 : Prop) (h : (¬ p2608) ∨ (¬ p1992) ∨ (¬ p3549) ∨ p2027 ∨ (¬ p3591) ∨ p2765 ∨ (¬ p2274)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2608) ∨ (p2765) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial19352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory8608 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule19352 (meaning t m 1992) (meaning t m 2027) (meaning t m 2274) (meaning t m 2608) (meaning t m 2765) (meaning t m 3549) (meaning t m 3591) source

theorem rule19354 (p1981 p2027 p2295 p2323 p2331 p2352 p2588 : Prop) (h : (¬ p1981) ∨ (¬ p2588) ∨ (¬ p2352) ∨ (¬ p2295) ∨ p2323 ∨ (¬ p2331) ∨ p2027) : (¬ p1981) ∨ (p2027) ∨ (¬ p2295) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2352) ∨ (¬ p2588) := by
  classical
  tauto

theorem initial19354 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) := by
  have source := ElevenTheory.theory8610 t (m.theta 0 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19354 (meaning t m 1981) (meaning t m 2027) (meaning t m 2295) (meaning t m 2323) (meaning t m 2331) (meaning t m 2352) (meaning t m 2588) source

theorem rule19355 (p1992 p2210 p2699 p4377 : Prop) (h : p2699 ∨ (¬ p1992) ∨ (¬ p2210) ∨ p4377) : (¬ p1992) ∨ (¬ p2210) ∨ (p2699) ∨ (p4377) := by
  classical
  tauto

theorem initial19355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (meaning t m 4377) := by
  have source := ElevenTheory.theory8611 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5)
  exact rule19355 (meaning t m 1992) (meaning t m 2210) (meaning t m 2699) (meaning t m 4377) source

theorem rule19356 (p2010 p2765 p4110 p4646 : Prop) (h : (¬ p2010) ∨ (¬ p4110) ∨ p2765 ∨ p4646) : (¬ p2010) ∨ (p2765) ∨ (¬ p4110) ∨ (p4646) := by
  classical
  tauto

theorem initial19356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 4110)) ∨ (meaning t m 4646) := by
  have source := ElevenTheory.theory8612 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule19356 (meaning t m 2010) (meaning t m 2765) (meaning t m 4110) (meaning t m 4646) source

theorem rule19357 (p1999 p2027 p2241 p2699 p3506 p3842 p4191 : Prop) (h : (¬ p2241) ∨ (¬ p1999) ∨ p2027 ∨ p2699 ∨ (¬ p4191) ∨ (¬ p3506) ∨ (¬ p3842)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial19357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory8613 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule19357 (meaning t m 1999) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 3506) (meaning t m 3842) (meaning t m 4191) source

theorem rule19358 (p1996 p2027 p2233 p2499 p2573 p2934 p3527 p3553 : Prop) (h : p2233 ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p3553) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p1996) ∨ (¬ p2934)) : (¬ p1996) ∨ (p2027) ∨ (p2233) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2934) ∨ (¬ p3527) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial19358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory8614 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 7) (m.theta 3 7) (m.theta 4 6) (m.theta 7 8)
  exact rule19358 (meaning t m 1996) (meaning t m 2027) (meaning t m 2233) (meaning t m 2499) (meaning t m 2573) (meaning t m 2934) (meaning t m 3527) (meaning t m 3553) source

theorem rule19359 (p1994 p2027 p2230 p2440 p2633 p3540 p3570 p4001 : Prop) (h : (¬ p3540) ∨ (¬ p2230) ∨ p2633 ∨ p2027 ∨ (¬ p3570) ∨ (¬ p4001) ∨ (¬ p1994) ∨ (¬ p2440)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (p2633) ∨ (¬ p3540) ∨ (¬ p3570) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial19359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory8615 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule19359 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2633) (meaning t m 3540) (meaning t m 3570) (meaning t m 4001) source

theorem rule19361 (p1981 p2027 p2528 p2914 p3641 p3876 p4347 : Prop) (h : p2914 ∨ (¬ p3876) ∨ (¬ p2528) ∨ (¬ p1981) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3641)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2528) ∨ (p2914) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial19361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory8617 t (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule19361 (meaning t m 1981) (meaning t m 2027) (meaning t m 2528) (meaning t m 2914) (meaning t m 3641) (meaning t m 3876) (meaning t m 4347) source

theorem rule19366 (p1996 p2027 p2169 p2589 p2608 p2685 p2749 p3842 p3989 p4035 p4110 p5193 : Prop) (h : (¬ p2589) ∨ (¬ p5193) ∨ (¬ p2685) ∨ p2027 ∨ (¬ p1996) ∨ (¬ p3989) ∨ (¬ p2608) ∨ (¬ p4110) ∨ p2169 ∨ (¬ p4035) ∨ (¬ p2749) ∨ (¬ p3842)) : (¬ p1996) ∨ (p2027) ∨ (p2169) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2685) ∨ (¬ p2749) ∨ (¬ p3842) ∨ (¬ p3989) ∨ (¬ p4035) ∨ (¬ p4110) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial19366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory8622 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule19366 (meaning t m 1996) (meaning t m 2027) (meaning t m 2169) (meaning t m 2589) (meaning t m 2608) (meaning t m 2685) (meaning t m 2749) (meaning t m 3842) (meaning t m 3989) (meaning t m 4035) (meaning t m 4110) (meaning t m 5193) source

theorem rule19368 (p1994 p2027 p2459 p2630 p2633 p3572 p3857 p3961 p4155 : Prop) (h : (¬ p1994) ∨ (¬ p3961) ∨ (¬ p2630) ∨ (¬ p3857) ∨ p2027 ∨ (¬ p3572) ∨ p2633 ∨ (¬ p2459) ∨ (¬ p4155)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2630) ∨ (p2633) ∨ (¬ p3572) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial19368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory8624 t (m.theta 0 7) (m.theta 0 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule19368 (meaning t m 1994) (meaning t m 2027) (meaning t m 2459) (meaning t m 2630) (meaning t m 2633) (meaning t m 3572) (meaning t m 3857) (meaning t m 3961) (meaning t m 4155) source

theorem rule19371 (p2024 p2027 p2241 p2641 p2699 p3755 p4195 : Prop) (h : (¬ p2024) ∨ p2699 ∨ (¬ p3755) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p4195) ∨ (¬ p2241)) : (¬ p2024) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (p2699) ∨ (¬ p3755) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial19371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2024)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory8627 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9)
  exact rule19371 (meaning t m 2024) (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 2699) (meaning t m 3755) (meaning t m 4195) source

theorem rule19372 (p1994 p2027 p2633 p2727 p2957 p3556 p3570 p3662 : Prop) (h : (¬ p2957) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p1994) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ p2633) : (¬ p1994) ∨ (p2027) ∨ (p2633) ∨ (¬ p2727) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial19372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory8628 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule19372 (meaning t m 1994) (meaning t m 2027) (meaning t m 2633) (meaning t m 2727) (meaning t m 2957) (meaning t m 3556) (meaning t m 3570) (meaning t m 3662) source

theorem rule19374 (p1997 p2027 p2230 p2766 p3540 p3644 p4348 : Prop) (h : p2027 ∨ (¬ p4348) ∨ (¬ p3644) ∨ (¬ p3540) ∨ p2766 ∨ (¬ p1997) ∨ (¬ p2230)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (p2766) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial19374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory8630 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule19374 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2766) (meaning t m 3540) (meaning t m 3644) (meaning t m 4348) source

theorem rule19376 (p2004 p2202 p2427 p4911 : Prop) (h : (¬ p2427) ∨ (¬ p2004) ∨ p2202 ∨ p4911) : (¬ p2004) ∨ (p2202) ∨ (¬ p2427) ∨ (p4911) := by
  classical
  tauto

theorem initial19376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 4911) := by
  have source := ElevenTheory.theory8632 t (m.theta 1 7) (m.theta 4 5) (m.theta 5 7)
  exact rule19376 (meaning t m 2004) (meaning t m 2202) (meaning t m 2427) (meaning t m 4911) source

theorem rule19378 (p1990 p2699 p3093 p4518 : Prop) (h : (¬ p1990) ∨ p2699 ∨ (¬ p3093) ∨ p4518) : (¬ p1990) ∨ (p2699) ∨ (¬ p3093) ∨ (p4518) := by
  classical
  tauto

theorem initial19378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (meaning t m 4518) := by
  have source := ElevenTheory.theory8634 t (m.theta 0 1) (m.theta 1 6) (m.theta 5 6)
  exact rule19378 (meaning t m 1990) (meaning t m 2699) (meaning t m 3093) (meaning t m 4518) source

theorem rule19381 (p1990 p2027 p2241 p2295 p2641 p2699 p3097 : Prop) (h : (¬ p1990) ∨ (¬ p2295) ∨ p2699 ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3097) ∨ (¬ p2641)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (p2699) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial19381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory8637 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule19381 (meaning t m 1990) (meaning t m 2027) (meaning t m 2241) (meaning t m 2295) (meaning t m 2641) (meaning t m 2699) (meaning t m 3097) source

theorem rule19387 (p1983 p2027 p2177 p2307 p2344 p3246 p3570 : Prop) (h : (¬ p2307) ∨ (¬ p2177) ∨ (¬ p1983) ∨ (¬ p3246) ∨ p2027 ∨ p2344 ∨ (¬ p3570)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (p2344) ∨ (¬ p3246) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial19387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory8643 t (m.theta 0 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule19387 (meaning t m 1983) (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2344) (meaning t m 3246) (meaning t m 3570) source

theorem rule19389 (p1977 p2355 p3662 p4917 : Prop) (h : p2355 ∨ (¬ p1977) ∨ p4917 ∨ (¬ p3662)) : (¬ p1977) ∨ (p2355) ∨ (¬ p3662) ∨ (p4917) := by
  classical
  tauto

theorem initial19389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 3662)) ∨ (meaning t m 4917) := by
  have source := ElevenTheory.theory8645 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 7)
  exact rule19389 (meaning t m 1977) (meaning t m 2355) (meaning t m 3662) (meaning t m 4917) source

theorem rule19390 (p2651 p2946 p4700 : Prop) (h : (¬ p4700) ∨ (¬ p2946) ∨ p2651) : (p2651) ∨ (¬ p2946) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial19390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2651) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory8646 (m.theta 0 3) (m.theta 3 4) (m.theta 3 5)
  exact rule19390 (meaning t m 2651) (meaning t m 2946) (meaning t m 4700) source

theorem rule19393 (p1994 p2630 p3586 p4842 : Prop) (h : (¬ p1994) ∨ p4842 ∨ p3586 ∨ (¬ p2630)) : (¬ p1994) ∨ (¬ p2630) ∨ (p3586) ∨ (p4842) := by
  classical
  tauto

theorem initial19393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 3586) ∨ (meaning t m 4842) := by
  have source := ElevenTheory.theory8649 t (m.theta 2 3) (m.theta 2 6) (m.theta 3 4)
  exact rule19393 (meaning t m 1994) (meaning t m 2630) (meaning t m 3586) (meaning t m 4842) source

theorem rule19394 (p2137 p2951 p4316 : Prop) (h : (¬ p2137) ∨ p2951 ∨ (¬ p4316)) : (¬ p2137) ∨ (p2951) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial19394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (meaning t m 2951) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory8650 (m.theta 0 5) (m.theta 2 5) (m.theta 3 5)
  exact rule19394 (meaning t m 2137) (meaning t m 2951) (meaning t m 4316) source

theorem rule19400 (p1994 p2027 p2630 p2766 p3553 p3572 p4348 : Prop) (h : (¬ p2630) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p3572) ∨ p2766 ∨ (¬ p4348) ∨ (¬ p3553)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p2766) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial19400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory8656 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule19400 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2766) (meaning t m 3553) (meaning t m 3572) (meaning t m 4348) source

theorem rule19402 (p1998 p2027 p2114 p2137 p2156 p2177 p2274 p2839 : Prop) (h : p2114 ∨ (¬ p1998) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2137) ∨ (¬ p2839) ∨ (¬ p2177) ∨ (¬ p2156)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2839) := by
  classical
  tauto

theorem initial19402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2839)) := by
  have source := ElevenTheory.theory8658 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule19402 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2156) (meaning t m 2177) (meaning t m 2274) (meaning t m 2839) source

theorem rule19403 (p1984 p2501 p3008 p3591 : Prop) (h : p2501 ∨ (¬ p1984) ∨ p3008 ∨ (¬ p3591)) : (¬ p1984) ∨ (p2501) ∨ (p3008) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial19403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2501) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory8659 t (m.theta 0 1) (m.theta 1 6) (m.theta 4 6)
  exact rule19403 (meaning t m 1984) (meaning t m 2501) (meaning t m 3008) (meaning t m 3591) source

theorem rule19404 (p2001 p2027 p2641 p2688 p2946 p2963 p3156 : Prop) (h : (¬ p2963) ∨ (¬ p2946) ∨ p2688 ∨ (¬ p2001) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p3156)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3156) := by
  classical
  tauto

theorem initial19404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3156)) := by
  have source := ElevenTheory.theory8660 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8)
  exact rule19404 (meaning t m 2001) (meaning t m 2027) (meaning t m 2641) (meaning t m 2688) (meaning t m 2946) (meaning t m 2963) (meaning t m 3156) source

theorem rule19405 (p1984 p2027 p2191 p2373 p2765 p3555 p4110 : Prop) (h : (¬ p1984) ∨ p2765 ∨ (¬ p4110) ∨ (¬ p2191) ∨ p2027 ∨ (¬ p2373) ∨ (¬ p3555)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2373) ∨ (p2765) ∨ (¬ p3555) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial19405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory8661 t (m.theta 0 1) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule19405 (meaning t m 1984) (meaning t m 2027) (meaning t m 2191) (meaning t m 2373) (meaning t m 2765) (meaning t m 3555) (meaning t m 4110) source

theorem rule19407 (p1995 p2233 p3379 p5190 : Prop) (h : p5190 ∨ (¬ p1995) ∨ (¬ p3379) ∨ p2233) : (¬ p1995) ∨ (p2233) ∨ (¬ p3379) ∨ (p5190) := by
  classical
  tauto

theorem initial19407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 3379)) ∨ (meaning t m 5190) := by
  have source := ElevenTheory.theory8663 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4)
  exact rule19407 (meaning t m 1995) (meaning t m 2233) (meaning t m 3379) (meaning t m 5190) source

theorem rule19409 (p2027 p2313 p2383 p2553 p3324 p4973 : Prop) (h : (¬ p4973) ∨ (¬ p3324) ∨ (¬ p2383) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p2313)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p2553) ∨ (¬ p3324) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial19409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory8665 t (m.theta 0 6) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19409 (meaning t m 2027) (meaning t m 2313) (meaning t m 2383) (meaning t m 2553) (meaning t m 3324) (meaning t m 4973) source

theorem rule19412 (p2098 p3055 p5368 : Prop) (h : (¬ p3055) ∨ (¬ p5368) ∨ (¬ p2098)) : (¬ p2098) ∨ (¬ p3055) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial19412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory8668 (m.theta 0 2) (m.theta 2 4) (m.theta 2 8)
  exact rule19412 (meaning t m 2098) (meaning t m 3055) (meaning t m 5368) source

theorem rule19413 (p1998 p2027 p2137 p2220 p2938 p3969 p4244 p5558 : Prop) (h : p2938 ∨ (¬ p1998) ∨ (¬ p5558) ∨ p2027 ∨ (¬ p3969) ∨ (¬ p2220) ∨ (¬ p4244) ∨ (¬ p2137)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2137) ∨ (¬ p2220) ∨ (p2938) ∨ (¬ p3969) ∨ (¬ p4244) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial19413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory8669 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10)
  exact rule19413 (meaning t m 1998) (meaning t m 2027) (meaning t m 2137) (meaning t m 2220) (meaning t m 2938) (meaning t m 3969) (meaning t m 4244) (meaning t m 5558) source

theorem rule19414 (p2104 p3055 p5368 : Prop) (h : (¬ p3055) ∨ (¬ p5368) ∨ p2104) : (p2104) ∨ (¬ p3055) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial19414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2104) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory8670 (m.theta 0 2) (m.theta 2 4) (m.theta 2 8)
  exact rule19414 (meaning t m 2104) (meaning t m 3055) (meaning t m 5368) source

theorem rule19415 (p1976 p2027 p2476 p2765 p3641 p3684 p3905 p4110 : Prop) (h : (¬ p1976) ∨ (¬ p3684) ∨ p2027 ∨ p2765 ∨ (¬ p4110) ∨ (¬ p3641) ∨ (¬ p2476) ∨ (¬ p3905)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2476) ∨ (p2765) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p3905) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial19415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory8671 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule19415 (meaning t m 1976) (meaning t m 2027) (meaning t m 2476) (meaning t m 2765) (meaning t m 3641) (meaning t m 3684) (meaning t m 3905) (meaning t m 4110) source

theorem rule19417 (p1994 p2027 p2765 p3333 p3359 p3684 p4110 : Prop) (h : (¬ p3684) ∨ p2765 ∨ (¬ p4110) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p3359) ∨ (¬ p3333)) : (¬ p1994) ∨ (p2027) ∨ (p2765) ∨ (¬ p3333) ∨ (¬ p3359) ∨ (¬ p3684) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial19417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory8673 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6)
  exact rule19417 (meaning t m 1994) (meaning t m 2027) (meaning t m 2765) (meaning t m 3333) (meaning t m 3359) (meaning t m 3684) (meaning t m 4110) source

theorem rule19419 (p1976 p2027 p2589 p2766 p3692 p3905 p3969 p4286 p4607 : Prop) (h : (¬ p1976) ∨ (¬ p2589) ∨ (¬ p3905) ∨ (¬ p3969) ∨ p2766 ∨ p2027 ∨ (¬ p4607) ∨ (¬ p4286) ∨ (¬ p3692)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2589) ∨ (p2766) ∨ (¬ p3692) ∨ (¬ p3905) ∨ (¬ p3969) ∨ (¬ p4286) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial19419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory8675 t (m.theta 0 2) (m.theta 0 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule19419 (meaning t m 1976) (meaning t m 2027) (meaning t m 2589) (meaning t m 2766) (meaning t m 3692) (meaning t m 3905) (meaning t m 3969) (meaning t m 4286) (meaning t m 4607) source

theorem rule19420 (p1998 p2027 p2177 p2295 p2765 p3125 p4037 : Prop) (h : p2027 ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p3125) ∨ (¬ p1998) ∨ p2765 ∨ (¬ p4037)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (p2765) ∨ (¬ p3125) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial19420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory8676 t (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule19420 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 2765) (meaning t m 3125) (meaning t m 4037) source

theorem rule19423 (p1995 p2027 p2459 p2534 p2633 p3379 p3860 p4370 : Prop) (h : (¬ p2459) ∨ (¬ p1995) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p3860) ∨ p2633 ∨ (¬ p4370) ∨ (¬ p3379)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4370) := by
  classical
  tauto

theorem initial19423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4370)) := by
  have source := ElevenTheory.theory8679 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule19423 (meaning t m 1995) (meaning t m 2027) (meaning t m 2459) (meaning t m 2534) (meaning t m 2633) (meaning t m 3379) (meaning t m 3860) (meaning t m 4370) source

theorem rule19424 (p2006 p2323 p2946 p4906 : Prop) (h : p4906 ∨ p2323 ∨ (¬ p2946) ∨ (¬ p2006)) : (¬ p2006) ∨ (p2323) ∨ (¬ p2946) ∨ (p4906) := by
  classical
  tauto

theorem initial19424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (meaning t m 4906) := by
  have source := ElevenTheory.theory8680 t (m.theta 0 3) (m.theta 2 5) (m.theta 3 5)
  exact rule19424 (meaning t m 2006) (meaning t m 2323) (meaning t m 2946) (meaning t m 4906) source

theorem rule19425 (p1978 p2611 p2946 p2954 p4117 : Prop) (h : p2954 ∨ p2611 ∨ (¬ p2946) ∨ (¬ p4117) ∨ (¬ p1978)) : (¬ p1978) ∨ (p2611) ∨ (¬ p2946) ∨ (p2954) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial19425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2946)) ∨ (meaning t m 2954) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory8681 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 5)
  exact rule19425 (meaning t m 1978) (meaning t m 2611) (meaning t m 2946) (meaning t m 2954) (meaning t m 4117) source

theorem rule19426 (p1994 p2132 p2611 p2630 p4315 p5053 : Prop) (h : (¬ p4315) ∨ p2611 ∨ p5053 ∨ (¬ p2132) ∨ (¬ p2630) ∨ (¬ p1994)) : (¬ p1994) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p2630) ∨ (¬ p4315) ∨ (p5053) := by
  classical
  tauto

theorem initial19426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 4315)) ∨ (meaning t m 5053) := by
  have source := ElevenTheory.theory8682 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5)
  exact rule19426 (meaning t m 1994) (meaning t m 2132) (meaning t m 2611) (meaning t m 2630) (meaning t m 4315) (meaning t m 5053) source

theorem rule19427 (p1999 p2459 p2633 p4330 : Prop) (h : (¬ p1999) ∨ p2633 ∨ (¬ p2459) ∨ p4330) : (¬ p1999) ∨ (¬ p2459) ∨ (p2633) ∨ (p4330) := by
  classical
  tauto

theorem initial19427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (meaning t m 4330) := by
  have source := ElevenTheory.theory8683 t (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule19427 (meaning t m 1999) (meaning t m 2459) (meaning t m 2633) (meaning t m 4330) source

theorem rule19428 (p2025 p2027 p2764 p3555 p3830 p4322 p4363 : Prop) (h : (¬ p2025) ∨ p2764 ∨ p2027 ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p3830) ∨ (¬ p3555)) : (¬ p2025) ∨ (p2027) ∨ (p2764) ∨ (¬ p3555) ∨ (¬ p3830) ∨ (¬ p4322) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial19428 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2025)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory8684 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 9) (m.theta 5 9) (m.theta 9 10)
  exact rule19428 (meaning t m 2025) (meaning t m 2027) (meaning t m 2764) (meaning t m 3555) (meaning t m 3830) (meaning t m 4322) (meaning t m 4363) source

theorem rule19429 (p1994 p2027 p2630 p3572 p3623 p4075 p4155 p4372 : Prop) (h : (¬ p3572) ∨ p2027 ∨ p3623 ∨ (¬ p4155) ∨ (¬ p4075) ∨ (¬ p1994) ∨ (¬ p2630) ∨ (¬ p4372)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p3572) ∨ (p3623) ∨ (¬ p4075) ∨ (¬ p4155) ∨ (¬ p4372) := by
  classical
  tauto

theorem initial19429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3572)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4372)) := by
  have source := ElevenTheory.theory8685 t (m.theta 0 7) (m.theta 1 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 10)
  exact rule19429 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 3572) (meaning t m 3623) (meaning t m 4075) (meaning t m 4155) (meaning t m 4372) source

theorem rule19431 (p1995 p2027 p2766 p3266 p3379 p3440 p3860 p4321 : Prop) (h : (¬ p4321) ∨ (¬ p3440) ∨ (¬ p3379) ∨ (¬ p3266) ∨ (¬ p3860) ∨ (¬ p1995) ∨ p2027 ∨ p2766) : (¬ p1995) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3379) ∨ (¬ p3440) ∨ (¬ p3860) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial19431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3440)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory8687 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 1 9) (m.theta 8 9) (m.theta 9 10)
  exact rule19431 (meaning t m 1995) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3379) (meaning t m 3440) (meaning t m 3860) (meaning t m 4321) source

theorem rule19432 (p2934 p3379 p4366 : Prop) (h : (¬ p4366) ∨ (¬ p3379) ∨ (¬ p2934)) : (¬ p2934) ∨ (¬ p3379) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial19432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory8688 (m.theta 0 1) (m.theta 1 4) (m.theta 1 7)
  exact rule19432 (meaning t m 2934) (meaning t m 3379) (meaning t m 4366) source

theorem rule19433 (p1995 p2027 p2766 p3379 p3555 p3692 p3880 p4034 : Prop) (h : (¬ p1995) ∨ (¬ p4034) ∨ p2766 ∨ (¬ p3555) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3379)) : (¬ p1995) ∨ (p2027) ∨ (p2766) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4034) := by
  classical
  tauto

theorem initial19433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4034)) := by
  have source := ElevenTheory.theory8689 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule19433 (meaning t m 1995) (meaning t m 2027) (meaning t m 2766) (meaning t m 3379) (meaning t m 3555) (meaning t m 3692) (meaning t m 3880) (meaning t m 4034) source

theorem rule19435 (p1982 p2027 p2166 p2202 p2427 p3146 p3486 : Prop) (h : p2202 ∨ (¬ p2427) ∨ (¬ p1982) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p2166)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2166) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p3146) ∨ (¬ p3486) := by
  classical
  tauto

theorem initial19435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3486)) := by
  have source := ElevenTheory.theory8691 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule19435 (meaning t m 1982) (meaning t m 2027) (meaning t m 2166) (meaning t m 2202) (meaning t m 2427) (meaning t m 3146) (meaning t m 3486) source

theorem rule19436 (p1982 p2027 p2688 p2951 p2992 p3146 p3998 p4238 p5568 : Prop) (h : p2027 ∨ p2688 ∨ (¬ p1982) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p4238) ∨ (¬ p5568) ∨ (¬ p3998)) : (¬ p1982) ∨ (p2027) ∨ (p2688) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p3998) ∨ (¬ p4238) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial19436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4238)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory8692 t (m.theta 0 5) (m.theta 0 8) (m.theta 1 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule19436 (meaning t m 1982) (meaning t m 2027) (meaning t m 2688) (meaning t m 2951) (meaning t m 2992) (meaning t m 3146) (meaning t m 3998) (meaning t m 4238) (meaning t m 5568) source

theorem rule19437 (p2396 p2417 p3921 : Prop) (h : (¬ p3921) ∨ (¬ p2417) ∨ p2396) : (p2396) ∨ (¬ p2417) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial19437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2396) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory8693 (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule19437 (meaning t m 2396) (meaning t m 2417) (meaning t m 3921) source

theorem rule19438 (p1997 p2027 p2114 p2542 p2573 p2663 p2737 p2811 p3574 : Prop) (h : (¬ p2542) ∨ (¬ p1997) ∨ (¬ p3574) ∨ (¬ p2573) ∨ (¬ p2811) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p2663) ∨ p2114) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial19438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory8694 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule19438 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2542) (meaning t m 2573) (meaning t m 2663) (meaning t m 2737) (meaning t m 2811) (meaning t m 3574) source

theorem rule19439 (p3178 p3987 p4114 : Prop) (h : (¬ p3987) ∨ (¬ p4114) ∨ p3178) : (p3178) ∨ (¬ p3987) ∨ (¬ p4114) := by
  classical
  tauto

theorem initial19439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3178) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4114)) := by
  have source := ElevenTheory.theory8695 (m.theta 0 3) (m.theta 0 6) (m.theta 0 8)
  exact rule19439 (meaning t m 3178) (meaning t m 3987) (meaning t m 4114) source

theorem rule19440 (p1994 p2027 p2459 p2630 p2633 p4118 p4195 p4196 : Prop) (h : p2027 ∨ p2633 ∨ (¬ p4195) ∨ (¬ p1994) ∨ (¬ p2459) ∨ (¬ p4118) ∨ (¬ p2630) ∨ (¬ p4196)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2630) ∨ (p2633) ∨ (¬ p4118) ∨ (¬ p4195) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial19440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory8696 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule19440 (meaning t m 1994) (meaning t m 2027) (meaning t m 2459) (meaning t m 2630) (meaning t m 2633) (meaning t m 4118) (meaning t m 4195) (meaning t m 4196) source

theorem rule19441 (p1994 p2027 p2459 p2630 p2633 p3877 p4118 : Prop) (h : p2633 ∨ (¬ p1994) ∨ (¬ p2459) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p3877)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2630) ∨ (p2633) ∨ (¬ p3877) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial19441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory8697 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule19441 (meaning t m 1994) (meaning t m 2027) (meaning t m 2459) (meaning t m 2630) (meaning t m 2633) (meaning t m 3877) (meaning t m 4118) source

theorem rule19442 (p1997 p2027 p2187 p2542 p2765 p3574 p3956 : Prop) (h : p2765 ∨ (¬ p3956) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p1997) ∨ (¬ p2542)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2542) ∨ (p2765) ∨ (¬ p3574) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial19442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory8698 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule19442 (meaning t m 1997) (meaning t m 2027) (meaning t m 2187) (meaning t m 2542) (meaning t m 2765) (meaning t m 3574) (meaning t m 3956) source

theorem rule19443 (p1997 p2027 p2187 p2230 p2765 p3540 p3920 p3956 : Prop) (h : (¬ p2187) ∨ (¬ p3920) ∨ p2765 ∨ (¬ p2230) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p3956) ∨ (¬ p3540)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (p2765) ∨ (¬ p3540) ∨ (¬ p3920) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial19443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory8699 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8)
  exact rule19443 (meaning t m 1997) (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2765) (meaning t m 3540) (meaning t m 3920) (meaning t m 3956) source

theorem rule19444 (p1975 p2202 p2553 p4717 : Prop) (h : (¬ p2553) ∨ (¬ p1975) ∨ p2202 ∨ p4717) : (¬ p1975) ∨ (p2202) ∨ (¬ p2553) ∨ (p4717) := by
  classical
  tauto

theorem initial19444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 4717) := by
  have source := ElevenTheory.theory8700 t (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule19444 (meaning t m 1975) (meaning t m 2202) (meaning t m 2553) (meaning t m 4717) source

theorem rule19447 (p2001 p2534 p2766 p4434 : Prop) (h : (¬ p2001) ∨ p2766 ∨ (¬ p2534) ∨ p4434) : (¬ p2001) ∨ (¬ p2534) ∨ (p2766) ∨ (p4434) := by
  classical
  tauto

theorem initial19447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (meaning t m 4434) := by
  have source := ElevenTheory.theory8703 t (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule19447 (meaning t m 2001) (meaning t m 2534) (meaning t m 2766) (meaning t m 4434) source

theorem rule19451 (p2010 p2633 p3570 p4277 : Prop) (h : (¬ p2010) ∨ p2633 ∨ (¬ p3570) ∨ p4277) : (¬ p2010) ∨ (p2633) ∨ (¬ p3570) ∨ (p4277) := by
  classical
  tauto

theorem initial19451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3570)) ∨ (meaning t m 4277) := by
  have source := ElevenTheory.theory8707 t (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule19451 (meaning t m 2010) (meaning t m 2633) (meaning t m 3570) (meaning t m 4277) source

theorem rule19452 (p1994 p2027 p2331 p2630 p2633 p3172 p4195 p4548 : Prop) (h : (¬ p4195) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p1994) ∨ p2633 ∨ (¬ p4548) ∨ (¬ p3172)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2331) ∨ (¬ p2630) ∨ (p2633) ∨ (¬ p3172) ∨ (¬ p4195) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial19452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory8708 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8) (m.theta 7 8)
  exact rule19452 (meaning t m 1994) (meaning t m 2027) (meaning t m 2331) (meaning t m 2630) (meaning t m 2633) (meaning t m 3172) (meaning t m 4195) (meaning t m 4548) source

theorem rule19456 (p1984 p2027 p2202 p2245 p2563 p2952 p2992 p3745 p4154 : Prop) (h : p2027 ∨ (¬ p2992) ∨ (¬ p2952) ∨ (¬ p1984) ∨ (¬ p2245) ∨ (¬ p2563) ∨ p2202 ∨ (¬ p3745) ∨ (¬ p4154)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2245) ∨ (¬ p2563) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial19456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory8712 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6)
  exact rule19456 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2245) (meaning t m 2563) (meaning t m 2952) (meaning t m 2992) (meaning t m 3745) (meaning t m 4154) source

theorem rule19457 (p1982 p2027 p2098 p2114 p2138 p2839 p3146 p4188 : Prop) (h : (¬ p1982) ∨ (¬ p3146) ∨ (¬ p2138) ∨ p2027 ∨ p2114 ∨ (¬ p2839) ∨ (¬ p4188) ∨ (¬ p2098)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2098) ∨ (p2114) ∨ (¬ p2138) ∨ (¬ p2839) ∨ (¬ p3146) ∨ (¬ p4188) := by
  classical
  tauto

theorem initial19457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4188)) := by
  have source := ElevenTheory.theory8713 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule19457 (meaning t m 1982) (meaning t m 2027) (meaning t m 2098) (meaning t m 2114) (meaning t m 2138) (meaning t m 2839) (meaning t m 3146) (meaning t m 4188) source

theorem rule19459 (p1984 p2027 p2247 p2459 p2633 p4118 p4360 : Prop) (h : (¬ p2247) ∨ p2633 ∨ (¬ p1984) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p2459)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p4118) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial19459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory8715 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule19459 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2459) (meaning t m 2633) (meaning t m 4118) (meaning t m 4360) source

theorem rule19461 (p1988 p2027 p2114 p2137 p2220 p2839 p3146 p3266 : Prop) (h : (¬ p2839) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p2137) ∨ (¬ p3146) ∨ p2114 ∨ (¬ p1988) ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2220) ∨ (¬ p2839) ∨ (¬ p3146) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial19461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory8717 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19461 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2220) (meaning t m 2839) (meaning t m 3146) (meaning t m 3266) source

theorem rule19462 (p1991 p2027 p2657 p2964 p3641 p4256 p5160 : Prop) (h : (¬ p1991) ∨ (¬ p2657) ∨ (¬ p5160) ∨ (¬ p3641) ∨ (¬ p4256) ∨ p2964 ∨ p2027) : (¬ p1991) ∨ (p2027) ∨ (¬ p2657) ∨ (p2964) ∨ (¬ p3641) ∨ (¬ p4256) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial19462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory8718 t (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9)
  exact rule19462 (meaning t m 1991) (meaning t m 2027) (meaning t m 2657) (meaning t m 2964) (meaning t m 3641) (meaning t m 4256) (meaning t m 5160) source

theorem rule19463 (p2245 p4849 p5206 : Prop) (h : (¬ p4849) ∨ (¬ p2245) ∨ p5206) : (¬ p2245) ∨ (¬ p4849) ∨ (p5206) := by
  classical
  tauto

theorem initial19463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 4849)) ∨ (meaning t m 5206) := by
  have source := ElevenTheory.theory8719 (m.theta 0 1) (m.theta 0 3) (m.theta 0 7)
  exact rule19463 (meaning t m 2245) (meaning t m 4849) (meaning t m 5206) source

theorem rule19465 (p1984 p2027 p2247 p2765 p2881 p2996 p3553 p3872 : Prop) (h : (¬ p3553) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p2247) ∨ (¬ p1984) ∨ p2765 ∨ (¬ p3872)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2765) ∨ (¬ p2881) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial19465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory8721 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule19465 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2765) (meaning t m 2881) (meaning t m 2996) (meaning t m 3553) (meaning t m 3872) source

theorem rule19466 (p1984 p2027 p2247 p2274 p2765 p3568 p4154 : Prop) (h : (¬ p2274) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3568) ∨ p2765 ∨ (¬ p2247) ∨ (¬ p4154)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p3568) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial19466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory8722 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule19466 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2274) (meaning t m 2765) (meaning t m 3568) (meaning t m 4154) source

theorem rule19468 (p1982 p2938 p3146 p4904 : Prop) (h : (¬ p3146) ∨ (¬ p1982) ∨ p4904 ∨ p2938) : (¬ p1982) ∨ (p2938) ∨ (¬ p3146) ∨ (p4904) := by
  classical
  tauto

theorem initial19468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 4904) := by
  have source := ElevenTheory.theory8724 t (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule19468 (meaning t m 1982) (meaning t m 2938) (meaning t m 3146) (meaning t m 4904) source

theorem rule19474 (p1987 p2027 p2104 p2696 p3437 p3537 p3588 : Prop) (h : p2027 ∨ (¬ p3588) ∨ (¬ p2696) ∨ (¬ p1987) ∨ (¬ p2104) ∨ p3437 ∨ (¬ p3537)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2104) ∨ (¬ p2696) ∨ (p3437) ∨ (¬ p3537) ∨ (¬ p3588) := by
  classical
  tauto

theorem initial19474 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3588)) := by
  have source := ElevenTheory.theory8730 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 2 8)
  exact rule19474 (meaning t m 1987) (meaning t m 2027) (meaning t m 2104) (meaning t m 2696) (meaning t m 3437) (meaning t m 3537) (meaning t m 3588) source

theorem rule19476 (p2252 p2657 p2727 : Prop) (h : (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2252)) : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2727) := by
  classical
  tauto

theorem initial19476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) := by
  have source := ElevenTheory.theory8732 (m.theta 0 3) (m.theta 1 3) (m.theta 3 4)
  exact rule19476 (meaning t m 2252) (meaning t m 2657) (meaning t m 2727) source

theorem rule19479 (p1988 p2027 p2103 p2459 p3266 p3437 p3537 p3588 p4403 : Prop) (h : (¬ p4403) ∨ p3437 ∨ (¬ p3588) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p3537) ∨ (¬ p2459) ∨ (¬ p2103) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2103) ∨ (¬ p2459) ∨ (¬ p3266) ∨ (p3437) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p4403) := by
  classical
  tauto

theorem initial19479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2103)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3266)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4403)) := by
  have source := ElevenTheory.theory8735 t (m.theta 0 8) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19479 (meaning t m 1988) (meaning t m 2027) (meaning t m 2103) (meaning t m 2459) (meaning t m 3266) (meaning t m 3437) (meaning t m 3537) (meaning t m 3588) (meaning t m 4403) source

theorem rule19483 (p1993 p2027 p2388 p2657 p2727 p3166 p3662 : Prop) (h : (¬ p2657) ∨ (¬ p2727) ∨ p2027 ∨ p2388 ∨ (¬ p3662) ∨ (¬ p3166) ∨ (¬ p1993)) : (¬ p1993) ∨ (p2027) ∨ (p2388) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3166) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial19483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory8739 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 8)
  exact rule19483 (meaning t m 1993) (meaning t m 2027) (meaning t m 2388) (meaning t m 2657) (meaning t m 2727) (meaning t m 3166) (meaning t m 3662) source

theorem rule19484 (p1985 p2027 p2352 p2870 p3008 p3758 p3989 : Prop) (h : (¬ p3989) ∨ p3008 ∨ (¬ p2870) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p1985) ∨ (¬ p3758)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2870) ∨ (p3008) ∨ (¬ p3758) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial19484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2870)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory8740 t (m.theta 2 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule19484 (meaning t m 1985) (meaning t m 2027) (meaning t m 2352) (meaning t m 2870) (meaning t m 3008) (meaning t m 3758) (meaning t m 3989) source

theorem rule19486 (p1984 p2027 p2245 p2657 p2727 p2911 p2914 p4360 p4548 : Prop) (h : p2914 ∨ p2027 ∨ (¬ p4360) ∨ (¬ p1984) ∨ (¬ p2911) ∨ (¬ p2727) ∨ (¬ p4548) ∨ (¬ p2657) ∨ (¬ p2245)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p4360) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial19486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory8742 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 8)
  exact rule19486 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2657) (meaning t m 2727) (meaning t m 2911) (meaning t m 2914) (meaning t m 4360) (meaning t m 4548) source

theorem rule19487 (p1982 p2027 p2437 p2528 p2545 p3641 p3876 : Prop) (h : (¬ p2528) ∨ (¬ p1982) ∨ (¬ p2437) ∨ (¬ p3876) ∨ p2545 ∨ p2027 ∨ (¬ p3641)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2437) ∨ (¬ p2528) ∨ (p2545) ∨ (¬ p3641) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial19487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory8743 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 8 9)
  exact rule19487 (meaning t m 1982) (meaning t m 2027) (meaning t m 2437) (meaning t m 2528) (meaning t m 2545) (meaning t m 3641) (meaning t m 3876) source

theorem rule19488 (p2023 p2027 p2202 p3449 p3585 p3684 p3954 : Prop) (h : p2027 ∨ p2202 ∨ (¬ p2023) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p3585) ∨ (¬ p3684)) : (¬ p2023) ∨ (p2027) ∨ (p2202) ∨ (¬ p3449) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial19488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2023)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory8744 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 2 4) (m.theta 4 5)
  exact rule19488 (meaning t m 2023) (meaning t m 2027) (meaning t m 2202) (meaning t m 3449) (meaning t m 3585) (meaning t m 3684) (meaning t m 3954) source

theorem rule19489 (p3487 p3590 p3683 : Prop) (h : (¬ p3590) ∨ (¬ p3487) ∨ p3683) : (¬ p3487) ∨ (¬ p3590) ∨ (p3683) := by
  classical
  tauto

theorem initial19489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3590)) ∨ (meaning t m 3683) := by
  have source := ElevenTheory.theory8745 (m.theta 1 4) (m.theta 2 4) (m.theta 3 4)
  exact rule19489 (meaning t m 3487) (meaning t m 3590) (meaning t m 3683) source

theorem rule19490 (p2474 p3961 p5197 : Prop) (h : (¬ p3961) ∨ p2474 ∨ (¬ p5197)) : (p2474) ∨ (¬ p3961) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial19490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2474) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory8746 (m.theta 0 4) (m.theta 0 7) (m.theta 0 8)
  exact rule19490 (meaning t m 2474) (meaning t m 3961) (meaning t m 5197) source

theorem rule19491 (p2406 p2928 p3741 : Prop) (h : (¬ p3741) ∨ (¬ p2406) ∨ (¬ p2928)) : (¬ p2406) ∨ (¬ p2928) ∨ (¬ p3741) := by
  classical
  tauto

theorem initial19491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3741)) := by
  have source := ElevenTheory.theory8747 (m.theta 1 4) (m.theta 4 5) (m.theta 4 7)
  exact rule19491 (meaning t m 2406) (meaning t m 2928) (meaning t m 3741) source

theorem rule19492 (p1996 p2437 p2545 p4327 : Prop) (h : (¬ p1996) ∨ p2545 ∨ (¬ p2437) ∨ p4327) : (¬ p1996) ∨ (¬ p2437) ∨ (p2545) ∨ (p4327) := by
  classical
  tauto

theorem initial19492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2545) ∨ (meaning t m 4327) := by
  have source := ElevenTheory.theory8748 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule19492 (meaning t m 1996) (meaning t m 2437) (meaning t m 2545) (meaning t m 4327) source

theorem rule19493 (p3412 p3952 p4338 p4516 : Prop) (h : (¬ p4338) ∨ (¬ p3412) ∨ (¬ p4516) ∨ (¬ p3952)) : (¬ p3412) ∨ (¬ p3952) ∨ (¬ p4338) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial19493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory8749 (m.theta 1 5) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6)
  exact rule19493 (meaning t m 3412) (meaning t m 3952) (meaning t m 4338) (meaning t m 4516) source

theorem rule19494 (p1986 p2027 p2406 p2409 p2589 p3389 p3876 : Prop) (h : (¬ p3389) ∨ (¬ p1986) ∨ (¬ p2406) ∨ p2409 ∨ p2027 ∨ (¬ p2589) ∨ (¬ p3876)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial19494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory8750 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule19494 (meaning t m 1986) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2589) (meaning t m 3389) (meaning t m 3876) source

theorem rule19499 (p1983 p2027 p2202 p2307 p2396 p2493 p2578 p3238 : Prop) (h : p2027 ∨ (¬ p1983) ∨ p2202 ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p3238) ∨ (¬ p2493) ∨ (¬ p2578)) : (¬ p1983) ∨ (p2027) ∨ (p2202) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2493) ∨ (¬ p2578) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial19499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory8755 t (m.theta 0 6) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule19499 (meaning t m 1983) (meaning t m 2027) (meaning t m 2202) (meaning t m 2307) (meaning t m 2396) (meaning t m 2493) (meaning t m 2578) (meaning t m 3238) source

theorem rule19500 (p1981 p2027 p2187 p2295 p2323 p2946 p3097 p4336 : Prop) (h : p2027 ∨ (¬ p2946) ∨ (¬ p2295) ∨ (¬ p4336) ∨ p2323 ∨ (¬ p3097) ∨ (¬ p2187) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2295) ∨ (p2323) ∨ (¬ p2946) ∨ (¬ p3097) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial19500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory8756 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19500 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2295) (meaning t m 2323) (meaning t m 2946) (meaning t m 3097) (meaning t m 4336) source

theorem rule19501 (p1983 p2027 p2230 p2233 p2982 p3680 p4381 : Prop) (h : (¬ p4381) ∨ p2233 ∨ p2027 ∨ (¬ p1983) ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3680)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial19501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory8757 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule19501 (meaning t m 1983) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2982) (meaning t m 3680) (meaning t m 4381) source

theorem rule19502 (p1976 p2027 p2764 p3425 p3659 p4348 p4444 : Prop) (h : (¬ p3659) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p4444) ∨ (¬ p1976) ∨ (¬ p4348) ∨ p2764) : (¬ p1976) ∨ (p2027) ∨ (p2764) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial19502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory8758 t (m.theta 0 2) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19502 (meaning t m 1976) (meaning t m 2027) (meaning t m 2764) (meaning t m 3425) (meaning t m 3659) (meaning t m 4348) (meaning t m 4444) source

theorem rule19503 (p1997 p2027 p2323 p2651 p2850 p3016 p3584 : Prop) (h : (¬ p3016) ∨ p2323 ∨ (¬ p2651) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2850) ∨ (¬ p3584)) : (¬ p1997) ∨ (p2027) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p2850) ∨ (¬ p3016) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial19503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory8759 t (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule19503 (meaning t m 1997) (meaning t m 2027) (meaning t m 2323) (meaning t m 2651) (meaning t m 2850) (meaning t m 3016) (meaning t m 3584) source

theorem rule19506 (p1999 p2027 p2323 p2651 p3016 p3276 p4191 p4422 : Prop) (h : p2027 ∨ (¬ p1999) ∨ (¬ p3016) ∨ (¬ p2651) ∨ p2323 ∨ (¬ p4422) ∨ (¬ p4191) ∨ (¬ p3276)) : (¬ p1999) ∨ (p2027) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3276) ∨ (¬ p4191) ∨ (¬ p4422) := by
  classical
  tauto

theorem initial19506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4422)) := by
  have source := ElevenTheory.theory8762 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule19506 (meaning t m 1999) (meaning t m 2027) (meaning t m 2323) (meaning t m 2651) (meaning t m 3016) (meaning t m 3276) (meaning t m 4191) (meaning t m 4422) source

theorem rule19510 (p2010 p2202 p2427 p4277 : Prop) (h : (¬ p2010) ∨ p2202 ∨ (¬ p2427) ∨ p4277) : (¬ p2010) ∨ (p2202) ∨ (¬ p2427) ∨ (p4277) := by
  classical
  tauto

theorem initial19510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 4277) := by
  have source := ElevenTheory.theory8766 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule19510 (meaning t m 2010) (meaning t m 2202) (meaning t m 2427) (meaning t m 4277) source

theorem rule19511 (p2584 p2663 p3987 : Prop) (h : (¬ p2584) ∨ (¬ p2663) ∨ p3987) : (¬ p2584) ∨ (¬ p2663) ∨ (p3987) := by
  classical
  tauto

theorem initial19511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2663)) ∨ (meaning t m 3987) := by
  have source := ElevenTheory.theory8767 (m.theta 0 3) (m.theta 0 4) (m.theta 0 6)
  exact rule19511 (meaning t m 2584) (meaning t m 2663) (meaning t m 3987) source

theorem rule19512 (p1991 p2027 p2177 p2462 p3414 p3553 p4107 : Prop) (h : (¬ p2177) ∨ p2462 ∨ (¬ p3553) ∨ (¬ p1991) ∨ (¬ p4107) ∨ (¬ p3414) ∨ p2027) : (¬ p1991) ∨ (p2027) ∨ (¬ p2177) ∨ (p2462) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial19512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory8768 t (m.theta 0 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule19512 (meaning t m 1991) (meaning t m 2027) (meaning t m 2177) (meaning t m 2462) (meaning t m 3414) (meaning t m 3553) (meaning t m 4107) source

theorem rule19513 (p1984 p2027 p2245 p2963 p2997 p3063 p3324 p3549 : Prop) (h : (¬ p3324) ∨ p2997 ∨ (¬ p3063) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3549) ∨ (¬ p2245) ∨ (¬ p2963)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3063) ∨ (¬ p3324) ∨ (¬ p3549) := by
  classical
  tauto

theorem initial19513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3549)) := by
  have source := ElevenTheory.theory8769 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19513 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2963) (meaning t m 2997) (meaning t m 3063) (meaning t m 3324) (meaning t m 3549) source

theorem rule19516 (p1998 p2027 p2177 p2274 p2331 p2388 p2952 p3986 : Prop) (h : (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2331) ∨ (¬ p1998) ∨ (¬ p3986) ∨ p2027 ∨ p2388 ∨ (¬ p2952)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2331) ∨ (p2388) ∨ (¬ p2952) ∨ (¬ p3986) := by
  classical
  tauto

theorem initial19516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3986)) := by
  have source := ElevenTheory.theory8772 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule19516 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 2331) (meaning t m 2388) (meaning t m 2952) (meaning t m 3986) source

end SunPrize.SMT
