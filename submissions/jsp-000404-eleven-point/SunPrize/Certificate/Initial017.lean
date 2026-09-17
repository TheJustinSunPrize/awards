import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory007
import SunPrize.Certificate.Theory008
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule10102 (p2027 p2745 p3609 p4118 p4360 p4373 : Prop) (h : (¬ p4118) ∨ (¬ p2745) ∨ (¬ p4360) ∨ (¬ p4373) ∨ p2027 ∨ (¬ p3609)) : (p2027) ∨ (¬ p2745) ∨ (¬ p3609) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4373) := by
  classical
  tauto

theorem initial10102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4373)) := by
  have source := ElevenTheory.theory1774 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule10102 (meaning t m 2027) (meaning t m 2745) (meaning t m 3609) (meaning t m 4118) (meaning t m 4360) (meaning t m 4373) source

theorem rule10103 (p2027 p2363 p2518 p2531 p3193 p4433 p4440 : Prop) (h : (¬ p3193) ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p2531) ∨ (¬ p4433) ∨ p2027 ∨ (¬ p4440)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p2531) ∨ (¬ p3193) ∨ (¬ p4433) ∨ (¬ p4440) := by
  classical
  tauto

theorem initial10103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4440)) := by
  have source := ElevenTheory.theory1775 t (m.theta 1 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule10103 (meaning t m 2027) (meaning t m 2363) (meaning t m 2518) (meaning t m 2531) (meaning t m 3193) (meaning t m 4433) (meaning t m 4440) source

theorem rule10104 (p2027 p2589 p3233 p3347 p3707 p4425 p4953 : Prop) (h : (¬ p3707) ∨ (¬ p3347) ∨ (¬ p3233) ∨ (¬ p4953) ∨ (¬ p2589) ∨ (¬ p4425) ∨ p2027) : (p2027) ∨ (¬ p2589) ∨ (¬ p3233) ∨ (¬ p3347) ∨ (¬ p3707) ∨ (¬ p4425) ∨ (¬ p4953) := by
  classical
  tauto

theorem initial10104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3233)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4953)) := by
  have source := ElevenTheory.theory1776 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 9) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule10104 (meaning t m 2027) (meaning t m 2589) (meaning t m 3233) (meaning t m 3347) (meaning t m 3707) (meaning t m 4425) (meaning t m 4953) source

theorem rule10105 (p2027 p2608 p2737 p4366 p4424 p4778 : Prop) (h : (¬ p4424) ∨ (¬ p4366) ∨ (¬ p4778) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2737)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p4778) := by
  classical
  tauto

theorem initial10105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4778)) := by
  have source := ElevenTheory.theory1777 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7)
  exact rule10105 (meaning t m 2027) (meaning t m 2608) (meaning t m 2737) (meaning t m 4366) (meaning t m 4424) (meaning t m 4778) source

theorem rule10106 (p2027 p2396 p3027 p3297 p3848 p4570 p5295 : Prop) (h : p2027 ∨ (¬ p3297) ∨ (¬ p5295) ∨ (¬ p3027) ∨ (¬ p3848) ∨ (¬ p4570) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3027) ∨ (¬ p3297) ∨ (¬ p3848) ∨ (¬ p4570) ∨ (¬ p5295) := by
  classical
  tauto

theorem initial10106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3297)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 5295)) := by
  have source := ElevenTheory.theory1778 t (m.theta 0 9) (m.theta 1 3) (m.theta 3 7) (m.theta 3 9) (m.theta 6 7) (m.theta 7 9)
  exact rule10106 (meaning t m 2027) (meaning t m 2396) (meaning t m 3027) (meaning t m 3297) (meaning t m 3848) (meaning t m 4570) (meaning t m 5295) source

theorem rule10107 (p2027 p2252 p2396 p3027 p3292 p4570 p4656 : Prop) (h : p2027 ∨ (¬ p4570) ∨ (¬ p2396) ∨ (¬ p3027) ∨ (¬ p4656) ∨ (¬ p2252) ∨ (¬ p3292)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p3027) ∨ (¬ p3292) ∨ (¬ p4570) ∨ (¬ p4656) := by
  classical
  tauto

theorem initial10107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 4656)) := by
  have source := ElevenTheory.theory1779 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 7) (m.theta 3 9) (m.theta 6 7) (m.theta 7 9)
  exact rule10107 (meaning t m 2027) (meaning t m 2252) (meaning t m 2396) (meaning t m 3027) (meaning t m 3292) (meaning t m 4570) (meaning t m 4656) source

theorem rule10108 (p2027 p2241 p2992 p3452 p4116 p4704 : Prop) (h : (¬ p3452) ∨ (¬ p4116) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p4704) ∨ (¬ p2992)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial10108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory1780 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5)
  exact rule10108 (meaning t m 2027) (meaning t m 2241) (meaning t m 2992) (meaning t m 3452) (meaning t m 4116) (meaning t m 4704) source

theorem rule10110 (p2027 p2352 p2363 p3692 p3988 p4718 : Prop) (h : (¬ p2363) ∨ (¬ p2352) ∨ (¬ p4718) ∨ p2027 ∨ (¬ p3988) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial10110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory1782 t (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule10110 (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 3692) (meaning t m 3988) (meaning t m 4718) source

theorem rule10111 (p2027 p2191 p2192 p2352 p4506 p4718 : Prop) (h : (¬ p2192) ∨ (¬ p4718) ∨ (¬ p2352) ∨ (¬ p4506) ∨ p2027 ∨ (¬ p2191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2352) ∨ (¬ p4506) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial10111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 4506)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory1783 t (m.theta 1 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule10111 (meaning t m 2027) (meaning t m 2191) (meaning t m 2192) (meaning t m 2352) (meaning t m 4506) (meaning t m 4718) source

theorem rule10112 (p2027 p2396 p2553 p3690 p4204 p4718 : Prop) (h : p2027 ∨ (¬ p2396) ∨ (¬ p4718) ∨ (¬ p3690) ∨ (¬ p4204) ∨ (¬ p2553)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p3690) ∨ (¬ p4204) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial10112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory1784 t (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule10112 (meaning t m 2027) (meaning t m 2396) (meaning t m 2553) (meaning t m 3690) (meaning t m 4204) (meaning t m 4718) source

theorem rule10113 (p2027 p2406 p2474 p2528 p3347 p3857 p4608 : Prop) (h : (¬ p2474) ∨ (¬ p3347) ∨ (¬ p2406) ∨ (¬ p4608) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p3857)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2474) ∨ (¬ p2528) ∨ (¬ p3347) ∨ (¬ p3857) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial10113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2474)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory1785 t (m.theta 0 4) (m.theta 0 8) (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule10113 (meaning t m 2027) (meaning t m 2406) (meaning t m 2474) (meaning t m 2528) (meaning t m 3347) (meaning t m 3857) (meaning t m 4608) source

theorem rule10114 (p3189 p4360 : Prop) (h : (¬ p4360) ∨ (¬ p3189)) : (¬ p3189) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial10114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory1786 (m.theta 1 3) (m.theta 3 8)
  exact rule10114 (meaning t m 3189) (meaning t m 4360) source

theorem rule10115 (p2027 p2518 p3146 p3193 p4158 p4440 : Prop) (h : (¬ p2518) ∨ (¬ p4158) ∨ (¬ p3146) ∨ (¬ p4440) ∨ (¬ p3193) ∨ p2027) : (p2027) ∨ (¬ p2518) ∨ (¬ p3146) ∨ (¬ p3193) ∨ (¬ p4158) ∨ (¬ p4440) := by
  classical
  tauto

theorem initial10115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 4158)) ∨ (¬ (meaning t m 4440)) := by
  have source := ElevenTheory.theory1787 t (m.theta 1 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule10115 (meaning t m 2027) (meaning t m 2518) (meaning t m 3146) (meaning t m 3193) (meaning t m 4158) (meaning t m 4440) source

theorem rule10116 (p2027 p3146 p3857 p3961 p4063 p4132 p5564 : Prop) (h : (¬ p4132) ∨ (¬ p3857) ∨ (¬ p4063) ∨ p2027 ∨ (¬ p5564) ∨ (¬ p3146) ∨ (¬ p3961)) : (p2027) ∨ (¬ p3146) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4063) ∨ (¬ p4132) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial10116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4063)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory1788 t (m.theta 0 7) (m.theta 0 8) (m.theta 5 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule10116 (meaning t m 2027) (meaning t m 3146) (meaning t m 3857) (meaning t m 3961) (meaning t m 4063) (meaning t m 4132) (meaning t m 5564) source

theorem rule10117 (p4139 p4141 p5660 p5661 p5662 : Prop) : (p4141) ∨ (¬ (p4141 ∧ p4139 ∧ p5660 ∧ p5661 ∧ p5662)) := by
  classical
  tauto

theorem initial10117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4141) ∨ (¬ (meaning t m 5659)) := by
  exact rule10117 (meaning t m 4139) (meaning t m 4141) (meaning t m 5660) (meaning t m 5661) (meaning t m 5662)

theorem rule10118 (p4139 p4141 p5660 p5661 p5662 : Prop) : (p4139) ∨ (¬ (p4141 ∧ p4139 ∧ p5660 ∧ p5661 ∧ p5662)) := by
  classical
  tauto

theorem initial10118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4139) ∨ (¬ (meaning t m 5659)) := by
  exact rule10118 (meaning t m 4139) (meaning t m 4141) (meaning t m 5660) (meaning t m 5661) (meaning t m 5662)

theorem rule10119 (p4139 p4141 p5660 p5661 p5662 : Prop) : (¬ (p4141 ∧ p4139 ∧ p5660 ∧ p5661 ∧ p5662)) ∨ (p5660) := by
  classical
  tauto

theorem initial10119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5659)) ∨ (meaning t m 5660) := by
  exact rule10119 (meaning t m 4139) (meaning t m 4141) (meaning t m 5660) (meaning t m 5661) (meaning t m 5662)

theorem rule10120 (p4139 p4141 p5660 p5661 p5662 : Prop) : (¬ (p4141 ∧ p4139 ∧ p5660 ∧ p5661 ∧ p5662)) ∨ (p5661) := by
  classical
  tauto

theorem initial10120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5659)) ∨ (meaning t m 5661) := by
  exact rule10120 (meaning t m 4139) (meaning t m 4141) (meaning t m 5660) (meaning t m 5661) (meaning t m 5662)

theorem rule10121 (p4139 p4141 p5660 p5661 p5662 : Prop) : (¬ (p4141 ∧ p4139 ∧ p5660 ∧ p5661 ∧ p5662)) ∨ (p5662) := by
  classical
  tauto

theorem initial10121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5659)) ∨ (meaning t m 5662) := by
  exact rule10121 (meaning t m 4139) (meaning t m 4141) (meaning t m 5660) (meaning t m 5661) (meaning t m 5662)

theorem rule10122 (p4139 p4141 p5660 p5661 p5662 : Prop) : (¬ p4139) ∨ (¬ p4141) ∨ ((p4141 ∧ p4139 ∧ p5660 ∧ p5661 ∧ p5662)) ∨ (¬ p5660) ∨ (¬ p5661) ∨ (¬ p5662) := by
  classical
  tauto

theorem initial10122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4139)) ∨ (¬ (meaning t m 4141)) ∨ (meaning t m 5659) ∨ (¬ (meaning t m 5660)) ∨ (¬ (meaning t m 5661)) ∨ (¬ (meaning t m 5662)) := by
  exact rule10122 (meaning t m 4139) (meaning t m 4141) (meaning t m 5660) (meaning t m 5661) (meaning t m 5662)

theorem rule10125 (p4129 p5664 p5665 p5666 p5667 : Prop) : (p4129) ∨ (¬ (p5664 ∧ p5665 ∧ p4129 ∧ p5666 ∧ p5667)) := by
  classical
  tauto

theorem initial10125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4129) ∨ (¬ (meaning t m 5663)) := by
  exact rule10125 (meaning t m 4129) (meaning t m 5664) (meaning t m 5665) (meaning t m 5666) (meaning t m 5667)

theorem rule10131 (p5659 p5663 : Prop) : (¬ (p5659 ∨ p5663)) ∨ (p5659) ∨ (p5663) := by
  classical
  tauto

theorem initial10131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5658)) ∨ (meaning t m 5659) ∨ (meaning t m 5663) := by
  exact rule10131 (meaning t m 5659) (meaning t m 5663)

theorem rule10132 (p4123 p5658 : Prop) (h : (p4123 ↔ p5658)) : (¬ p4123) ∨ (p5658) := by
  classical
  tauto

theorem initial10132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4123)) ∨ (meaning t m 5658) := by
  have source := ElevenTheory.theory1789 t (m.theta 5 10) (m.theta 5 7) (m.theta 7 10)
  exact rule10132 (meaning t m 4123) (meaning t m 5658) source

theorem rule10134 (p2027 p2299 p3146 p3747 p4348 p4559 : Prop) (h : (¬ p4559) ∨ (¬ p3747) ∨ (¬ p4348) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p4348) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial10134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory1790 t (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule10134 (meaning t m 2027) (meaning t m 2299) (meaning t m 3146) (meaning t m 3747) (meaning t m 4348) (meaning t m 4559) source

theorem rule10135 (p2027 p2579 p3389 p4137 p4620 p4710 : Prop) (h : (¬ p4710) ∨ (¬ p3389) ∨ p2027 ∨ (¬ p4620) ∨ (¬ p4137) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4137) ∨ (¬ p4620) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial10135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory1791 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9)
  exact rule10135 (meaning t m 2027) (meaning t m 2579) (meaning t m 3389) (meaning t m 4137) (meaning t m 4620) (meaning t m 4710) source

theorem rule10136 (p2027 p2299 p3747 p3969 p4559 p5558 : Prop) (h : (¬ p4559) ∨ (¬ p2299) ∨ (¬ p5558) ∨ (¬ p3969) ∨ (¬ p3747) ∨ p2027) : (p2027) ∨ (¬ p2299) ∨ (¬ p3747) ∨ (¬ p3969) ∨ (¬ p4559) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial10136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory1792 t (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule10136 (meaning t m 2027) (meaning t m 2299) (meaning t m 3747) (meaning t m 3969) (meaning t m 4559) (meaning t m 5558) source

theorem rule10137 (p2027 p2881 p3941 p3955 p4559 p5580 : Prop) (h : (¬ p3955) ∨ (¬ p5580) ∨ p2027 ∨ (¬ p4559) ∨ (¬ p2881) ∨ (¬ p3941)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3941) ∨ (¬ p3955) ∨ (¬ p4559) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial10137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory1793 t (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule10137 (meaning t m 2027) (meaning t m 2881) (meaning t m 3941) (meaning t m 3955) (meaning t m 4559) (meaning t m 5580) source

theorem rule10138 (p2027 p2104 p2881 p3471 p4800 p4895 : Prop) (h : (¬ p4895) ∨ (¬ p2881) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p4800) ∨ (¬ p2104)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2881) ∨ (¬ p3471) ∨ (¬ p4800) ∨ (¬ p4895) := by
  classical
  tauto

theorem initial10138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4800)) ∨ (¬ (meaning t m 4895)) := by
  have source := ElevenTheory.theory1794 t (m.theta 0 2) (m.theta 2 7) (m.theta 2 8) (m.theta 5 7) (m.theta 7 8)
  exact rule10138 (meaning t m 2027) (meaning t m 2104) (meaning t m 2881) (meaning t m 3471) (meaning t m 4800) (meaning t m 4895) source

theorem rule10139 (p2027 p3212 p3556 p4107 p4135 p4559 : Prop) (h : (¬ p4135) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p3212) ∨ (¬ p4559) ∨ (¬ p3556)) : (p2027) ∨ (¬ p3212) ∨ (¬ p3556) ∨ (¬ p4107) ∨ (¬ p4135) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial10139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory1795 t (m.theta 0 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule10139 (meaning t m 2027) (meaning t m 3212) (meaning t m 3556) (meaning t m 4107) (meaning t m 4135) (meaning t m 4559) source

theorem rule10140 (p2027 p2717 p3690 p3941 p4169 p4445 p5122 : Prop) (h : (¬ p4445) ∨ (¬ p4169) ∨ (¬ p3941) ∨ (¬ p3690) ∨ (¬ p2717) ∨ (¬ p5122) ∨ p2027) : (p2027) ∨ (¬ p2717) ∨ (¬ p3690) ∨ (¬ p3941) ∨ (¬ p4169) ∨ (¬ p4445) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial10140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory1796 t (m.theta 2 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10) (m.theta 8 9)
  exact rule10140 (meaning t m 2027) (meaning t m 2717) (meaning t m 3690) (meaning t m 3941) (meaning t m 4169) (meaning t m 4445) (meaning t m 5122) source

theorem rule10141 (p2027 p2509 p2881 p2922 p4277 p4383 : Prop) (h : (¬ p2881) ∨ p2027 ∨ (¬ p2509) ∨ (¬ p2922) ∨ (¬ p4383) ∨ (¬ p4277)) : (p2027) ∨ (¬ p2509) ∨ (¬ p2881) ∨ (¬ p2922) ∨ (¬ p4277) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial10141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory1797 t (m.theta 1 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule10141 (meaning t m 2027) (meaning t m 2509) (meaning t m 2881) (meaning t m 2922) (meaning t m 4277) (meaning t m 4383) source

theorem rule10142 (p2027 p2437 p3574 p4137 p4620 p4710 : Prop) (h : (¬ p4137) ∨ (¬ p2437) ∨ (¬ p3574) ∨ (¬ p4710) ∨ (¬ p4620) ∨ p2027) : (p2027) ∨ (¬ p2437) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4620) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial10142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory1798 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9)
  exact rule10142 (meaning t m 2027) (meaning t m 2437) (meaning t m 3574) (meaning t m 4137) (meaning t m 4620) (meaning t m 4710) source

theorem rule10143 (p2027 p2553 p3246 p4137 p4396 p4559 : Prop) (h : (¬ p4559) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p4137) ∨ (¬ p4396) ∨ (¬ p2553)) : (p2027) ∨ (¬ p2553) ∨ (¬ p3246) ∨ (¬ p4137) ∨ (¬ p4396) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial10143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory1799 t (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule10143 (meaning t m 2027) (meaning t m 2553) (meaning t m 3246) (meaning t m 4137) (meaning t m 4396) (meaning t m 4559) source

theorem rule10144 (p2027 p3556 p3741 p3868 p4533 p5660 : Prop) (h : (¬ p4533) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p3741) ∨ (¬ p5660) ∨ (¬ p3868)) : (p2027) ∨ (¬ p3556) ∨ (¬ p3741) ∨ (¬ p3868) ∨ (¬ p4533) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial10144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4533)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory1800 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 10)
  exact rule10144 (meaning t m 2027) (meaning t m 3556) (meaning t m 3741) (meaning t m 3868) (meaning t m 4533) (meaning t m 5660) source

theorem rule10145 (p2027 p2563 p3389 p3646 p3904 p4646 : Prop) (h : p2027 ∨ (¬ p3646) ∨ (¬ p2563) ∨ (¬ p3389) ∨ (¬ p3904) ∨ (¬ p4646)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3389) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial10145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory1801 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule10145 (meaning t m 2027) (meaning t m 2563) (meaning t m 3389) (meaning t m 3646) (meaning t m 3904) (meaning t m 4646) source

theorem rule10147 (p2027 p3073 p3692 p4119 p4140 p4317 p4435 p5472 : Prop) (h : (¬ p4119) ∨ (¬ p4317) ∨ (¬ p3692) ∨ (¬ p4140) ∨ (¬ p4435) ∨ (¬ p3073) ∨ (¬ p5472) ∨ p2027) : (p2027) ∨ (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4140) ∨ (¬ p4317) ∨ (¬ p4435) ∨ (¬ p5472) := by
  classical
  tauto

theorem initial10147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4317)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 5472)) := by
  have source := ElevenTheory.theory1803 t (m.theta 1 6) (m.theta 1 8) (m.theta 5 7) (m.theta 5 8) (m.theta 6 10) (m.theta 6 7) (m.theta 8 9)
  exact rule10147 (meaning t m 2027) (meaning t m 3073) (meaning t m 3692) (meaning t m 4119) (meaning t m 4140) (meaning t m 4317) (meaning t m 4435) (meaning t m 5472) source

theorem rule10148 (p2027 p2253 p2331 p2741 p3452 p4154 p4376 : Prop) (h : (¬ p2331) ∨ (¬ p4154) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2741) ∨ (¬ p2253)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2741) ∨ (¬ p3452) ∨ (¬ p4154) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial10148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory1804 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 6)
  exact rule10148 (meaning t m 2027) (meaning t m 2253) (meaning t m 2331) (meaning t m 2741) (meaning t m 3452) (meaning t m 4154) (meaning t m 4376) source

theorem rule10150 (p2027 p2313 p2667 p3189 p4154 p4405 p4417 : Prop) (h : (¬ p3189) ∨ (¬ p4417) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p2667) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (¬ p3189) ∨ (¬ p4154) ∨ (¬ p4405) ∨ (¬ p4417) := by
  classical
  tauto

theorem initial10150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4417)) := by
  have source := ElevenTheory.theory1806 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7) (m.theta 6 8)
  exact rule10150 (meaning t m 2027) (meaning t m 2313) (meaning t m 2667) (meaning t m 3189) (meaning t m 4154) (meaning t m 4405) (meaning t m 4417) source

theorem rule10152 (p2027 p2553 p3016 p3359 p4022 p4620 : Prop) (h : (¬ p2553) ∨ (¬ p4022) ∨ p2027 ∨ (¬ p4620) ∨ (¬ p3359) ∨ (¬ p3016)) : (p2027) ∨ (¬ p2553) ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p4022) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial10152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory1808 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 9)
  exact rule10152 (meaning t m 2027) (meaning t m 2553) (meaning t m 3016) (meaning t m 3359) (meaning t m 4022) (meaning t m 4620) source

theorem rule10155 (p4286 p4287 p5670 p5671 p5672 : Prop) : (p4286) ∨ (¬ (p4287 ∧ p5670 ∧ p4286 ∧ p5671 ∧ p5672)) := by
  classical
  tauto

theorem initial10155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4286) ∨ (¬ (meaning t m 5669)) := by
  exact rule10155 (meaning t m 4286) (meaning t m 4287) (meaning t m 5670) (meaning t m 5671) (meaning t m 5672)

theorem rule10161 (p4149 p4239 p5674 p5675 p5676 : Prop) : (p4149) ∨ (¬ (p5674 ∧ p4239 ∧ p4149 ∧ p5675 ∧ p5676)) := by
  classical
  tauto

theorem initial10161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4149) ∨ (¬ (meaning t m 5673)) := by
  exact rule10161 (meaning t m 4149) (meaning t m 4239) (meaning t m 5674) (meaning t m 5675) (meaning t m 5676)

theorem rule10167 (p5669 p5673 : Prop) : (¬ (p5669 ∨ p5673)) ∨ (p5669) ∨ (p5673) := by
  classical
  tauto

theorem initial10167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5668)) ∨ (meaning t m 5669) ∨ (meaning t m 5673) := by
  exact rule10167 (meaning t m 5669) (meaning t m 5673)

theorem rule10168 (p4143 p5668 : Prop) (h : (p4143 ↔ p5668)) : (¬ p4143) ∨ (p5668) := by
  classical
  tauto

theorem initial10168 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4143)) ∨ (meaning t m 5668) := by
  have source := ElevenTheory.theory1809 t (m.theta 4 10) (m.theta 4 8) (m.theta 8 10)
  exact rule10168 (meaning t m 4143) (meaning t m 5668) source

theorem rule10171 (p2027 p2745 p2860 p2957 p3646 p3662 p4313 : Prop) (h : (¬ p3646) ∨ (¬ p4313) ∨ (¬ p2745) ∨ (¬ p2957) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p2860)) : (p2027) ∨ (¬ p2745) ∨ (¬ p2860) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p4313) := by
  classical
  tauto

theorem initial10171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4313)) := by
  have source := ElevenTheory.theory1811 t (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule10171 (meaning t m 2027) (meaning t m 2745) (meaning t m 2860) (meaning t m 2957) (meaning t m 3646) (meaning t m 3662) (meaning t m 4313) source

theorem rule10174 (p2027 p3051 p3646 p3744 p4140 p4620 : Prop) (h : p2027 ∨ (¬ p3646) ∨ (¬ p4620) ∨ (¬ p3744) ∨ (¬ p4140) ∨ (¬ p3051)) : (p2027) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4140) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial10174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory1814 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9)
  exact rule10174 (meaning t m 2027) (meaning t m 3051) (meaning t m 3646) (meaning t m 3744) (meaning t m 4140) (meaning t m 4620) source

theorem rule10176 (p2027 p2579 p3097 p3389 p4710 p4718 : Prop) (h : (¬ p4718) ∨ (¬ p3389) ∨ (¬ p2579) ∨ (¬ p3097) ∨ (¬ p4710) ∨ p2027) : (p2027) ∨ (¬ p2579) ∨ (¬ p3097) ∨ (¬ p3389) ∨ (¬ p4710) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial10176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory1816 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7)
  exact rule10176 (meaning t m 2027) (meaning t m 2579) (meaning t m 3097) (meaning t m 3389) (meaning t m 4710) (meaning t m 4718) source

theorem rule10177 (p2027 p2717 p3399 p3551 p3820 p3873 p4794 : Prop) (h : p2027 ∨ (¬ p4794) ∨ (¬ p2717) ∨ (¬ p3820) ∨ (¬ p3399) ∨ (¬ p3873) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3399) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p3873) ∨ (¬ p4794) := by
  classical
  tauto

theorem initial10177 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4794)) := by
  have source := ElevenTheory.theory1817 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 7) (m.theta 1 7) (m.theta 2 7) (m.theta 7 8)
  exact rule10177 (meaning t m 2027) (meaning t m 2717) (meaning t m 3399) (meaning t m 3551) (meaning t m 3820) (meaning t m 3873) (meaning t m 4794) source

theorem rule10178 (p2027 p2717 p2745 p3553 p3662 p4386 p4781 : Prop) (h : (¬ p4386) ∨ (¬ p4781) ∨ p2027 ∨ (¬ p2717) ∨ (¬ p2745) ∨ (¬ p3553) ∨ (¬ p3662)) : (p2027) ∨ (¬ p2717) ∨ (¬ p2745) ∨ (¬ p3553) ∨ (¬ p3662) ∨ (¬ p4386) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial10178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory1818 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule10178 (meaning t m 2027) (meaning t m 2717) (meaning t m 2745) (meaning t m 3553) (meaning t m 3662) (meaning t m 4386) (meaning t m 4781) source

theorem rule10179 (p2027 p2667 p2745 p2870 p2962 p3556 p4154 p4313 : Prop) (h : p2027 ∨ (¬ p2870) ∨ (¬ p4313) ∨ (¬ p3556) ∨ (¬ p2745) ∨ (¬ p2962) ∨ (¬ p2667) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2667) ∨ (¬ p2745) ∨ (¬ p2870) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p4154) ∨ (¬ p4313) := by
  classical
  tauto

theorem initial10179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4313)) := by
  have source := ElevenTheory.theory1819 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7)
  exact rule10179 (meaning t m 2027) (meaning t m 2667) (meaning t m 2745) (meaning t m 2870) (meaning t m 2962) (meaning t m 3556) (meaning t m 4154) (meaning t m 4313) source

theorem rule10180 (p2132 p2138 : Prop) (h : (¬ p2138) ∨ (¬ p2132)) : (¬ p2132) ∨ (¬ p2138) := by
  classical
  tauto

theorem initial10180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2138)) := by
  have source := ElevenTheory.theory1820 (m.theta 0 2) (m.theta 2 5)
  exact rule10180 (meaning t m 2132) (meaning t m 2138) source

theorem rule10182 (p2992 p4237 p4360 : Prop) (h : (¬ p2992) ∨ (¬ p4360) ∨ (¬ p4237)) : (¬ p2992) ∨ (¬ p4237) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial10182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory1822 (m.theta 1 3) (m.theta 3 5) (m.theta 3 8)
  exact rule10182 (meaning t m 2992) (meaning t m 4237) (meaning t m 4360) source

theorem rule10183 (p2027 p2088 p2534 p2881 p3960 p4186 p4277 : Prop) (h : (¬ p4186) ∨ (¬ p2088) ∨ (¬ p4277) ∨ (¬ p2534) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p3960)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2534) ∨ (¬ p2881) ∨ (¬ p3960) ∨ (¬ p4186) ∨ (¬ p4277) := by
  classical
  tauto

theorem initial10183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4277)) := by
  have source := ElevenTheory.theory1823 t (m.theta 0 8) (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule10183 (meaning t m 2027) (meaning t m 2088) (meaning t m 2534) (meaning t m 2881) (meaning t m 3960) (meaning t m 4186) (meaning t m 4277) source

theorem rule10184 (p2027 p2667 p2860 p2992 p3743 p4154 p5053 : Prop) (h : (¬ p2667) ∨ (¬ p2860) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p3743) ∨ (¬ p5053) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2667) ∨ (¬ p2860) ∨ (¬ p2992) ∨ (¬ p3743) ∨ (¬ p4154) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial10184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory1824 t (m.theta 0 6) (m.theta 1 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule10184 (meaning t m 2027) (meaning t m 2667) (meaning t m 2860) (meaning t m 2992) (meaning t m 3743) (meaning t m 4154) (meaning t m 5053) source

theorem rule10185 (p2187 p3989 : Prop) (h : (¬ p3989) ∨ (¬ p2187)) : (¬ p2187) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial10185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory1825 (m.theta 5 6) (m.theta 6 8)
  exact rule10185 (meaning t m 2187) (meaning t m 3989) source

theorem rule10189 (p5679 p5680 p5681 p5682 p5683 : Prop) : (¬ (p5679 ∧ p5680 ∧ p5681 ∧ p5682 ∧ p5683)) ∨ (p5682) := by
  classical
  tauto

theorem initial10189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5678)) ∨ (meaning t m 5682) := by
  exact rule10189 (meaning t m 5679) (meaning t m 5680) (meaning t m 5681) (meaning t m 5682) (meaning t m 5683)

theorem rule10194 (p4166 p5685 p5686 p5687 p5688 : Prop) : (p4166) ∨ (¬ (p5685 ∧ p5686 ∧ p4166 ∧ p5687 ∧ p5688)) := by
  classical
  tauto

theorem initial10194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4166) ∨ (¬ (meaning t m 5684)) := by
  exact rule10194 (meaning t m 4166) (meaning t m 5685) (meaning t m 5686) (meaning t m 5687) (meaning t m 5688)

theorem rule10200 (p5678 p5684 : Prop) : (¬ (p5678 ∨ p5684)) ∨ (p5678) ∨ (p5684) := by
  classical
  tauto

theorem initial10200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5677)) ∨ (meaning t m 5678) ∨ (meaning t m 5684) := by
  exact rule10200 (meaning t m 5678) (meaning t m 5684)

theorem rule10201 (p4160 p5677 : Prop) (h : (p4160 ↔ p5677)) : (¬ p4160) ∨ (p5677) := by
  classical
  tauto

theorem initial10201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4160)) ∨ (meaning t m 5677) := by
  have source := ElevenTheory.theory1826 t (m.theta 2 10) (m.theta 2 4) (m.theta 4 10)
  exact rule10201 (meaning t m 4160) (meaning t m 5677) source

theorem rule10203 (p2027 p2992 p4111 p4241 p4256 p4608 : Prop) (h : (¬ p4241) ∨ (¬ p4111) ∨ (¬ p4608) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p4256)) : (p2027) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4256) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial10203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory1827 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8)
  exact rule10203 (meaning t m 2027) (meaning t m 2992) (meaning t m 4111) (meaning t m 4241) (meaning t m 4256) (meaning t m 4608) source

theorem rule10204 (p2717 p3659 : Prop) (h : (¬ p3659) ∨ (¬ p2717)) : (¬ p2717) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial10204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory1828 (m.theta 2 7) (m.theta 7 8)
  exact rule10204 (meaning t m 2717) (meaning t m 3659) source

theorem rule10205 (p2027 p2177 p2311 p2553 p2581 p3551 : Prop) (h : p2027 ∨ (¬ p2311) ∨ (¬ p3551) ∨ (¬ p2581) ∨ (¬ p2553) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2553) ∨ (¬ p2581) ∨ (¬ p3551) := by
  classical
  tauto

theorem initial10205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2581)) ∨ (¬ (meaning t m 3551)) := by
  have source := ElevenTheory.theory1829 t (m.theta 0 6) (m.theta 0 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule10205 (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 2553) (meaning t m 2581) (meaning t m 3551) source

theorem rule10206 (p2027 p2284 p3051 p4110 p4320 p4539 : Prop) (h : p2027 ∨ (¬ p4110) ∨ (¬ p4320) ∨ (¬ p2284) ∨ (¬ p3051) ∨ (¬ p4539)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3051) ∨ (¬ p4110) ∨ (¬ p4320) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial10206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory1830 t (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule10206 (meaning t m 2027) (meaning t m 2284) (meaning t m 3051) (meaning t m 4110) (meaning t m 4320) (meaning t m 4539) source

theorem rule10207 (p2027 p2748 p3136 p3359 p4111 p4241 p4949 : Prop) (h : (¬ p2748) ∨ (¬ p3136) ∨ (¬ p4241) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p3359) ∨ (¬ p4949)) : (p2027) ∨ (¬ p2748) ∨ (¬ p3136) ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4949) := by
  classical
  tauto

theorem initial10207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4949)) := by
  have source := ElevenTheory.theory1831 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 9)
  exact rule10207 (meaning t m 2027) (meaning t m 2748) (meaning t m 3136) (meaning t m 3359) (meaning t m 4111) (meaning t m 4241) (meaning t m 4949) source

theorem rule10208 (p2027 p2870 p3516 p3691 p3947 p4386 p5053 : Prop) (h : (¬ p3516) ∨ (¬ p4386) ∨ (¬ p3691) ∨ (¬ p3947) ∨ (¬ p5053) ∨ (¬ p2870) ∨ p2027) : (p2027) ∨ (¬ p2870) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial10208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory1832 t (m.theta 0 7) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule10208 (meaning t m 2027) (meaning t m 2870) (meaning t m 3516) (meaning t m 3691) (meaning t m 3947) (meaning t m 4386) (meaning t m 5053) source

theorem rule10209 (p2027 p2396 p2922 p3193 p4276 p4636 : Prop) (h : (¬ p2922) ∨ (¬ p4276) ∨ (¬ p4636) ∨ p2027 ∨ (¬ p3193) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p4276) ∨ (¬ p4636) := by
  classical
  tauto

theorem initial10209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4636)) := by
  have source := ElevenTheory.theory1833 t (m.theta 1 4) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule10209 (meaning t m 2027) (meaning t m 2396) (meaning t m 2922) (meaning t m 3193) (meaning t m 4276) (meaning t m 4636) source

theorem rule10210 (p2027 p2589 p3016 p3389 p3742 p4717 : Prop) (h : (¬ p3016) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4717) ∨ (¬ p2589) ∨ p2027) : (p2027) ∨ (¬ p2589) ∨ (¬ p3016) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory1834 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule10210 (meaning t m 2027) (meaning t m 2589) (meaning t m 3016) (meaning t m 3389) (meaning t m 3742) (meaning t m 4717) source

theorem rule10212 (p3016 p3574 : Prop) (h : (¬ p3574) ∨ (¬ p3016)) : (¬ p3016) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial10212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory1836 (m.theta 3 4) (m.theta 4 6)
  exact rule10212 (meaning t m 3016) (meaning t m 3574) source

theorem rule10213 (p2027 p2363 p2782 p2819 p3857 p4197 : Prop) (h : (¬ p4197) ∨ (¬ p2363) ∨ (¬ p2782) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2782) ∨ (¬ p2819) ∨ (¬ p3857) ∨ (¬ p4197) := by
  classical
  tauto

theorem initial10213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2782)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4197)) := by
  have source := ElevenTheory.theory1837 t (m.theta 0 6) (m.theta 0 8) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule10213 (meaning t m 2027) (meaning t m 2363) (meaning t m 2782) (meaning t m 2819) (meaning t m 3857) (meaning t m 4197) source

theorem rule10215 (p2027 p3051 p3646 p3822 p4140 p4889 : Prop) (h : (¬ p3822) ∨ (¬ p3051) ∨ (¬ p4889) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p4140)) : (p2027) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3822) ∨ (¬ p4140) ∨ (¬ p4889) := by
  classical
  tauto

theorem initial10215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4889)) := by
  have source := ElevenTheory.theory1839 t (m.theta 0 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule10215 (meaning t m 2027) (meaning t m 3051) (meaning t m 3646) (meaning t m 3822) (meaning t m 4140) (meaning t m 4889) source

theorem rule10216 (p2027 p2476 p2662 p2810 p3136 p4241 p4608 : Prop) (h : (¬ p4608) ∨ (¬ p3136) ∨ (¬ p2810) ∨ (¬ p2662) ∨ (¬ p2476) ∨ p2027 ∨ (¬ p4241)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial10216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory1840 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8)
  exact rule10216 (meaning t m 2027) (meaning t m 2476) (meaning t m 2662) (meaning t m 2810) (meaning t m 3136) (meaning t m 4241) (meaning t m 4608) source

theorem rule10217 (p2027 p2098 p2363 p4232 p4859 p5339 : Prop) (h : p2027 ∨ (¬ p5339) ∨ (¬ p4232) ∨ (¬ p2098) ∨ (¬ p2363) ∨ (¬ p4859)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2363) ∨ (¬ p4232) ∨ (¬ p4859) ∨ (¬ p5339) := by
  classical
  tauto

theorem initial10217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 4232)) ∨ (¬ (meaning t m 4859)) ∨ (¬ (meaning t m 5339)) := by
  have source := ElevenTheory.theory1841 t (m.theta 0 2) (m.theta 2 8) (m.theta 2 9) (m.theta 6 8) (m.theta 8 9)
  exact rule10217 (meaning t m 2027) (meaning t m 2098) (meaning t m 2363) (meaning t m 4232) (meaning t m 4859) (meaning t m 5339) source

theorem rule10218 (p2027 p2140 p2870 p3246 p3821 p4984 : Prop) (h : (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4984) ∨ (¬ p2870) ∨ (¬ p2140) ∨ p2027) : (p2027) ∨ (¬ p2140) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial10218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2140)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory1842 t (m.theta 0 5) (m.theta 0 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9)
  exact rule10218 (meaning t m 2027) (meaning t m 2140) (meaning t m 2870) (meaning t m 3246) (meaning t m 3821) (meaning t m 4984) source

theorem rule10219 (p2027 p2166 p3136 p3877 p4312 p4960 : Prop) (h : p2027 ∨ (¬ p4960) ∨ (¬ p3136) ∨ (¬ p2166) ∨ (¬ p4312) ∨ (¬ p3877)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3136) ∨ (¬ p3877) ∨ (¬ p4312) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial10219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory1843 t (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8)
  exact rule10219 (meaning t m 2027) (meaning t m 2166) (meaning t m 3136) (meaning t m 3877) (meaning t m 4312) (meaning t m 4960) source

theorem rule10221 (p2027 p2191 p2373 p2493 p4202 p4717 : Prop) (h : (¬ p4202) ∨ (¬ p2191) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p4717) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2373) ∨ (¬ p2493) ∨ (¬ p4202) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory1845 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8)
  exact rule10221 (meaning t m 2027) (meaning t m 2191) (meaning t m 2373) (meaning t m 2493) (meaning t m 4202) (meaning t m 4717) source

theorem rule10224 (p5691 p5692 p5693 p5694 p5695 : Prop) : (¬ (p5691 ∧ p5692 ∧ p5693 ∧ p5694 ∧ p5695)) ∨ (p5693) := by
  classical
  tauto

theorem initial10224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5690)) ∨ (meaning t m 5693) := by
  exact rule10224 (meaning t m 5691) (meaning t m 5692) (meaning t m 5693) (meaning t m 5694) (meaning t m 5695)

theorem rule10228 (p4181 p5697 p5698 p5699 p5700 : Prop) : (¬ (p5697 ∧ p5698 ∧ p4181 ∧ p5699 ∧ p5700)) ∨ (p5697) := by
  classical
  tauto

theorem initial10228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5696)) ∨ (meaning t m 5697) := by
  exact rule10228 (meaning t m 4181) (meaning t m 5697) (meaning t m 5698) (meaning t m 5699) (meaning t m 5700)

theorem rule10229 (p4181 p5697 p5698 p5699 p5700 : Prop) : (¬ (p5697 ∧ p5698 ∧ p4181 ∧ p5699 ∧ p5700)) ∨ (p5698) := by
  classical
  tauto

theorem initial10229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5696)) ∨ (meaning t m 5698) := by
  exact rule10229 (meaning t m 4181) (meaning t m 5697) (meaning t m 5698) (meaning t m 5699) (meaning t m 5700)

theorem rule10230 (p4181 p5697 p5698 p5699 p5700 : Prop) : (p4181) ∨ (¬ (p5697 ∧ p5698 ∧ p4181 ∧ p5699 ∧ p5700)) := by
  classical
  tauto

theorem initial10230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4181) ∨ (¬ (meaning t m 5696)) := by
  exact rule10230 (meaning t m 4181) (meaning t m 5697) (meaning t m 5698) (meaning t m 5699) (meaning t m 5700)

theorem rule10231 (p4181 p5697 p5698 p5699 p5700 : Prop) : (¬ (p5697 ∧ p5698 ∧ p4181 ∧ p5699 ∧ p5700)) ∨ (p5699) := by
  classical
  tauto

theorem initial10231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5696)) ∨ (meaning t m 5699) := by
  exact rule10231 (meaning t m 4181) (meaning t m 5697) (meaning t m 5698) (meaning t m 5699) (meaning t m 5700)

theorem rule10232 (p4181 p5697 p5698 p5699 p5700 : Prop) : (¬ (p5697 ∧ p5698 ∧ p4181 ∧ p5699 ∧ p5700)) ∨ (p5700) := by
  classical
  tauto

theorem initial10232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5696)) ∨ (meaning t m 5700) := by
  exact rule10232 (meaning t m 4181) (meaning t m 5697) (meaning t m 5698) (meaning t m 5699) (meaning t m 5700)

theorem rule10233 (p4181 p5697 p5698 p5699 p5700 : Prop) : (¬ p4181) ∨ ((p5697 ∧ p5698 ∧ p4181 ∧ p5699 ∧ p5700)) ∨ (¬ p5697) ∨ (¬ p5698) ∨ (¬ p5699) ∨ (¬ p5700) := by
  classical
  tauto

theorem initial10233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4181)) ∨ (meaning t m 5696) ∨ (¬ (meaning t m 5697)) ∨ (¬ (meaning t m 5698)) ∨ (¬ (meaning t m 5699)) ∨ (¬ (meaning t m 5700)) := by
  exact rule10233 (meaning t m 4181) (meaning t m 5697) (meaning t m 5698) (meaning t m 5699) (meaning t m 5700)

theorem rule10236 (p5690 p5696 : Prop) : (¬ (p5690 ∨ p5696)) ∨ (p5690) ∨ (p5696) := by
  classical
  tauto

theorem initial10236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5689)) ∨ (meaning t m 5690) ∨ (meaning t m 5696) := by
  exact rule10236 (meaning t m 5690) (meaning t m 5696)

theorem rule10237 (p4175 p5689 : Prop) (h : (p4175 ↔ p5689)) : (¬ p4175) ∨ (p5689) := by
  classical
  tauto

theorem initial10237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4175)) ∨ (meaning t m 5689) := by
  have source := ElevenTheory.theory1846 t (m.theta 1 10) (m.theta 1 8) (m.theta 8 10)
  exact rule10237 (meaning t m 4175) (meaning t m 5689) source

theorem rule10239 (p3073 p4261 : Prop) (h : (¬ p4261) ∨ (¬ p3073)) : (¬ p3073) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial10239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory1847 (m.theta 1 8) (m.theta 8 9)
  exact rule10239 (meaning t m 3073) (meaning t m 4261) source

theorem rule10240 (p2027 p2406 p2509 p2563 p3693 p4507 : Prop) (h : p2027 ∨ (¬ p3693) ∨ (¬ p2406) ∨ (¬ p4507) ∨ (¬ p2563) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2563) ∨ (¬ p3693) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial10240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory1848 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8)
  exact rule10240 (meaning t m 2027) (meaning t m 2406) (meaning t m 2509) (meaning t m 2563) (meaning t m 3693) (meaning t m 4507) source

theorem rule10241 (p2027 p2210 p2247 p2996 p4282 p4917 : Prop) (h : (¬ p2247) ∨ (¬ p4917) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p4282) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p4282) ∨ (¬ p4917) := by
  classical
  tauto

theorem initial10241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4917)) := by
  have source := ElevenTheory.theory1849 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 7)
  exact rule10241 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2996) (meaning t m 4282) (meaning t m 4917) source

theorem rule10242 (p2027 p2727 p3016 p3662 p3879 p4717 : Prop) (h : (¬ p3879) ∨ (¬ p3662) ∨ (¬ p4717) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p3016)) : (p2027) ∨ (¬ p2727) ∨ (¬ p3016) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory1850 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6)
  exact rule10242 (meaning t m 2027) (meaning t m 2727) (meaning t m 3016) (meaning t m 3662) (meaning t m 3879) (meaning t m 4717) source

theorem rule10243 (p2027 p2810 p2860 p2957 p3646 p4313 p4704 : Prop) (h : (¬ p2957) ∨ (¬ p2810) ∨ (¬ p4704) ∨ (¬ p3646) ∨ (¬ p4313) ∨ p2027 ∨ (¬ p2860)) : (p2027) ∨ (¬ p2810) ∨ (¬ p2860) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p4313) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial10243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory1851 t (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule10243 (meaning t m 2027) (meaning t m 2810) (meaning t m 2860) (meaning t m 2957) (meaning t m 3646) (meaning t m 4313) (meaning t m 4704) source

theorem rule10244 (p2027 p3083 p3136 p3364 p3874 p4704 : Prop) (h : p2027 ∨ (¬ p4704) ∨ (¬ p3083) ∨ (¬ p3874) ∨ (¬ p3364) ∨ (¬ p3136)) : (p2027) ∨ (¬ p3083) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3874) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial10244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory1852 t (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 8)
  exact rule10244 (meaning t m 2027) (meaning t m 3083) (meaning t m 3136) (meaning t m 3364) (meaning t m 3874) (meaning t m 4704) source

theorem rule10245 (p2027 p2589 p2659 p2992 p4111 p4241 : Prop) (h : (¬ p2589) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p2659) ∨ (¬ p4241) ∨ (¬ p4111)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2659) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial10245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory1853 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule10245 (meaning t m 2027) (meaning t m 2589) (meaning t m 2659) (meaning t m 2992) (meaning t m 4111) (meaning t m 4241) source

theorem rule10246 (p2027 p2331 p2542 p2589 p2655 p4975 : Prop) (h : p2027 ∨ (¬ p4975) ∨ (¬ p2331) ∨ (¬ p2542) ∨ (¬ p2655) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial10246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory1854 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule10246 (meaning t m 2027) (meaning t m 2331) (meaning t m 2542) (meaning t m 2589) (meaning t m 2655) (meaning t m 4975) source

theorem rule10247 (p2027 p2331 p2440 p2657 p3984 p4717 : Prop) (h : (¬ p2331) ∨ (¬ p2657) ∨ (¬ p4717) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p3984)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3984) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory1855 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6)
  exact rule10247 (meaning t m 2027) (meaning t m 2331) (meaning t m 2440) (meaning t m 2657) (meaning t m 3984) (meaning t m 4717) source

theorem rule10248 (p2027 p2331 p2737 p2811 p3585 p4343 p4975 : Prop) (h : p2027 ∨ (¬ p2737) ∨ (¬ p4975) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p2331) ∨ (¬ p2811)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial10248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory1856 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6)
  exact rule10248 (meaning t m 2027) (meaning t m 2331) (meaning t m 2737) (meaning t m 2811) (meaning t m 3585) (meaning t m 4343) (meaning t m 4975) source

theorem rule10250 (p2027 p2166 p2950 p3136 p3412 p4120 p4787 : Prop) (h : (¬ p4787) ∨ (¬ p4120) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2950) ∨ (¬ p3412)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2950) ∨ (¬ p3136) ∨ (¬ p3412) ∨ (¬ p4120) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial10250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory1858 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8)
  exact rule10250 (meaning t m 2027) (meaning t m 2166) (meaning t m 2950) (meaning t m 3136) (meaning t m 3412) (meaning t m 4120) (meaning t m 4787) source

theorem rule10251 (p2027 p2241 p2630 p2745 p3452 p4116 : Prop) (h : (¬ p2745) ∨ (¬ p4116) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2630) ∨ (¬ p2745) ∨ (¬ p3452) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial10251 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory1859 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4)
  exact rule10251 (meaning t m 2027) (meaning t m 2241) (meaning t m 2630) (meaning t m 2745) (meaning t m 3452) (meaning t m 4116) source

theorem rule10252 (p2027 p3434 p3659 p3692 p4443 p4902 : Prop) (h : (¬ p4443) ∨ (¬ p4902) ∨ (¬ p3659) ∨ (¬ p3434) ∨ (¬ p3692) ∨ p2027) : (p2027) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial10252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory1860 t (m.theta 2 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule10252 (meaning t m 2027) (meaning t m 3434) (meaning t m 3659) (meaning t m 3692) (meaning t m 4443) (meaning t m 4902) source

theorem rule10253 (p2373 p3880 : Prop) (h : (¬ p3880) ∨ (¬ p2373)) : (¬ p2373) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial10253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory1861 (m.theta 4 5) (m.theta 5 8)
  exact rule10253 (meaning t m 2373) (meaning t m 3880) source

theorem rule10254 (p2027 p2241 p2641 p3452 p4116 p4975 : Prop) (h : (¬ p4116) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p4975) ∨ (¬ p2241) ∨ (¬ p2641)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial10254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory1862 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6)
  exact rule10254 (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 3452) (meaning t m 4116) (meaning t m 4975) source

theorem rule10255 (p2027 p2478 p2509 p3222 p3857 p4695 : Prop) (h : (¬ p2478) ∨ (¬ p3857) ∨ p2027 ∨ (¬ p4695) ∨ (¬ p2509) ∨ (¬ p3222)) : (p2027) ∨ (¬ p2478) ∨ (¬ p2509) ∨ (¬ p3222) ∨ (¬ p3857) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial10255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2478)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory1863 t (m.theta 0 8) (m.theta 1 4) (m.theta 4 8) (m.theta 4 9) (m.theta 8 9)
  exact rule10255 (meaning t m 2027) (meaning t m 2478) (meaning t m 2509) (meaning t m 3222) (meaning t m 3857) (meaning t m 4695) source

theorem rule10256 (p2027 p2534 p3073 p3238 p4610 p4688 : Prop) (h : (¬ p4610) ∨ (¬ p4688) ∨ (¬ p3238) ∨ (¬ p3073) ∨ p2027 ∨ (¬ p2534)) : (p2027) ∨ (¬ p2534) ∨ (¬ p3073) ∨ (¬ p3238) ∨ (¬ p4610) ∨ (¬ p4688) := by
  classical
  tauto

theorem initial10256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4610)) ∨ (¬ (meaning t m 4688)) := by
  have source := ElevenTheory.theory1864 t (m.theta 1 4) (m.theta 1 8) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule10256 (meaning t m 2027) (meaning t m 2534) (meaning t m 3073) (meaning t m 3238) (meaning t m 4610) (meaning t m 4688) source

theorem rule10257 (p2027 p2241 p2748 p3583 p3954 p5049 : Prop) (h : (¬ p2748) ∨ (¬ p2241) ∨ (¬ p5049) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p3954)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial10257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory1865 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5)
  exact rule10257 (meaning t m 2027) (meaning t m 2241) (meaning t m 2748) (meaning t m 3583) (meaning t m 3954) (meaning t m 5049) source

theorem rule10258 (p2027 p3189 p3574 p4111 p4346 p4598 : Prop) (h : (¬ p3574) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p4346) ∨ (¬ p3189) ∨ (¬ p4598)) : (p2027) ∨ (¬ p3189) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p4346) ∨ (¬ p4598) := by
  classical
  tauto

theorem initial10258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4346)) ∨ (¬ (meaning t m 4598)) := by
  have source := ElevenTheory.theory1866 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6) (m.theta 4 8)
  exact rule10258 (meaning t m 2027) (meaning t m 3189) (meaning t m 3574) (meaning t m 4111) (meaning t m 4346) (meaning t m 4598) source

theorem rule10259 (p2027 p2307 p2396 p2578 p4137 p4625 : Prop) (h : (¬ p2578) ∨ (¬ p4137) ∨ (¬ p2307) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p4625)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2578) ∨ (¬ p4137) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial10259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory1867 t (m.theta 0 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule10259 (meaning t m 2027) (meaning t m 2307) (meaning t m 2396) (meaning t m 2578) (meaning t m 4137) (meaning t m 4625) source

theorem rule10261 (p2027 p2383 p2578 p3016 p3742 p3921 p4405 : Prop) (h : (¬ p3921) ∨ (¬ p4405) ∨ (¬ p2578) ∨ (¬ p2383) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p3742)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2578) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3921) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial10261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory1869 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule10261 (meaning t m 2027) (meaning t m 2383) (meaning t m 2578) (meaning t m 3016) (meaning t m 3742) (meaning t m 3921) (meaning t m 4405) source

theorem rule10263 (p2027 p2563 p3125 p3946 p4198 p4533 : Prop) (h : (¬ p3125) ∨ (¬ p4198) ∨ (¬ p3946) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p4533)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4198) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial10263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory1871 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9)
  exact rule10263 (meaning t m 2027) (meaning t m 2563) (meaning t m 3125) (meaning t m 3946) (meaning t m 4198) (meaning t m 4533) source

theorem rule10264 (p2027 p2187 p2387 p2563 p4198 p4533 : Prop) (h : (¬ p2563) ∨ (¬ p4533) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p4198) ∨ (¬ p2387)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2563) ∨ (¬ p4198) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial10264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory1872 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule10264 (meaning t m 2027) (meaning t m 2187) (meaning t m 2387) (meaning t m 2563) (meaning t m 4198) (meaning t m 4533) source

theorem rule10265 (p2027 p2553 p3097 p3660 p3952 p4702 : Prop) (h : (¬ p4702) ∨ (¬ p3660) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p2553)) : (p2027) ∨ (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3660) ∨ (¬ p3952) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial10265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory1873 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule10265 (meaning t m 2027) (meaning t m 2553) (meaning t m 3097) (meaning t m 3660) (meaning t m 3952) (meaning t m 4702) source

theorem rule10266 (p2027 p2284 p2553 p4275 p4320 p4718 : Prop) (h : (¬ p2553) ∨ (¬ p4718) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p4320) ∨ (¬ p4275)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2553) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial10266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory1874 t (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule10266 (meaning t m 2027) (meaning t m 2284) (meaning t m 2553) (meaning t m 4275) (meaning t m 4320) (meaning t m 4718) source

theorem rule10267 (p2027 p2501 p2553 p3093 p4366 p4427 : Prop) (h : (¬ p3093) ∨ (¬ p4427) ∨ (¬ p2501) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p4366)) : (p2027) ∨ (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427) := by
  classical
  tauto

theorem initial10267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2501)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4427)) := by
  have source := ElevenTheory.theory1875 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 4 6) (m.theta 6 7)
  exact rule10267 (meaning t m 2027) (meaning t m 2501) (meaning t m 2553) (meaning t m 3093) (meaning t m 4366) (meaning t m 4427) source

theorem rule10268 (p2027 p2533 p3680 p4118 p4444 p5063 : Prop) (h : (¬ p5063) ∨ (¬ p4118) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p2533) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4118) ∨ (¬ p4444) ∨ (¬ p5063) := by
  classical
  tauto

theorem initial10268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5063)) := by
  have source := ElevenTheory.theory1876 t (m.theta 3 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule10268 (meaning t m 2027) (meaning t m 2533) (meaning t m 3680) (meaning t m 4118) (meaning t m 4444) (meaning t m 5063) source

theorem rule10269 (p2027 p3146 p3266 p3657 p4191 p4623 p4905 : Prop) (h : (¬ p4623) ∨ (¬ p4905) ∨ (¬ p3146) ∨ (¬ p3657) ∨ (¬ p4191) ∨ (¬ p3266) ∨ p2027) : (p2027) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4191) ∨ (¬ p4623) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial10269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4623)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory1877 t (m.theta 5 8) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule10269 (meaning t m 2027) (meaning t m 3146) (meaning t m 3266) (meaning t m 3657) (meaning t m 4191) (meaning t m 4623) (meaning t m 4905) source

theorem rule10270 (p2027 p2531 p3641 p3684 p4120 p4533 : Prop) (h : (¬ p3684) ∨ (¬ p3641) ∨ p2027 ∨ (¬ p2531) ∨ (¬ p4120) ∨ (¬ p4533)) : (p2027) ∨ (¬ p2531) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4120) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial10270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory1878 t (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule10270 (meaning t m 2027) (meaning t m 2531) (meaning t m 3641) (meaning t m 3684) (meaning t m 4120) (meaning t m 4533) source

theorem rule10271 (p2027 p2299 p2881 p3568 p3872 p4564 : Prop) (h : (¬ p4564) ∨ (¬ p3568) ∨ (¬ p2299) ∨ (¬ p2881) ∨ (¬ p3872) ∨ p2027) : (p2027) ∨ (¬ p2299) ∨ (¬ p2881) ∨ (¬ p3568) ∨ (¬ p3872) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial10271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory1879 t (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule10271 (meaning t m 2027) (meaning t m 2299) (meaning t m 2881) (meaning t m 3568) (meaning t m 3872) (meaning t m 4564) source

theorem rule10272 (p2027 p3201 p3568 p3584 p4710 p4973 : Prop) (h : (¬ p4710) ∨ (¬ p3201) ∨ (¬ p3584) ∨ (¬ p4973) ∨ p2027 ∨ (¬ p3568)) : (p2027) ∨ (¬ p3201) ∨ (¬ p3568) ∨ (¬ p3584) ∨ (¬ p4710) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial10272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory1880 t (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule10272 (meaning t m 2027) (meaning t m 3201) (meaning t m 3568) (meaning t m 3584) (meaning t m 4710) (meaning t m 4973) source

theorem rule10273 (p2027 p2177 p2553 p3553 p4067 p4973 : Prop) (h : (¬ p2553) ∨ (¬ p4067) ∨ (¬ p3553) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p4973)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial10273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory1881 t (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule10273 (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 3553) (meaning t m 4067) (meaning t m 4973) source

theorem rule10274 (p2027 p3324 p3584 p3641 p4157 p4973 : Prop) (h : p2027 ∨ (¬ p3641) ∨ (¬ p4973) ∨ (¬ p3584) ∨ (¬ p4157) ∨ (¬ p3324)) : (p2027) ∨ (¬ p3324) ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p4157) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial10274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory1882 t (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule10274 (meaning t m 2027) (meaning t m 3324) (meaning t m 3584) (meaning t m 3641) (meaning t m 4157) (meaning t m 4973) source

theorem rule10275 (p2027 p2313 p2493 p2553 p2577 p5191 : Prop) (h : (¬ p2577) ∨ (¬ p2553) ∨ (¬ p2313) ∨ (¬ p5191) ∨ p2027 ∨ (¬ p2493)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p5191) := by
  classical
  tauto

theorem initial10275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 5191)) := by
  have source := ElevenTheory.theory1883 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 6 7)
  exact rule10275 (meaning t m 2027) (meaning t m 2313) (meaning t m 2493) (meaning t m 2553) (meaning t m 2577) (meaning t m 5191) source

theorem rule10277 (p2470 p2589 p4607 : Prop) (h : (¬ p2470) ∨ (¬ p2589) ∨ (¬ p4607)) : (¬ p2470) ∨ (¬ p2589) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial10277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory1885 (m.theta 0 4) (m.theta 4 5) (m.theta 4 8)
  exact rule10277 (meaning t m 2470) (meaning t m 2589) (meaning t m 4607) source

theorem rule10278 (p2027 p2373 p2406 p3904 p4120 p5191 : Prop) (h : (¬ p2406) ∨ (¬ p2373) ∨ (¬ p5191) ∨ (¬ p4120) ∨ (¬ p3904) ∨ p2027) : (p2027) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p5191) := by
  classical
  tauto

theorem initial10278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 5191)) := by
  have source := ElevenTheory.theory1886 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 5 8)
  exact rule10278 (meaning t m 2027) (meaning t m 2373) (meaning t m 2406) (meaning t m 3904) (meaning t m 4120) (meaning t m 5191) source

theorem rule10279 (p2027 p2373 p2387 p4110 p4441 p4486 : Prop) (h : (¬ p4110) ∨ (¬ p4486) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2373) ∨ (¬ p4441)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2387) ∨ (¬ p4110) ∨ (¬ p4441) ∨ (¬ p4486) := by
  classical
  tauto

theorem initial10279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 4486)) := by
  have source := ElevenTheory.theory1887 t (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule10279 (meaning t m 2027) (meaning t m 2373) (meaning t m 2387) (meaning t m 4110) (meaning t m 4441) (meaning t m 4486) source

theorem rule10280 (p2027 p2774 p3365 p3367 p3688 p4752 : Prop) (h : (¬ p3367) ∨ (¬ p3688) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4752)) : (p2027) ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial10280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory1888 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6)
  exact rule10280 (meaning t m 2027) (meaning t m 2774) (meaning t m 3365) (meaning t m 3367) (meaning t m 3688) (meaning t m 4752) source

theorem rule10283 (p2027 p2532 p2982 p3880 p4348 p4905 : Prop) (h : (¬ p2532) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p2982) ∨ (¬ p4905) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2532) ∨ (¬ p2982) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial10283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory1891 t (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule10283 (meaning t m 2027) (meaning t m 2532) (meaning t m 2982) (meaning t m 3880) (meaning t m 4348) (meaning t m 4905) source

theorem rule10285 (p2027 p2088 p2274 p2312 p4261 p4371 p4514 p4590 : Prop) (h : (¬ p2312) ∨ (¬ p2274) ∨ (¬ p4371) ∨ (¬ p4514) ∨ p2027 ∨ (¬ p2088) ∨ (¬ p4590) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4514) ∨ (¬ p4590) := by
  classical
  tauto

theorem initial10285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 4514)) ∨ (¬ (meaning t m 4590)) := by
  have source := ElevenTheory.theory1893 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 6) (m.theta 1 8) (m.theta 5 6) (m.theta 6 7) (m.theta 8 9)
  exact rule10285 (meaning t m 2027) (meaning t m 2088) (meaning t m 2274) (meaning t m 2312) (meaning t m 4261) (meaning t m 4371) (meaning t m 4514) (meaning t m 4590) source

theorem rule10286 (p2027 p2295 p3093 p4366 p4427 p4757 : Prop) (h : (¬ p4427) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p4757) ∨ (¬ p3093) ∨ (¬ p2295)) : (p2027) ∨ (¬ p2295) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427) ∨ (¬ p4757) := by
  classical
  tauto

theorem initial10286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4427)) ∨ (¬ (meaning t m 4757)) := by
  have source := ElevenTheory.theory1894 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 3 6) (m.theta 6 7)
  exact rule10286 (meaning t m 2027) (meaning t m 2295) (meaning t m 3093) (meaning t m 4366) (meaning t m 4427) (meaning t m 4757) source

theorem rule10287 (p2027 p2313 p2501 p2553 p3093 p5015 : Prop) (h : (¬ p2313) ∨ (¬ p3093) ∨ (¬ p5015) ∨ (¬ p2553) ∨ (¬ p2501) ∨ p2027) : (p2027) ∨ (¬ p2313) ∨ (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3093) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial10287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2501)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory1895 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7)
  exact rule10287 (meaning t m 2027) (meaning t m 2313) (meaning t m 2501) (meaning t m 2553) (meaning t m 3093) (meaning t m 5015) source

theorem rule10289 (p2027 p2187 p2331 p3172 p4564 p4769 : Prop) (h : p2027 ∨ (¬ p4769) ∨ (¬ p4564) ∨ (¬ p2187) ∨ (¬ p2331) ∨ (¬ p3172)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2331) ∨ (¬ p3172) ∨ (¬ p4564) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial10289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4564)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory1897 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8)
  exact rule10289 (meaning t m 2027) (meaning t m 2187) (meaning t m 2331) (meaning t m 3172) (meaning t m 4564) (meaning t m 4769) source

theorem rule10291 (p2027 p3564 p3857 p3956 p4345 p4614 : Prop) (h : (¬ p3956) ∨ (¬ p4614) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p4345) ∨ (¬ p3564)) : (p2027) ∨ (¬ p3564) ∨ (¬ p3857) ∨ (¬ p3956) ∨ (¬ p4345) ∨ (¬ p4614) := by
  classical
  tauto

theorem initial10291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4614)) := by
  have source := ElevenTheory.theory1899 t (m.theta 0 8) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule10291 (meaning t m 2027) (meaning t m 3564) (meaning t m 3857) (meaning t m 3956) (meaning t m 4345) (meaning t m 4614) source

theorem rule10292 (p2027 p2253 p2331 p2750 p3954 p4154 : Prop) (h : (¬ p2750) ∨ (¬ p2253) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial10292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory1900 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 6)
  exact rule10292 (meaning t m 2027) (meaning t m 2253) (meaning t m 2331) (meaning t m 2750) (meaning t m 3954) (meaning t m 4154) source

theorem rule10293 (p2027 p2274 p2311 p2396 p3821 p4486 : Prop) (h : (¬ p2396) ∨ p2027 ∨ (¬ p2311) ∨ (¬ p3821) ∨ (¬ p2274) ∨ (¬ p4486)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2311) ∨ (¬ p2396) ∨ (¬ p3821) ∨ (¬ p4486) := by
  classical
  tauto

theorem initial10293 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4486)) := by
  have source := ElevenTheory.theory1901 t (m.theta 0 6) (m.theta 0 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule10293 (meaning t m 2027) (meaning t m 2274) (meaning t m 2311) (meaning t m 2396) (meaning t m 3821) (meaning t m 4486) source

theorem rule10294 (p2027 p2298 p2553 p2797 p3572 p4973 : Prop) (h : (¬ p2298) ∨ (¬ p4973) ∨ (¬ p2553) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p3572)) : (p2027) ∨ (¬ p2298) ∨ (¬ p2553) ∨ (¬ p2797) ∨ (¬ p3572) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial10294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory1902 t (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7)
  exact rule10294 (meaning t m 2027) (meaning t m 2298) (meaning t m 2553) (meaning t m 2797) (meaning t m 3572) (meaning t m 4973) source

theorem rule10295 (p2027 p2352 p2387 p2577 p3389 p4711 : Prop) (h : (¬ p3389) ∨ (¬ p4711) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2352) ∨ (¬ p2577)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p3389) ∨ (¬ p4711) := by
  classical
  tauto

theorem initial10295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4711)) := by
  have source := ElevenTheory.theory1903 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 8)
  exact rule10295 (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 2577) (meaning t m 3389) (meaning t m 4711) source

theorem rule10297 (p2027 p2166 p2751 p3497 p4315 p4365 : Prop) (h : (¬ p3497) ∨ (¬ p2751) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p4315) ∨ (¬ p4365)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2751) ∨ (¬ p3497) ∨ (¬ p4315) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial10297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory1905 t (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8)
  exact rule10297 (meaning t m 2027) (meaning t m 2166) (meaning t m 2751) (meaning t m 3497) (meaning t m 4315) (meaning t m 4365) source

theorem rule10298 (p2027 p2727 p2749 p2810 p3583 p5049 : Prop) (h : (¬ p2749) ∨ (¬ p5049) ∨ (¬ p2727) ∨ (¬ p3583) ∨ (¬ p2810) ∨ p2027) : (p2027) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p3583) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial10298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory1906 t (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4)
  exact rule10298 (meaning t m 2027) (meaning t m 2727) (meaning t m 2749) (meaning t m 2810) (meaning t m 3583) (meaning t m 5049) source

theorem rule10299 (p2027 p2870 p3698 p4129 p4382 p4830 p4948 : Prop) (h : (¬ p4830) ∨ p2027 ∨ (¬ p4129) ∨ (¬ p4948) ∨ (¬ p4382) ∨ (¬ p2870) ∨ (¬ p3698)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3698) ∨ (¬ p4129) ∨ (¬ p4382) ∨ (¬ p4830) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial10299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4830)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory1907 t (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 10) (m.theta 7 9)
  exact rule10299 (meaning t m 2027) (meaning t m 2870) (meaning t m 3698) (meaning t m 4129) (meaning t m 4382) (meaning t m 4830) (meaning t m 4948) source

theorem rule10300 (p2027 p3670 p4037 p4191 p4231 p4846 : Prop) (h : (¬ p3670) ∨ (¬ p4846) ∨ (¬ p4231) ∨ (¬ p4191) ∨ (¬ p4037) ∨ p2027) : (p2027) ∨ (¬ p3670) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4231) ∨ (¬ p4846) := by
  classical
  tauto

theorem initial10300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4231)) ∨ (¬ (meaning t m 4846)) := by
  have source := ElevenTheory.theory1908 t (m.theta 2 6) (m.theta 2 9) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule10300 (meaning t m 2027) (meaning t m 3670) (meaning t m 4037) (meaning t m 4191) (meaning t m 4231) (meaning t m 4846) source

theorem rule10302 (p2027 p2249 p2284 p2950 p2992 p3646 : Prop) (h : (¬ p2249) ∨ (¬ p2992) ∨ (¬ p2950) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p3646)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2284) ∨ (¬ p2950) ∨ (¬ p2992) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial10302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory1910 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6)
  exact rule10302 (meaning t m 2027) (meaning t m 2249) (meaning t m 2284) (meaning t m 2950) (meaning t m 2992) (meaning t m 3646) source

theorem rule10305 (p2027 p2315 p2363 p3325 p3551 p4348 : Prop) (h : (¬ p2315) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4348) ∨ (¬ p3325) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2315) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3551) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial10305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2315)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory1913 t (m.theta 0 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule10305 (meaning t m 2027) (meaning t m 2315) (meaning t m 2363) (meaning t m 3325) (meaning t m 3551) (meaning t m 4348) source

theorem rule10306 (p2027 p2137 p2156 p2839 p3588 p4169 p4555 : Prop) (h : (¬ p4169) ∨ p2027 ∨ (¬ p2137) ∨ (¬ p3588) ∨ (¬ p2839) ∨ (¬ p2156) ∨ (¬ p4555)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2839) ∨ (¬ p3588) ∨ (¬ p4169) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial10306 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1914 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7)
  exact rule10306 (meaning t m 2027) (meaning t m 2137) (meaning t m 2156) (meaning t m 2839) (meaning t m 3588) (meaning t m 4169) (meaning t m 4555) source

theorem rule10307 (p2027 p2295 p2312 p2341 p3324 p4503 : Prop) (h : p2027 ∨ (¬ p2341) ∨ (¬ p3324) ∨ (¬ p2312) ∨ (¬ p2295) ∨ (¬ p4503)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3324) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial10307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory1915 t (m.theta 0 7) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule10307 (meaning t m 2027) (meaning t m 2295) (meaning t m 2312) (meaning t m 2341) (meaning t m 3324) (meaning t m 4503) source

theorem rule10308 (p2027 p2104 p2696 p2751 p3189 p4963 : Prop) (h : p2027 ∨ (¬ p2104) ∨ (¬ p3189) ∨ (¬ p2696) ∨ (¬ p4963) ∨ (¬ p2751)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p3189) ∨ (¬ p4963) := by
  classical
  tauto

theorem initial10308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4963)) := by
  have source := ElevenTheory.theory1916 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8)
  exact rule10308 (meaning t m 2027) (meaning t m 2104) (meaning t m 2696) (meaning t m 2751) (meaning t m 3189) (meaning t m 4963) source

theorem rule10310 (p2027 p2528 p3166 p3292 p5009 p5107 : Prop) (h : (¬ p5009) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p3292) ∨ (¬ p3166) ∨ (¬ p5107)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3166) ∨ (¬ p3292) ∨ (¬ p5009) ∨ (¬ p5107) := by
  classical
  tauto

theorem initial10310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 5009)) ∨ (¬ (meaning t m 5107)) := by
  have source := ElevenTheory.theory1918 t (m.theta 0 3) (m.theta 3 8) (m.theta 3 9) (m.theta 4 8) (m.theta 8 9)
  exact rule10310 (meaning t m 2027) (meaning t m 2528) (meaning t m 3166) (meaning t m 3292) (meaning t m 5009) (meaning t m 5107) source

theorem rule10311 (p2027 p2685 p3552 p4037 p4195 p4620 : Prop) (h : (¬ p4037) ∨ p2027 ∨ (¬ p4620) ∨ (¬ p3552) ∨ (¬ p2685) ∨ (¬ p4195)) : (p2027) ∨ (¬ p2685) ∨ (¬ p3552) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial10311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory1919 t (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 9)
  exact rule10311 (meaning t m 2027) (meaning t m 2685) (meaning t m 3552) (meaning t m 4037) (meaning t m 4195) (meaning t m 4620) source

theorem rule10312 (p2177 p3644 p4710 : Prop) (h : (¬ p2177) ∨ (¬ p3644) ∨ (¬ p4710)) : (¬ p2177) ∨ (¬ p3644) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial10312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory1920 (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule10312 (meaning t m 2177) (meaning t m 3644) (meaning t m 4710) source

theorem rule10313 (p2027 p2751 p2972 p4208 p4315 p4365 : Prop) (h : (¬ p4365) ∨ (¬ p2972) ∨ (¬ p2751) ∨ (¬ p4315) ∨ (¬ p4208) ∨ p2027) : (p2027) ∨ (¬ p2751) ∨ (¬ p2972) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial10313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory1921 t (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9)
  exact rule10313 (meaning t m 2027) (meaning t m 2751) (meaning t m 2972) (meaning t m 4208) (meaning t m 4315) (meaning t m 4365) source

theorem rule10314 (p2027 p2493 p2751 p2810 p3574 p4281 : Prop) (h : (¬ p2751) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p2810) ∨ (¬ p4281)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p3574) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial10314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory1922 t (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6)
  exact rule10314 (meaning t m 2027) (meaning t m 2493) (meaning t m 2751) (meaning t m 2810) (meaning t m 3574) (meaning t m 4281) source

theorem rule10315 (p2027 p2751 p3027 p3516 p4066 p4324 p4781 : Prop) (h : (¬ p2751) ∨ (¬ p4066) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p4324) ∨ p4781 ∨ (¬ p3516)) : (p2027) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4324) ∨ (p4781) := by
  classical
  tauto

theorem initial10315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4324)) ∨ (meaning t m 4781) := by
  have source := ElevenTheory.theory1923 t (m.theta 0 7) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 9)
  exact rule10315 (meaning t m 2027) (meaning t m 2751) (meaning t m 3027) (meaning t m 3516) (meaning t m 4066) (meaning t m 4324) (meaning t m 4781) source

theorem rule10316 (p2027 p2751 p3319 p4037 p4195 p4759 : Prop) (h : p2027 ∨ (¬ p4195) ∨ (¬ p4759) ∨ (¬ p2751) ∨ (¬ p4037) ∨ (¬ p3319)) : (p2027) ∨ (¬ p2751) ∨ (¬ p3319) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial10316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory1924 t (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9)
  exact rule10316 (meaning t m 2027) (meaning t m 2751) (meaning t m 3319) (meaning t m 4037) (meaning t m 4195) (meaning t m 4759) source

theorem rule10317 (p2027 p2307 p2751 p3568 p4195 p4759 p5016 : Prop) (h : p2027 ∨ (¬ p4195) ∨ (¬ p4759) ∨ (¬ p3568) ∨ (¬ p2751) ∨ (¬ p2307) ∨ (¬ p5016)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2751) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4759) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial10317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4759)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory1925 t (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7)
  exact rule10317 (meaning t m 2027) (meaning t m 2307) (meaning t m 2751) (meaning t m 3568) (meaning t m 4195) (meaning t m 4759) (meaning t m 5016) source

theorem rule10320 (p2027 p2088 p3097 p3743 p4114 p4347 p4405 : Prop) (h : (¬ p3743) ∨ (¬ p2088) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p4405) ∨ (¬ p4114)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3097) ∨ (¬ p3743) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial10320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory1928 t (m.theta 0 6) (m.theta 0 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule10320 (meaning t m 2027) (meaning t m 2088) (meaning t m 3097) (meaning t m 3743) (meaning t m 4114) (meaning t m 4347) (meaning t m 4405) source

theorem rule10321 (p3005 p3877 : Prop) (h : (¬ p3877) ∨ (¬ p3005)) : (¬ p3005) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial10321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory1929 (m.theta 2 3) (m.theta 3 8)
  exact rule10321 (meaning t m 3005) (meaning t m 3877) source

theorem rule10323 (p2027 p2249 p2657 p2922 p3742 p4281 : Prop) (h : p2027 ∨ (¬ p2249) ∨ (¬ p3742) ∨ (¬ p2922) ∨ (¬ p2657) ∨ (¬ p4281)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2657) ∨ (¬ p2922) ∨ (¬ p3742) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial10323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory1931 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7)
  exact rule10323 (meaning t m 2027) (meaning t m 2249) (meaning t m 2657) (meaning t m 2922) (meaning t m 3742) (meaning t m 4281) source

theorem rule10326 (p2027 p2274 p2331 p3414 p3740 p3921 p4564 : Prop) (h : (¬ p3740) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4564) ∨ (¬ p2274) ∨ (¬ p3414) ∨ (¬ p3921)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2331) ∨ (¬ p3414) ∨ (¬ p3740) ∨ (¬ p3921) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial10326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory1934 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7)
  exact rule10326 (meaning t m 2027) (meaning t m 2274) (meaning t m 2331) (meaning t m 3414) (meaning t m 3740) (meaning t m 3921) (meaning t m 4564) source

theorem rule10327 (p2027 p2246 p2284 p2946 p2996 p3699 p4555 : Prop) (h : p2027 ∨ (¬ p4555) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3699) ∨ (¬ p2996) ∨ (¬ p2246)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p2996) ∨ (¬ p3699) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial10327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1935 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7)
  exact rule10327 (meaning t m 2027) (meaning t m 2246) (meaning t m 2284) (meaning t m 2946) (meaning t m 2996) (meaning t m 3699) (meaning t m 4555) source

theorem rule10329 (p2027 p2972 p4034 p4037 p4110 p4564 p5045 : Prop) (h : (¬ p4034) ∨ (¬ p5045) ∨ (¬ p2972) ∨ (¬ p4037) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p4564)) : (p2027) ∨ (¬ p2972) ∨ (¬ p4034) ∨ (¬ p4037) ∨ (¬ p4110) ∨ (¬ p4564) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial10329 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4564)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory1937 t (m.theta 1 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule10329 (meaning t m 2027) (meaning t m 2972) (meaning t m 4034) (meaning t m 4037) (meaning t m 4110) (meaning t m 4564) (meaning t m 5045) source

theorem rule10330 (p2027 p3599 p3688 p4037 p4846 p5269 : Prop) (h : (¬ p4037) ∨ (¬ p3599) ∨ (¬ p3688) ∨ (¬ p5269) ∨ (¬ p4846) ∨ p2027) : (p2027) ∨ (¬ p3599) ∨ (¬ p3688) ∨ (¬ p4037) ∨ (¬ p4846) ∨ (¬ p5269) := by
  classical
  tauto

theorem initial10330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4846)) ∨ (¬ (meaning t m 5269)) := by
  have source := ElevenTheory.theory1938 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 9) (m.theta 3 6) (m.theta 6 9)
  exact rule10330 (meaning t m 2027) (meaning t m 3599) (meaning t m 3688) (meaning t m 4037) (meaning t m 4846) (meaning t m 5269) source

theorem rule10331 (p2027 p2563 p2891 p3556 p4173 p4533 : Prop) (h : (¬ p2563) ∨ (¬ p3556) ∨ (¬ p4173) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p4533)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p4173) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial10331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory1939 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule10331 (meaning t m 2027) (meaning t m 2563) (meaning t m 2891) (meaning t m 3556) (meaning t m 4173) (meaning t m 4533) source

theorem rule10332 (p2027 p2982 p3947 p4135 p4235 p4280 : Prop) (h : (¬ p3947) ∨ (¬ p4135) ∨ (¬ p2982) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p4280)) : (p2027) ∨ (¬ p2982) ∨ (¬ p3947) ∨ (¬ p4135) ∨ (¬ p4235) ∨ (¬ p4280) := by
  classical
  tauto

theorem initial10332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4280)) := by
  have source := ElevenTheory.theory1940 t (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule10332 (meaning t m 2027) (meaning t m 2982) (meaning t m 3947) (meaning t m 4135) (meaning t m 4235) (meaning t m 4280) source

theorem rule10333 (p2027 p2685 p3040 p3527 p3877 p4548 : Prop) (h : (¬ p3527) ∨ (¬ p3877) ∨ (¬ p4548) ∨ p2027 ∨ (¬ p3040) ∨ (¬ p2685)) : (p2027) ∨ (¬ p2685) ∨ (¬ p3040) ∨ (¬ p3527) ∨ (¬ p3877) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial10333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3040)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory1941 t (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8)
  exact rule10333 (meaning t m 2027) (meaning t m 2685) (meaning t m 3040) (meaning t m 3527) (meaning t m 3877) (meaning t m 4548) source

theorem rule10334 (p2027 p2751 p3038 p3527 p3551 p3572 p4155 : Prop) (h : (¬ p2751) ∨ (¬ p3527) ∨ (¬ p4155) ∨ (¬ p3572) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p3038)) : (p2027) ∨ (¬ p2751) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3572) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial10334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory1942 t (m.theta 0 7) (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8)
  exact rule10334 (meaning t m 2027) (meaning t m 2751) (meaning t m 3038) (meaning t m 3527) (meaning t m 3551) (meaning t m 3572) (meaning t m 4155) source

theorem rule10336 (p2027 p2685 p3040 p3516 p3543 p4035 p4656 : Prop) (h : p2027 ∨ (¬ p3516) ∨ (¬ p4656) ∨ (¬ p4035) ∨ (¬ p2685) ∨ (¬ p3543) ∨ (¬ p3040)) : (p2027) ∨ (¬ p2685) ∨ (¬ p3040) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p4035) ∨ (¬ p4656) := by
  classical
  tauto

theorem initial10336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3040)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4656)) := by
  have source := ElevenTheory.theory1944 t (m.theta 0 7) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 7 9)
  exact rule10336 (meaning t m 2027) (meaning t m 2685) (meaning t m 3040) (meaning t m 3516) (meaning t m 3543) (meaning t m 4035) (meaning t m 4656) source

theorem rule10337 (p2027 p2528 p3324 p3875 p3920 p4347 p4973 : Prop) (h : (¬ p3875) ∨ (¬ p3920) ∨ (¬ p4973) ∨ (¬ p2528) ∨ (¬ p4347) ∨ (¬ p3324) ∨ p2027) : (p2027) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p3875) ∨ (¬ p3920) ∨ (¬ p4347) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial10337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory1945 t (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule10337 (meaning t m 2027) (meaning t m 2528) (meaning t m 3324) (meaning t m 3875) (meaning t m 3920) (meaning t m 4347) (meaning t m 4973) source

theorem rule10338 (p2027 p2156 p3737 p4032 p4033 p5253 : Prop) (h : (¬ p4032) ∨ (¬ p3737) ∨ (¬ p5253) ∨ (¬ p4033) ∨ p2027 ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3737) ∨ (¬ p4032) ∨ (¬ p4033) ∨ (¬ p5253) := by
  classical
  tauto

theorem initial10338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 5253)) := by
  have source := ElevenTheory.theory1946 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 10) (m.theta 6 9)
  exact rule10338 (meaning t m 2027) (meaning t m 2156) (meaning t m 3737) (meaning t m 4032) (meaning t m 4033) (meaning t m 5253) source

theorem rule10339 (p2027 p2284 p2528 p3661 p3875 p4001 p4118 p4555 : Prop) (h : (¬ p4555) ∨ (¬ p3875) ∨ (¬ p2528) ∨ (¬ p4001) ∨ (¬ p3661) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p2284)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2528) ∨ (¬ p3661) ∨ (¬ p3875) ∨ (¬ p4001) ∨ (¬ p4118) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial10339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1947 t (m.theta 3 5) (m.theta 3 8) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 5 7) (m.theta 8 9)
  exact rule10339 (meaning t m 2027) (meaning t m 2284) (meaning t m 2528) (meaning t m 3661) (meaning t m 3875) (meaning t m 4001) (meaning t m 4118) (meaning t m 4555) source

theorem rule10341 (p2027 p2528 p3266 p3322 p4191 p4384 : Prop) (h : (¬ p4191) ∨ (¬ p3322) ∨ (¬ p3266) ∨ (¬ p4384) ∨ (¬ p2528) ∨ p2027) : (p2027) ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p4191) ∨ (¬ p4384) := by
  classical
  tauto

theorem initial10341 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4384)) := by
  have source := ElevenTheory.theory1949 t (m.theta 4 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule10341 (meaning t m 2027) (meaning t m 2528) (meaning t m 3266) (meaning t m 3322) (meaning t m 4191) (meaning t m 4384) source

theorem rule10342 (p2027 p2528 p2668 p3693 p4037 p4134 p4171 : Prop) (h : p2027 ∨ (¬ p3693) ∨ (¬ p2528) ∨ (¬ p4171) ∨ (¬ p2668) ∨ (¬ p4037) ∨ (¬ p4134)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2668) ∨ (¬ p3693) ∨ (¬ p4037) ∨ (¬ p4134) ∨ (¬ p4171) := by
  classical
  tauto

theorem initial10342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4171)) := by
  have source := ElevenTheory.theory1950 t (m.theta 3 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule10342 (meaning t m 2027) (meaning t m 2528) (meaning t m 2668) (meaning t m 3693) (meaning t m 4037) (meaning t m 4134) (meaning t m 4171) source

theorem rule10344 (p2027 p2749 p2952 p2992 p3361 p3688 p4842 : Prop) (h : (¬ p3361) ∨ (¬ p2749) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4842) ∨ (¬ p3688)) : (p2027) ∨ (¬ p2749) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3361) ∨ (¬ p3688) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial10344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory1952 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5)
  exact rule10344 (meaning t m 2027) (meaning t m 2749) (meaning t m 2952) (meaning t m 2992) (meaning t m 3361) (meaning t m 3688) (meaning t m 4842) source

theorem rule10346 (p2027 p2331 p2952 p3986 p4320 p4555 : Prop) (h : (¬ p2952) ∨ (¬ p3986) ∨ (¬ p2331) ∨ (¬ p4555) ∨ (¬ p4320) ∨ p2027) : (p2027) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3986) ∨ (¬ p4320) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial10346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1954 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7)
  exact rule10346 (meaning t m 2027) (meaning t m 2331) (meaning t m 2952) (meaning t m 3986) (meaning t m 4320) (meaning t m 4555) source

theorem rule10347 (p2027 p2383 p3073 p3946 p4171 p4370 p4384 : Prop) (h : (¬ p4171) ∨ (¬ p4370) ∨ (¬ p3073) ∨ p2027 ∨ (¬ p2383) ∨ (¬ p3946) ∨ (¬ p4384)) : (p2027) ∨ (¬ p2383) ∨ (¬ p3073) ∨ (¬ p3946) ∨ (¬ p4171) ∨ (¬ p4370) ∨ (¬ p4384) := by
  classical
  tauto

theorem initial10347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4171)) ∨ (¬ (meaning t m 4370)) ∨ (¬ (meaning t m 4384)) := by
  have source := ElevenTheory.theory1955 t (m.theta 0 6) (m.theta 1 8) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule10347 (meaning t m 2027) (meaning t m 2383) (meaning t m 3073) (meaning t m 3946) (meaning t m 4171) (meaning t m 4370) (meaning t m 4384) source

theorem rule10348 (p2027 p2264 p2651 p3551 p4650 p4849 : Prop) (h : (¬ p2651) ∨ (¬ p4650) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p2264) ∨ (¬ p4849)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2651) ∨ (¬ p3551) ∨ (¬ p4650) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial10348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4650)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory1956 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule10348 (meaning t m 2027) (meaning t m 2264) (meaning t m 2651) (meaning t m 3551) (meaning t m 4650) (meaning t m 4849) source

theorem rule10349 (p2027 p2499 p2922 p3568 p4710 p4973 : Prop) (h : (¬ p2922) ∨ (¬ p4973) ∨ (¬ p2499) ∨ (¬ p3568) ∨ (¬ p4710) ∨ p2027) : (p2027) ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3568) ∨ (¬ p4710) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial10349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory1957 t (m.theta 1 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule10349 (meaning t m 2027) (meaning t m 2499) (meaning t m 2922) (meaning t m 3568) (meaning t m 4710) (meaning t m 4973) source

theorem rule10350 (p2027 p2299 p2911 p3568 p3920 p4973 : Prop) (h : (¬ p2911) ∨ (¬ p4973) ∨ (¬ p3568) ∨ p2027 ∨ (¬ p3920) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3568) ∨ (¬ p3920) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial10350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory1958 t (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule10350 (meaning t m 2027) (meaning t m 2299) (meaning t m 2911) (meaning t m 3568) (meaning t m 3920) (meaning t m 4973) source

theorem rule10356 (p2027 p2230 p2528 p2577 p3857 p4197 p4608 : Prop) (h : (¬ p4608) ∨ (¬ p4197) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2528) ∨ (¬ p2577) ∨ (¬ p3857)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2528) ∨ (¬ p2577) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial10356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory1964 t (m.theta 0 4) (m.theta 0 6) (m.theta 0 8) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule10356 (meaning t m 2027) (meaning t m 2230) (meaning t m 2528) (meaning t m 2577) (meaning t m 3857) (meaning t m 4197) (meaning t m 4608) source

theorem rule10357 (p2027 p2311 p2383 p2396 p3821 p4405 : Prop) (h : (¬ p2311) ∨ (¬ p4405) ∨ (¬ p2396) ∨ (¬ p2383) ∨ (¬ p3821) ∨ p2027) : (p2027) ∨ (¬ p2311) ∨ (¬ p2383) ∨ (¬ p2396) ∨ (¬ p3821) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial10357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory1965 t (m.theta 0 6) (m.theta 0 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule10357 (meaning t m 2027) (meaning t m 2311) (meaning t m 2383) (meaning t m 2396) (meaning t m 3821) (meaning t m 4405) source

theorem rule10358 (p2027 p2383 p3743 p3744 p3979 p4171 p5122 : Prop) (h : (¬ p2383) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p3979) ∨ (¬ p3743) ∨ (¬ p5122) ∨ (¬ p4171)) : (p2027) ∨ (¬ p2383) ∨ (¬ p3743) ∨ (¬ p3744) ∨ (¬ p3979) ∨ (¬ p4171) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial10358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4171)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory1966 t (m.theta 0 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10) (m.theta 8 9)
  exact rule10358 (meaning t m 2027) (meaning t m 2383) (meaning t m 3743) (meaning t m 3744) (meaning t m 3979) (meaning t m 4171) (meaning t m 5122) source

theorem rule10361 (p2027 p2911 p3556 p3570 p3741 p4533 : Prop) (h : p2027 ∨ (¬ p4533) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial10361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory1969 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule10361 (meaning t m 2027) (meaning t m 2911) (meaning t m 3556) (meaning t m 3570) (meaning t m 3741) (meaning t m 4533) source

theorem rule10362 (p2027 p2298 p2641 p2996 p4228 p5477 : Prop) (h : (¬ p2641) ∨ (¬ p2298) ∨ (¬ p5477) ∨ (¬ p4228) ∨ p2027 ∨ (¬ p2996)) : (p2027) ∨ (¬ p2298) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p4228) ∨ (¬ p5477) := by
  classical
  tauto

theorem initial10362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 5477)) := by
  have source := ElevenTheory.theory1970 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 10) (m.theta 6 7)
  exact rule10362 (meaning t m 2027) (meaning t m 2298) (meaning t m 2641) (meaning t m 2996) (meaning t m 4228) (meaning t m 5477) source

theorem rule10363 (p2027 p2807 p2911 p3172 p4327 p4548 : Prop) (h : p2027 ∨ (¬ p4327) ∨ (¬ p2911) ∨ (¬ p3172) ∨ (¬ p4548) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2807) ∨ (¬ p2911) ∨ (¬ p3172) ∨ (¬ p4327) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial10363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4327)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory1971 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 7) (m.theta 7 8)
  exact rule10363 (meaning t m 2027) (meaning t m 2807) (meaning t m 2911) (meaning t m 3172) (meaning t m 4327) (meaning t m 4548) source

theorem rule10364 (p2027 p3319 p3662 p4037 p4566 p4759 : Prop) (h : (¬ p4037) ∨ (¬ p4759) ∨ (¬ p3662) ∨ (¬ p3319) ∨ (¬ p4566) ∨ p2027) : (p2027) ∨ (¬ p3319) ∨ (¬ p3662) ∨ (¬ p4037) ∨ (¬ p4566) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial10364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4566)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory1972 t (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 6) (m.theta 6 9)
  exact rule10364 (meaning t m 2027) (meaning t m 3319) (meaning t m 3662) (meaning t m 4037) (meaning t m 4566) (meaning t m 4759) source

theorem rule10365 (p2027 p2459 p2499 p2881 p3051 p3452 p4137 p4521 p4604 : Prop) (h : (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4521) ∨ (¬ p2881) ∨ (¬ p2499) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3452) ∨ (¬ p4137) ∨ (¬ p4521) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial10365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory1973 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule10365 (meaning t m 2027) (meaning t m 2459) (meaning t m 2499) (meaning t m 2881) (meaning t m 3051) (meaning t m 3452) (meaning t m 4137) (meaning t m 4521) (meaning t m 4604) source

theorem rule10366 (p2027 p2656 p2727 p3389 p3662 p3879 p4646 : Prop) (h : (¬ p2727) ∨ (¬ p3879) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p4646) ∨ (¬ p3389) ∨ (¬ p2656)) : (p2027) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3389) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial10366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory1974 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7)
  exact rule10366 (meaning t m 2027) (meaning t m 2656) (meaning t m 2727) (meaning t m 3389) (meaning t m 3662) (meaning t m 3879) (meaning t m 4646) source

theorem rule10367 (p2027 p2341 p2427 p3553 p3691 p4386 p4702 : Prop) (h : p2027 ∨ (¬ p4386) ∨ (¬ p3691) ∨ (¬ p3553) ∨ (¬ p4702) ∨ (¬ p2427) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2427) ∨ (¬ p3553) ∨ (¬ p3691) ∨ (¬ p4386) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial10367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory1975 t (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule10367 (meaning t m 2027) (meaning t m 2341) (meaning t m 2427) (meaning t m 3553) (meaning t m 3691) (meaning t m 4386) (meaning t m 4702) source

theorem rule10368 (p2027 p3570 p3875 p4149 p4647 p5558 : Prop) (h : (¬ p5558) ∨ (¬ p3570) ∨ (¬ p3875) ∨ p2027 ∨ (¬ p4149) ∨ (¬ p4647)) : (p2027) ∨ (¬ p3570) ∨ (¬ p3875) ∨ (¬ p4149) ∨ (¬ p4647) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial10368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory1976 t (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10)
  exact rule10368 (meaning t m 2027) (meaning t m 3570) (meaning t m 3875) (meaning t m 4149) (meaning t m 4647) (meaning t m 5558) source

theorem rule10369 (p2027 p2911 p3551 p3741 p4283 p4320 p4702 : Prop) (h : (¬ p2911) ∨ (¬ p3741) ∨ (¬ p4702) ∨ p2027 ∨ (¬ p4320) ∨ (¬ p4283) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial10369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory1977 t (m.theta 0 7) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule10369 (meaning t m 2027) (meaning t m 2911) (meaning t m 3551) (meaning t m 3741) (meaning t m 4283) (meaning t m 4320) (meaning t m 4702) source

theorem rule10371 (p2027 p3256 p3692 p3988 p4237 p4320 p4555 : Prop) (h : (¬ p4320) ∨ (¬ p3988) ∨ (¬ p4555) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p4237)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4237) ∨ (¬ p4320) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial10371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1979 t (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule10371 (meaning t m 2027) (meaning t m 3256) (meaning t m 3692) (meaning t m 3988) (meaning t m 4237) (meaning t m 4320) (meaning t m 4555) source

theorem rule10372 (p2027 p2274 p2563 p3568 p4153 p4702 : Prop) (h : (¬ p4702) ∨ (¬ p2563) ∨ (¬ p3568) ∨ p2027 ∨ (¬ p4153) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3568) ∨ (¬ p4153) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial10372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory1980 t (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule10372 (meaning t m 2027) (meaning t m 2274) (meaning t m 2563) (meaning t m 3568) (meaning t m 4153) (meaning t m 4702) source

theorem rule10377 (p2027 p2156 p2427 p3556 p3745 p4153 p4702 : Prop) (h : p2027 ∨ (¬ p4153) ∨ (¬ p3556) ∨ (¬ p2427) ∨ (¬ p2156) ∨ (¬ p4702) ∨ (¬ p3745)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3745) ∨ (¬ p4153) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial10377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory1985 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule10377 (meaning t m 2027) (meaning t m 2156) (meaning t m 2427) (meaning t m 3556) (meaning t m 3745) (meaning t m 4153) (meaning t m 4702) source

theorem rule10379 (p2027 p2192 p2662 p2996 p3646 p3904 p4365 p4650 : Prop) (h : (¬ p2192) ∨ (¬ p4365) ∨ (¬ p3646) ∨ (¬ p2996) ∨ (¬ p2662) ∨ (¬ p3904) ∨ p2027 ∨ (¬ p4650)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2662) ∨ (¬ p2996) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4365) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial10379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory1987 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 7) (m.theta 5 6)
  exact rule10379 (meaning t m 2027) (meaning t m 2192) (meaning t m 2662) (meaning t m 2996) (meaning t m 3646) (meaning t m 3904) (meaning t m 4365) (meaning t m 4650) source

theorem rule10381 (p2027 p3888 p3956 p4771 p5584 p5600 : Prop) (h : (¬ p3888) ∨ (¬ p4771) ∨ (¬ p3956) ∨ (¬ p5584) ∨ p2027 ∨ (¬ p5600)) : (p2027) ∨ (¬ p3888) ∨ (¬ p3956) ∨ (¬ p4771) ∨ (¬ p5584) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial10381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4771)) ∨ (¬ (meaning t m 5584)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory1989 t (m.theta 3 8) (m.theta 4 6) (m.theta 6 10) (m.theta 6 8) (m.theta 8 10)
  exact rule10381 (meaning t m 2027) (meaning t m 3888) (meaning t m 3956) (meaning t m 4771) (meaning t m 5584) (meaning t m 5600) source

theorem rule10383 (p2027 p2427 p3222 p3486 p4202 p4953 : Prop) (h : (¬ p3486) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p4953) ∨ (¬ p3222) ∨ (¬ p4202)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3222) ∨ (¬ p3486) ∨ (¬ p4202) ∨ (¬ p4953) := by
  classical
  tauto

theorem initial10383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4953)) := by
  have source := ElevenTheory.theory1991 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 7)
  exact rule10383 (meaning t m 2027) (meaning t m 2427) (meaning t m 3222) (meaning t m 3486) (meaning t m 4202) (meaning t m 4953) source

theorem rule10385 (p2027 p2088 p2475 p2518 p3878 p4118 p4814 : Prop) (h : (¬ p2475) ∨ (¬ p4814) ∨ (¬ p4118) ∨ (¬ p3878) ∨ (¬ p2088) ∨ (¬ p2518) ∨ p2027) : (p2027) ∨ (¬ p2088) ∨ (¬ p2475) ∨ (¬ p2518) ∨ (¬ p3878) ∨ (¬ p4118) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial10385 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3878)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory1993 t (m.theta 0 8) (m.theta 1 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule10385 (meaning t m 2027) (meaning t m 2088) (meaning t m 2475) (meaning t m 2518) (meaning t m 3878) (meaning t m 4118) (meaning t m 4814) source

theorem rule10386 (p2027 p3073 p3266 p4322 p4335 p4498 : Prop) (h : (¬ p4498) ∨ (¬ p4335) ∨ (¬ p3073) ∨ (¬ p3266) ∨ (¬ p4322) ∨ p2027) : (p2027) ∨ (¬ p3073) ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p4498) := by
  classical
  tauto

theorem initial10386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4498)) := by
  have source := ElevenTheory.theory1994 t (m.theta 1 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule10386 (meaning t m 2027) (meaning t m 3073) (meaning t m 3266) (meaning t m 4322) (meaning t m 4335) (meaning t m 4498) source

theorem rule10387 (p2027 p2166 p3146 p3661 p4118 p4960 : Prop) (h : (¬ p3661) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p4960) ∨ (¬ p4118) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial10387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory1995 t (m.theta 1 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule10387 (meaning t m 2027) (meaning t m 2166) (meaning t m 3146) (meaning t m 3661) (meaning t m 4118) (meaning t m 4960) source

theorem rule10388 (p2027 p2274 p2284 p4033 p4208 p4620 : Prop) (h : (¬ p4620) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p4033) ∨ (¬ p4208)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p4033) ∨ (¬ p4208) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial10388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory1996 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule10388 (meaning t m 2027) (meaning t m 2274) (meaning t m 2284) (meaning t m 4033) (meaning t m 4208) (meaning t m 4620) source

theorem rule10392 (p2027 p2352 p2493 p3324 p4194 p4814 : Prop) (h : (¬ p3324) ∨ (¬ p4194) ∨ (¬ p4814) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p2493)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3324) ∨ (¬ p4194) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial10392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory2000 t (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule10392 (meaning t m 2027) (meaning t m 2352) (meaning t m 2493) (meaning t m 3324) (meaning t m 4194) (meaning t m 4814) source

theorem rule10393 (p2027 p2493 p2598 p2780 p4342 p5217 : Prop) (h : (¬ p5217) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p4342) ∨ (¬ p2598) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4342) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial10393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory2001 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6)
  exact rule10393 (meaning t m 2027) (meaning t m 2493) (meaning t m 2598) (meaning t m 2780) (meaning t m 4342) (meaning t m 5217) source

theorem rule10394 (p2027 p2406 p2563 p3646 p3904 p5191 : Prop) (h : (¬ p2406) ∨ (¬ p3904) ∨ (¬ p5191) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p3646)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p5191) := by
  classical
  tauto

theorem initial10394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 5191)) := by
  have source := ElevenTheory.theory2002 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6)
  exact rule10394 (meaning t m 2027) (meaning t m 2406) (meaning t m 2563) (meaning t m 3646) (meaning t m 3904) (meaning t m 5191) source

theorem rule10413 (p2027 p2598 p2922 p3425 p4106 p5217 : Prop) (h : (¬ p2598) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p5217) ∨ (¬ p4106) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2922) ∨ (¬ p3425) ∨ (¬ p4106) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial10413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory2005 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7)
  exact rule10413 (meaning t m 2027) (meaning t m 2598) (meaning t m 2922) (meaning t m 3425) (meaning t m 4106) (meaning t m 5217) source

theorem rule10415 (p2027 p2475 p2518 p2630 p3177 p3877 p4814 : Prop) (h : p2027 ∨ (¬ p2518) ∨ (¬ p4814) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p2475) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2475) ∨ (¬ p2518) ∨ (¬ p2630) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial10415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory2007 t (m.theta 0 8) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule10415 (meaning t m 2027) (meaning t m 2475) (meaning t m 2518) (meaning t m 2630) (meaning t m 3177) (meaning t m 3877) (meaning t m 4814) source

theorem rule10417 (p2027 p2341 p2922 p3575 p3659 p3686 p5217 : Prop) (h : (¬ p3686) ∨ (¬ p3575) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p5217) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2922) ∨ (¬ p3575) ∨ (¬ p3659) ∨ (¬ p3686) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial10417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory2009 t (m.theta 0 7) (m.theta 1 4) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule10417 (meaning t m 2027) (meaning t m 2341) (meaning t m 2922) (meaning t m 3575) (meaning t m 3659) (meaning t m 3686) (meaning t m 5217) source

theorem rule10419 (p2027 p2441 p2589 p3093 p3309 p3921 p5193 : Prop) (h : p2027 ∨ (¬ p5193) ∨ (¬ p3093) ∨ (¬ p2589) ∨ (¬ p2441) ∨ (¬ p3309) ∨ (¬ p3921)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3921) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial10419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory2011 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7)
  exact rule10419 (meaning t m 2027) (meaning t m 2441) (meaning t m 2589) (meaning t m 3093) (meaning t m 3309) (meaning t m 3921) (meaning t m 5193) source

end SunPrize.SMT
