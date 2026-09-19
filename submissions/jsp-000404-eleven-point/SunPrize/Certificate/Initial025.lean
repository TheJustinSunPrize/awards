import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory012
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule12613 (p4136 p4169 p4244 p4894 p4895 : Prop) : (p4136) ∨ (((¬ p4169) ∨ (¬ p4244) ∨ (¬ p4136) ∨ (¬ p4894) ∨ (¬ p4895))) := by
  classical
  tauto

theorem initial12613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4136) ∨ (meaning t m 5938) := by
  exact rule12613 (meaning t m 4136) (meaning t m 4169) (meaning t m 4244) (meaning t m 4894) (meaning t m 4895)

theorem rule12615 (p4136 p4169 p4244 p4894 p4895 : Prop) : (p4895) ∨ (((¬ p4169) ∨ (¬ p4244) ∨ (¬ p4136) ∨ (¬ p4894) ∨ (¬ p4895))) := by
  classical
  tauto

theorem initial12615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4895) ∨ (meaning t m 5938) := by
  exact rule12615 (meaning t m 4136) (meaning t m 4169) (meaning t m 4244) (meaning t m 4894) (meaning t m 4895)

theorem rule12617 (p2870 p3587 p4344 p4897 p4898 : Prop) : (p4344) ∨ (((¬ p4344) ∨ (¬ p3587) ∨ (¬ p2870) ∨ (¬ p4897) ∨ (¬ p4898))) := by
  classical
  tauto

theorem initial12617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4344) ∨ (meaning t m 5939) := by
  exact rule12617 (meaning t m 2870) (meaning t m 3587) (meaning t m 4344) (meaning t m 4897) (meaning t m 4898)

theorem rule12618 (p2870 p3587 p4344 p4897 p4898 : Prop) : (p3587) ∨ (((¬ p4344) ∨ (¬ p3587) ∨ (¬ p2870) ∨ (¬ p4897) ∨ (¬ p4898))) := by
  classical
  tauto

theorem initial12618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3587) ∨ (meaning t m 5939) := by
  exact rule12618 (meaning t m 2870) (meaning t m 3587) (meaning t m 4344) (meaning t m 4897) (meaning t m 4898)

theorem rule12619 (p2870 p3587 p4344 p4897 p4898 : Prop) : (p2870) ∨ (((¬ p4344) ∨ (¬ p3587) ∨ (¬ p2870) ∨ (¬ p4897) ∨ (¬ p4898))) := by
  classical
  tauto

theorem initial12619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2870) ∨ (meaning t m 5939) := by
  exact rule12619 (meaning t m 2870) (meaning t m 3587) (meaning t m 4344) (meaning t m 4897) (meaning t m 4898)

theorem rule12620 (p2870 p3587 p4344 p4897 p4898 : Prop) : (p4897) ∨ (((¬ p4344) ∨ (¬ p3587) ∨ (¬ p2870) ∨ (¬ p4897) ∨ (¬ p4898))) := by
  classical
  tauto

theorem initial12620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4897) ∨ (meaning t m 5939) := by
  exact rule12620 (meaning t m 2870) (meaning t m 3587) (meaning t m 4344) (meaning t m 4897) (meaning t m 4898)

theorem rule12625 (p5938 p5939 : Prop) : (¬ ((¬ p5938) ∨ (¬ p5939))) ∨ (¬ p5938) ∨ (¬ p5939) := by
  classical
  tauto

theorem initial12625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5937)) ∨ (¬ (meaning t m 5938)) ∨ (¬ (meaning t m 5939)) := by
  exact rule12625 (meaning t m 5938) (meaning t m 5939)

theorem rule12626 (p4892 p5937 : Prop) (h : (p4892 ↔ p5937)) : (¬ p4892) ∨ (p5937) := by
  classical
  tauto

theorem initial12626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4892)) ∨ (meaning t m 5937) := by
  have source := ElevenTheory.theory3291 t (m.theta 2 5) (m.theta 2 7) (m.theta 5 7)
  exact rule12626 (meaning t m 4892) (meaning t m 5937) source

theorem rule12628 (p2137 p3051 p4244 : Prop) (h : (¬ p3051) ∨ (¬ p4244) ∨ (¬ p2137)) : (¬ p2137) ∨ (¬ p3051) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial12628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory3292 (m.theta 0 5) (m.theta 2 5) (m.theta 5 7)
  exact rule12628 (meaning t m 2137) (meaning t m 3051) (meaning t m 4244) source

theorem rule12629 (p1982 p2027 p2459 p2608 p2699 p2707 p2717 : Prop) (h : (¬ p2717) ∨ p2699 ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2707) ∨ (¬ p2608)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p2717) := by
  classical
  tauto

theorem initial12629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) := by
  have source := ElevenTheory.theory3293 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule12629 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2608) (meaning t m 2699) (meaning t m 2707) (meaning t m 2717) source

theorem rule12630 (p3570 p4119 p4132 p4901 p4902 : Prop) : (p4132) ∨ (((¬ p4132) ∨ (¬ p3570) ∨ (¬ p4119) ∨ (¬ p4901) ∨ (¬ p4902))) := by
  classical
  tauto

theorem initial12630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4132) ∨ (meaning t m 5941) := by
  exact rule12630 (meaning t m 3570) (meaning t m 4119) (meaning t m 4132) (meaning t m 4901) (meaning t m 4902)

theorem rule12631 (p3570 p4119 p4132 p4901 p4902 : Prop) : (p3570) ∨ (((¬ p4132) ∨ (¬ p3570) ∨ (¬ p4119) ∨ (¬ p4901) ∨ (¬ p4902))) := by
  classical
  tauto

theorem initial12631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3570) ∨ (meaning t m 5941) := by
  exact rule12631 (meaning t m 3570) (meaning t m 4119) (meaning t m 4132) (meaning t m 4901) (meaning t m 4902)

theorem rule12632 (p3570 p4119 p4132 p4901 p4902 : Prop) : (p4119) ∨ (((¬ p4132) ∨ (¬ p3570) ∨ (¬ p4119) ∨ (¬ p4901) ∨ (¬ p4902))) := by
  classical
  tauto

theorem initial12632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4119) ∨ (meaning t m 5941) := by
  exact rule12632 (meaning t m 3570) (meaning t m 4119) (meaning t m 4132) (meaning t m 4901) (meaning t m 4902)

theorem rule12633 (p3570 p4119 p4132 p4901 p4902 : Prop) : (p4901) ∨ (((¬ p4132) ∨ (¬ p3570) ∨ (¬ p4119) ∨ (¬ p4901) ∨ (¬ p4902))) := by
  classical
  tauto

theorem initial12633 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4901) ∨ (meaning t m 5941) := by
  exact rule12633 (meaning t m 3570) (meaning t m 4119) (meaning t m 4132) (meaning t m 4901) (meaning t m 4902)

theorem rule12636 (p2881 p3747 p4042 p4904 p4905 : Prop) : (p4042) ∨ (((¬ p4042) ∨ (¬ p3747) ∨ (¬ p2881) ∨ (¬ p4904) ∨ (¬ p4905))) := by
  classical
  tauto

theorem initial12636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4042) ∨ (meaning t m 5942) := by
  exact rule12636 (meaning t m 2881) (meaning t m 3747) (meaning t m 4042) (meaning t m 4904) (meaning t m 4905)

theorem rule12637 (p2881 p3747 p4042 p4904 p4905 : Prop) : (p3747) ∨ (((¬ p4042) ∨ (¬ p3747) ∨ (¬ p2881) ∨ (¬ p4904) ∨ (¬ p4905))) := by
  classical
  tauto

theorem initial12637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3747) ∨ (meaning t m 5942) := by
  exact rule12637 (meaning t m 2881) (meaning t m 3747) (meaning t m 4042) (meaning t m 4904) (meaning t m 4905)

theorem rule12638 (p2881 p3747 p4042 p4904 p4905 : Prop) : (p2881) ∨ (((¬ p4042) ∨ (¬ p3747) ∨ (¬ p2881) ∨ (¬ p4904) ∨ (¬ p4905))) := by
  classical
  tauto

theorem initial12638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2881) ∨ (meaning t m 5942) := by
  exact rule12638 (meaning t m 2881) (meaning t m 3747) (meaning t m 4042) (meaning t m 4904) (meaning t m 4905)

theorem rule12639 (p2881 p3747 p4042 p4904 p4905 : Prop) : (p4904) ∨ (((¬ p4042) ∨ (¬ p3747) ∨ (¬ p2881) ∨ (¬ p4904) ∨ (¬ p4905))) := by
  classical
  tauto

theorem initial12639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4904) ∨ (meaning t m 5942) := by
  exact rule12639 (meaning t m 2881) (meaning t m 3747) (meaning t m 4042) (meaning t m 4904) (meaning t m 4905)

theorem rule12644 (p5941 p5942 : Prop) : (¬ ((¬ p5941) ∨ (¬ p5942))) ∨ (¬ p5941) ∨ (¬ p5942) := by
  classical
  tauto

theorem initial12644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5940)) ∨ (¬ (meaning t m 5941)) ∨ (¬ (meaning t m 5942)) := by
  exact rule12644 (meaning t m 5941) (meaning t m 5942)

theorem rule12645 (p4899 p5940 : Prop) (h : (p4899 ↔ p5940)) : (¬ p4899) ∨ (p5940) := by
  classical
  tauto

theorem initial12645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4899)) ∨ (meaning t m 5940) := by
  have source := ElevenTheory.theory3294 t (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule12645 (meaning t m 4899) (meaning t m 5940) source

theorem rule12647 (p3486 p3554 p4909 p4910 p4911 : Prop) : (p4909) ∨ (((¬ p4909) ∨ (¬ p3486) ∨ (¬ p3554) ∨ (¬ p4910) ∨ (¬ p4911))) := by
  classical
  tauto

theorem initial12647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4909) ∨ (meaning t m 5944) := by
  exact rule12647 (meaning t m 3486) (meaning t m 3554) (meaning t m 4909) (meaning t m 4910) (meaning t m 4911)

theorem rule12648 (p3486 p3554 p4909 p4910 p4911 : Prop) : (p3486) ∨ (((¬ p4909) ∨ (¬ p3486) ∨ (¬ p3554) ∨ (¬ p4910) ∨ (¬ p4911))) := by
  classical
  tauto

theorem initial12648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3486) ∨ (meaning t m 5944) := by
  exact rule12648 (meaning t m 3486) (meaning t m 3554) (meaning t m 4909) (meaning t m 4910) (meaning t m 4911)

theorem rule12649 (p3486 p3554 p4909 p4910 p4911 : Prop) : (p3554) ∨ (((¬ p4909) ∨ (¬ p3486) ∨ (¬ p3554) ∨ (¬ p4910) ∨ (¬ p4911))) := by
  classical
  tauto

theorem initial12649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3554) ∨ (meaning t m 5944) := by
  exact rule12649 (meaning t m 3486) (meaning t m 3554) (meaning t m 4909) (meaning t m 4910) (meaning t m 4911)

theorem rule12651 (p3486 p3554 p4909 p4910 p4911 : Prop) : (p4911) ∨ (((¬ p4909) ∨ (¬ p3486) ∨ (¬ p3554) ∨ (¬ p4910) ∨ (¬ p4911))) := by
  classical
  tauto

theorem initial12651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4911) ∨ (meaning t m 5944) := by
  exact rule12651 (meaning t m 3486) (meaning t m 3554) (meaning t m 4909) (meaning t m 4910) (meaning t m 4911)

theorem rule12653 (p2891 p3571 p4431 p4913 p4914 : Prop) : (p3571) ∨ (((¬ p3571) ∨ (¬ p4431) ∨ (¬ p2891) ∨ (¬ p4913) ∨ (¬ p4914))) := by
  classical
  tauto

theorem initial12653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3571) ∨ (meaning t m 5945) := by
  exact rule12653 (meaning t m 2891) (meaning t m 3571) (meaning t m 4431) (meaning t m 4913) (meaning t m 4914)

theorem rule12654 (p2891 p3571 p4431 p4913 p4914 : Prop) : (p4431) ∨ (((¬ p3571) ∨ (¬ p4431) ∨ (¬ p2891) ∨ (¬ p4913) ∨ (¬ p4914))) := by
  classical
  tauto

theorem initial12654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4431) ∨ (meaning t m 5945) := by
  exact rule12654 (meaning t m 2891) (meaning t m 3571) (meaning t m 4431) (meaning t m 4913) (meaning t m 4914)

theorem rule12655 (p2891 p3571 p4431 p4913 p4914 : Prop) : (p2891) ∨ (((¬ p3571) ∨ (¬ p4431) ∨ (¬ p2891) ∨ (¬ p4913) ∨ (¬ p4914))) := by
  classical
  tauto

theorem initial12655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2891) ∨ (meaning t m 5945) := by
  exact rule12655 (meaning t m 2891) (meaning t m 3571) (meaning t m 4431) (meaning t m 4913) (meaning t m 4914)

theorem rule12657 (p2891 p3571 p4431 p4913 p4914 : Prop) : (p4914) ∨ (((¬ p3571) ∨ (¬ p4431) ∨ (¬ p2891) ∨ (¬ p4913) ∨ (¬ p4914))) := by
  classical
  tauto

theorem initial12657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4914) ∨ (meaning t m 5945) := by
  exact rule12657 (meaning t m 2891) (meaning t m 3571) (meaning t m 4431) (meaning t m 4913) (meaning t m 4914)

theorem rule12661 (p5944 p5945 : Prop) : (¬ ((¬ p5944) ∨ (¬ p5945))) ∨ (¬ p5944) ∨ (¬ p5945) := by
  classical
  tauto

theorem initial12661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5943)) ∨ (¬ (meaning t m 5944)) ∨ (¬ (meaning t m 5945)) := by
  exact rule12661 (meaning t m 5944) (meaning t m 5945)

theorem rule12662 (p4907 p5943 : Prop) (h : (p4907 ↔ p5943)) : (¬ p4907) ∨ (p5943) := by
  classical
  tauto

theorem initial12662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4907)) ∨ (meaning t m 5943) := by
  have source := ElevenTheory.theory3295 t (m.theta 1 5) (m.theta 1 7) (m.theta 5 7)
  exact rule12662 (meaning t m 4907) (meaning t m 5943) source

theorem rule12664 (p3699 p4280 p4320 p4386 p4917 : Prop) : (p3699) ∨ (((¬ p3699) ∨ (¬ p4320) ∨ (¬ p4386) ∨ (¬ p4917) ∨ (¬ p4280))) := by
  classical
  tauto

theorem initial12664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3699) ∨ (meaning t m 5947) := by
  exact rule12664 (meaning t m 3699) (meaning t m 4280) (meaning t m 4320) (meaning t m 4386) (meaning t m 4917)

theorem rule12665 (p3699 p4280 p4320 p4386 p4917 : Prop) : (p4320) ∨ (((¬ p3699) ∨ (¬ p4320) ∨ (¬ p4386) ∨ (¬ p4917) ∨ (¬ p4280))) := by
  classical
  tauto

theorem initial12665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4320) ∨ (meaning t m 5947) := by
  exact rule12665 (meaning t m 3699) (meaning t m 4280) (meaning t m 4320) (meaning t m 4386) (meaning t m 4917)

theorem rule12666 (p3699 p4280 p4320 p4386 p4917 : Prop) : (p4386) ∨ (((¬ p3699) ∨ (¬ p4320) ∨ (¬ p4386) ∨ (¬ p4917) ∨ (¬ p4280))) := by
  classical
  tauto

theorem initial12666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4386) ∨ (meaning t m 5947) := by
  exact rule12666 (meaning t m 3699) (meaning t m 4280) (meaning t m 4320) (meaning t m 4386) (meaning t m 4917)

theorem rule12667 (p3699 p4280 p4320 p4386 p4917 : Prop) : (p4917) ∨ (((¬ p3699) ∨ (¬ p4320) ∨ (¬ p4386) ∨ (¬ p4917) ∨ (¬ p4280))) := by
  classical
  tauto

theorem initial12667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4917) ∨ (meaning t m 5947) := by
  exact rule12667 (meaning t m 3699) (meaning t m 4280) (meaning t m 4320) (meaning t m 4386) (meaning t m 4917)

theorem rule12670 (p2901 p2995 p4333 p4362 p4919 : Prop) : (p4333) ∨ (((¬ p4333) ∨ (¬ p2995) ∨ (¬ p2901) ∨ (¬ p4919) ∨ (¬ p4362))) := by
  classical
  tauto

theorem initial12670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4333) ∨ (meaning t m 5948) := by
  exact rule12670 (meaning t m 2901) (meaning t m 2995) (meaning t m 4333) (meaning t m 4362) (meaning t m 4919)

theorem rule12671 (p2901 p2995 p4333 p4362 p4919 : Prop) : (p2995) ∨ (((¬ p4333) ∨ (¬ p2995) ∨ (¬ p2901) ∨ (¬ p4919) ∨ (¬ p4362))) := by
  classical
  tauto

theorem initial12671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2995) ∨ (meaning t m 5948) := by
  exact rule12671 (meaning t m 2901) (meaning t m 2995) (meaning t m 4333) (meaning t m 4362) (meaning t m 4919)

theorem rule12672 (p2901 p2995 p4333 p4362 p4919 : Prop) : (p2901) ∨ (((¬ p4333) ∨ (¬ p2995) ∨ (¬ p2901) ∨ (¬ p4919) ∨ (¬ p4362))) := by
  classical
  tauto

theorem initial12672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2901) ∨ (meaning t m 5948) := by
  exact rule12672 (meaning t m 2901) (meaning t m 2995) (meaning t m 4333) (meaning t m 4362) (meaning t m 4919)

theorem rule12673 (p2901 p2995 p4333 p4362 p4919 : Prop) : (p4919) ∨ (((¬ p4333) ∨ (¬ p2995) ∨ (¬ p2901) ∨ (¬ p4919) ∨ (¬ p4362))) := by
  classical
  tauto

theorem initial12673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4919) ∨ (meaning t m 5948) := by
  exact rule12673 (meaning t m 2901) (meaning t m 2995) (meaning t m 4333) (meaning t m 4362) (meaning t m 4919)

theorem rule12678 (p5947 p5948 : Prop) : (¬ ((¬ p5947) ∨ (¬ p5948))) ∨ (¬ p5947) ∨ (¬ p5948) := by
  classical
  tauto

theorem initial12678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5946)) ∨ (¬ (meaning t m 5947)) ∨ (¬ (meaning t m 5948)) := by
  exact rule12678 (meaning t m 5947) (meaning t m 5948)

theorem rule12679 (p4915 p5946 : Prop) (h : (p4915 ↔ p5946)) : (¬ p4915) ∨ (p5946) := by
  classical
  tauto

theorem initial12679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4915)) ∨ (meaning t m 5946) := by
  have source := ElevenTheory.theory3296 t (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule12679 (meaning t m 4915) (meaning t m 5946) source

theorem rule12681 (p3644 p4186 p4383 p4420 p4922 : Prop) : (p4383) ∨ (((¬ p4383) ∨ (¬ p3644) ∨ (¬ p4186) ∨ (¬ p4922) ∨ (¬ p4420))) := by
  classical
  tauto

theorem initial12681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4383) ∨ (meaning t m 5950) := by
  exact rule12681 (meaning t m 3644) (meaning t m 4186) (meaning t m 4383) (meaning t m 4420) (meaning t m 4922)

theorem rule12682 (p3644 p4186 p4383 p4420 p4922 : Prop) : (p3644) ∨ (((¬ p4383) ∨ (¬ p3644) ∨ (¬ p4186) ∨ (¬ p4922) ∨ (¬ p4420))) := by
  classical
  tauto

theorem initial12682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3644) ∨ (meaning t m 5950) := by
  exact rule12682 (meaning t m 3644) (meaning t m 4186) (meaning t m 4383) (meaning t m 4420) (meaning t m 4922)

theorem rule12683 (p3644 p4186 p4383 p4420 p4922 : Prop) : (p4186) ∨ (((¬ p4383) ∨ (¬ p3644) ∨ (¬ p4186) ∨ (¬ p4922) ∨ (¬ p4420))) := by
  classical
  tauto

theorem initial12683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4186) ∨ (meaning t m 5950) := by
  exact rule12683 (meaning t m 3644) (meaning t m 4186) (meaning t m 4383) (meaning t m 4420) (meaning t m 4922)

theorem rule12684 (p3644 p4186 p4383 p4420 p4922 : Prop) : (p4922) ∨ (((¬ p4383) ∨ (¬ p3644) ∨ (¬ p4186) ∨ (¬ p4922) ∨ (¬ p4420))) := by
  classical
  tauto

theorem initial12684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4922) ∨ (meaning t m 5950) := by
  exact rule12684 (meaning t m 3644) (meaning t m 4186) (meaning t m 4383) (meaning t m 4420) (meaning t m 4922)

theorem rule12687 (p2911 p3875 p4404 p4438 p4924 : Prop) : (p4404) ∨ (((¬ p4404) ∨ (¬ p3875) ∨ (¬ p2911) ∨ (¬ p4924) ∨ (¬ p4438))) := by
  classical
  tauto

theorem initial12687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4404) ∨ (meaning t m 5951) := by
  exact rule12687 (meaning t m 2911) (meaning t m 3875) (meaning t m 4404) (meaning t m 4438) (meaning t m 4924)

theorem rule12688 (p2911 p3875 p4404 p4438 p4924 : Prop) : (p3875) ∨ (((¬ p4404) ∨ (¬ p3875) ∨ (¬ p2911) ∨ (¬ p4924) ∨ (¬ p4438))) := by
  classical
  tauto

theorem initial12688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3875) ∨ (meaning t m 5951) := by
  exact rule12688 (meaning t m 2911) (meaning t m 3875) (meaning t m 4404) (meaning t m 4438) (meaning t m 4924)

theorem rule12689 (p2911 p3875 p4404 p4438 p4924 : Prop) : (p2911) ∨ (((¬ p4404) ∨ (¬ p3875) ∨ (¬ p2911) ∨ (¬ p4924) ∨ (¬ p4438))) := by
  classical
  tauto

theorem initial12689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2911) ∨ (meaning t m 5951) := by
  exact rule12689 (meaning t m 2911) (meaning t m 3875) (meaning t m 4404) (meaning t m 4438) (meaning t m 4924)

theorem rule12691 (p2911 p3875 p4404 p4438 p4924 : Prop) : (p4438) ∨ (((¬ p4404) ∨ (¬ p3875) ∨ (¬ p2911) ∨ (¬ p4924) ∨ (¬ p4438))) := by
  classical
  tauto

theorem initial12691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4438) ∨ (meaning t m 5951) := by
  exact rule12691 (meaning t m 2911) (meaning t m 3875) (meaning t m 4404) (meaning t m 4438) (meaning t m 4924)

theorem rule12695 (p5950 p5951 : Prop) : (¬ ((¬ p5950) ∨ (¬ p5951))) ∨ (¬ p5950) ∨ (¬ p5951) := by
  classical
  tauto

theorem initial12695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5949)) ∨ (¬ (meaning t m 5950)) ∨ (¬ (meaning t m 5951)) := by
  exact rule12695 (meaning t m 5950) (meaning t m 5951)

theorem rule12696 (p4920 p5949 : Prop) (h : (p4920 ↔ p5949)) : (¬ p4920) ∨ (p5949) := by
  classical
  tauto

theorem initial12696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4920)) ∨ (meaning t m 5949) := by
  have source := ElevenTheory.theory3297 t (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule12696 (meaning t m 4920) (meaning t m 5949) source

theorem rule12698 (p1977 p2027 p2633 p2651 p3414 p3644 p3740 p4111 : Prop) (h : (¬ p3644) ∨ (¬ p1977) ∨ (¬ p3414) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p3740) ∨ p2633) : (¬ p1977) ∨ (p2027) ∨ (p2633) ∨ (¬ p2651) ∨ (¬ p3414) ∨ (¬ p3644) ∨ (¬ p3740) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial12698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory3298 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule12698 (meaning t m 1977) (meaning t m 2027) (meaning t m 2633) (meaning t m 2651) (meaning t m 3414) (meaning t m 3644) (meaning t m 3740) (meaning t m 4111) source

theorem rule12699 (p1987 p2027 p2651 p2810 p2938 p2952 p3879 p4235 : Prop) (h : (¬ p2651) ∨ p2938 ∨ (¬ p4235) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p3879) ∨ (¬ p2952) ∨ (¬ p2810)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (p2938) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial12699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory3299 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule12699 (meaning t m 1987) (meaning t m 2027) (meaning t m 2651) (meaning t m 2810) (meaning t m 2938) (meaning t m 2952) (meaning t m 3879) (meaning t m 4235) source

theorem rule12701 (p4363 p4388 p4938 p4939 p4940 : Prop) : (p4388) ∨ (((¬ p4388) ∨ (¬ p4363) ∨ (¬ p4938) ∨ (¬ p4939) ∨ (¬ p4940))) := by
  classical
  tauto

theorem initial12701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4388) ∨ (meaning t m 5953) := by
  exact rule12701 (meaning t m 4363) (meaning t m 4388) (meaning t m 4938) (meaning t m 4939) (meaning t m 4940)

theorem rule12702 (p4363 p4388 p4938 p4939 p4940 : Prop) : (p4363) ∨ (((¬ p4388) ∨ (¬ p4363) ∨ (¬ p4938) ∨ (¬ p4939) ∨ (¬ p4940))) := by
  classical
  tauto

theorem initial12702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4363) ∨ (meaning t m 5953) := by
  exact rule12702 (meaning t m 4363) (meaning t m 4388) (meaning t m 4938) (meaning t m 4939) (meaning t m 4940)

theorem rule12703 (p4363 p4388 p4938 p4939 p4940 : Prop) : (p4938) ∨ (((¬ p4388) ∨ (¬ p4363) ∨ (¬ p4938) ∨ (¬ p4939) ∨ (¬ p4940))) := by
  classical
  tauto

theorem initial12703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4938) ∨ (meaning t m 5953) := by
  exact rule12703 (meaning t m 4363) (meaning t m 4388) (meaning t m 4938) (meaning t m 4939) (meaning t m 4940)

theorem rule12707 (p2972 p4387 p4942 p4943 p4944 : Prop) : (p4387) ∨ (((¬ p4387) ∨ (¬ p4942) ∨ (¬ p2972) ∨ (¬ p4943) ∨ (¬ p4944))) := by
  classical
  tauto

theorem initial12707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4387) ∨ (meaning t m 5954) := by
  exact rule12707 (meaning t m 2972) (meaning t m 4387) (meaning t m 4942) (meaning t m 4943) (meaning t m 4944)

theorem rule12708 (p2972 p4387 p4942 p4943 p4944 : Prop) : (p4942) ∨ (((¬ p4387) ∨ (¬ p4942) ∨ (¬ p2972) ∨ (¬ p4943) ∨ (¬ p4944))) := by
  classical
  tauto

theorem initial12708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4942) ∨ (meaning t m 5954) := by
  exact rule12708 (meaning t m 2972) (meaning t m 4387) (meaning t m 4942) (meaning t m 4943) (meaning t m 4944)

theorem rule12709 (p2972 p4387 p4942 p4943 p4944 : Prop) : (p2972) ∨ (((¬ p4387) ∨ (¬ p4942) ∨ (¬ p2972) ∨ (¬ p4943) ∨ (¬ p4944))) := by
  classical
  tauto

theorem initial12709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2972) ∨ (meaning t m 5954) := by
  exact rule12709 (meaning t m 2972) (meaning t m 4387) (meaning t m 4942) (meaning t m 4943) (meaning t m 4944)

theorem rule12715 (p5953 p5954 : Prop) : (¬ ((¬ p5953) ∨ (¬ p5954))) ∨ (¬ p5953) ∨ (¬ p5954) := by
  classical
  tauto

theorem initial12715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5952)) ∨ (¬ (meaning t m 5953)) ∨ (¬ (meaning t m 5954)) := by
  exact rule12715 (meaning t m 5953) (meaning t m 5954)

theorem rule12716 (p4936 p5952 : Prop) (h : (p4936 ↔ p5952)) : (¬ p4936) ∨ (p5952) := by
  classical
  tauto

theorem initial12716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4936)) ∨ (meaning t m 5952) := by
  have source := ElevenTheory.theory3301 t (m.theta 1 5) (m.theta 1 9) (m.theta 5 9)
  exact rule12716 (meaning t m 4936) (meaning t m 5952) source

theorem rule12718 (p1985 p2027 p2765 p2891 p2982 p4110 p4363 : Prop) (h : (¬ p2891) ∨ p2765 ∨ (¬ p2982) ∨ (¬ p4110) ∨ (¬ p1985) ∨ (¬ p4363) ∨ p2027) : (¬ p1985) ∨ (p2027) ∨ (p2765) ∨ (¬ p2891) ∨ (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial12718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory3302 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule12718 (meaning t m 1985) (meaning t m 2027) (meaning t m 2765) (meaning t m 2891) (meaning t m 2982) (meaning t m 4110) (meaning t m 4363) source

theorem rule12719 (p3237 p4947 p4948 p4949 p4950 : Prop) : (p4947) ∨ (((¬ p4947) ∨ (¬ p4948) ∨ (¬ p3237) ∨ (¬ p4949) ∨ (¬ p4950))) := by
  classical
  tauto

theorem initial12719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4947) ∨ (meaning t m 5956) := by
  exact rule12719 (meaning t m 3237) (meaning t m 4947) (meaning t m 4948) (meaning t m 4949) (meaning t m 4950)

theorem rule12720 (p3237 p4947 p4948 p4949 p4950 : Prop) : (p4948) ∨ (((¬ p4947) ∨ (¬ p4948) ∨ (¬ p3237) ∨ (¬ p4949) ∨ (¬ p4950))) := by
  classical
  tauto

theorem initial12720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4948) ∨ (meaning t m 5956) := by
  exact rule12720 (meaning t m 3237) (meaning t m 4947) (meaning t m 4948) (meaning t m 4949) (meaning t m 4950)

theorem rule12721 (p3237 p4947 p4948 p4949 p4950 : Prop) : (p3237) ∨ (((¬ p4947) ∨ (¬ p4948) ∨ (¬ p3237) ∨ (¬ p4949) ∨ (¬ p4950))) := by
  classical
  tauto

theorem initial12721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3237) ∨ (meaning t m 5956) := by
  exact rule12721 (meaning t m 3237) (meaning t m 4947) (meaning t m 4948) (meaning t m 4949) (meaning t m 4950)

theorem rule12723 (p3237 p4947 p4948 p4949 p4950 : Prop) : (p4950) ∨ (((¬ p4947) ∨ (¬ p4948) ∨ (¬ p3237) ∨ (¬ p4949) ∨ (¬ p4950))) := by
  classical
  tauto

theorem initial12723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4950) ∨ (meaning t m 5956) := by
  exact rule12723 (meaning t m 3237) (meaning t m 4947) (meaning t m 4948) (meaning t m 4949) (meaning t m 4950)

theorem rule12725 (p2982 p4449 p4952 p4953 p4954 : Prop) : (p4952) ∨ (((¬ p4952) ∨ (¬ p4449) ∨ (¬ p2982) ∨ (¬ p4953) ∨ (¬ p4954))) := by
  classical
  tauto

theorem initial12725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4952) ∨ (meaning t m 5957) := by
  exact rule12725 (meaning t m 2982) (meaning t m 4449) (meaning t m 4952) (meaning t m 4953) (meaning t m 4954)

theorem rule12726 (p2982 p4449 p4952 p4953 p4954 : Prop) : (p4449) ∨ (((¬ p4952) ∨ (¬ p4449) ∨ (¬ p2982) ∨ (¬ p4953) ∨ (¬ p4954))) := by
  classical
  tauto

theorem initial12726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4449) ∨ (meaning t m 5957) := by
  exact rule12726 (meaning t m 2982) (meaning t m 4449) (meaning t m 4952) (meaning t m 4953) (meaning t m 4954)

theorem rule12727 (p2982 p4449 p4952 p4953 p4954 : Prop) : (p2982) ∨ (((¬ p4952) ∨ (¬ p4449) ∨ (¬ p2982) ∨ (¬ p4953) ∨ (¬ p4954))) := by
  classical
  tauto

theorem initial12727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2982) ∨ (meaning t m 5957) := by
  exact rule12727 (meaning t m 2982) (meaning t m 4449) (meaning t m 4952) (meaning t m 4953) (meaning t m 4954)

theorem rule12728 (p2982 p4449 p4952 p4953 p4954 : Prop) : (p4953) ∨ (((¬ p4952) ∨ (¬ p4449) ∨ (¬ p2982) ∨ (¬ p4953) ∨ (¬ p4954))) := by
  classical
  tauto

theorem initial12728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4953) ∨ (meaning t m 5957) := by
  exact rule12728 (meaning t m 2982) (meaning t m 4449) (meaning t m 4952) (meaning t m 4953) (meaning t m 4954)

theorem rule12733 (p5956 p5957 : Prop) : (¬ ((¬ p5956) ∨ (¬ p5957))) ∨ (¬ p5956) ∨ (¬ p5957) := by
  classical
  tauto

theorem initial12733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5955)) ∨ (¬ (meaning t m 5956)) ∨ (¬ (meaning t m 5957)) := by
  exact rule12733 (meaning t m 5956) (meaning t m 5957)

theorem rule12734 (p4945 p5955 : Prop) (h : (p4945 ↔ p5955)) : (¬ p4945) ∨ (p5955) := by
  classical
  tauto

theorem initial12734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4945)) ∨ (meaning t m 5955) := by
  have source := ElevenTheory.theory3303 t (m.theta 4 5) (m.theta 4 9) (m.theta 5 9)
  exact rule12734 (meaning t m 4945) (meaning t m 5955) source

theorem rule12736 (p1977 p2027 p2651 p2765 p2952 p3952 p4111 : Prop) (h : (¬ p1977) ∨ (¬ p4111) ∨ p2027 ∨ p2765 ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3952)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2651) ∨ (p2765) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial12736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory3304 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule12736 (meaning t m 1977) (meaning t m 2027) (meaning t m 2651) (meaning t m 2765) (meaning t m 2952) (meaning t m 3952) (meaning t m 4111) source

theorem rule12737 (p3368 p3412 p3662 p4448 p4957 : Prop) : (p3368) ∨ (((¬ p3368) ∨ (¬ p4448) ∨ (¬ p3412) ∨ (¬ p3662) ∨ (¬ p4957))) := by
  classical
  tauto

theorem initial12737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3368) ∨ (meaning t m 5959) := by
  exact rule12737 (meaning t m 3368) (meaning t m 3412) (meaning t m 3662) (meaning t m 4448) (meaning t m 4957)

theorem rule12738 (p3368 p3412 p3662 p4448 p4957 : Prop) : (p4448) ∨ (((¬ p3368) ∨ (¬ p4448) ∨ (¬ p3412) ∨ (¬ p3662) ∨ (¬ p4957))) := by
  classical
  tauto

theorem initial12738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4448) ∨ (meaning t m 5959) := by
  exact rule12738 (meaning t m 3368) (meaning t m 3412) (meaning t m 3662) (meaning t m 4448) (meaning t m 4957)

theorem rule12739 (p3368 p3412 p3662 p4448 p4957 : Prop) : (p3412) ∨ (((¬ p3368) ∨ (¬ p4448) ∨ (¬ p3412) ∨ (¬ p3662) ∨ (¬ p4957))) := by
  classical
  tauto

theorem initial12739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3412) ∨ (meaning t m 5959) := by
  exact rule12739 (meaning t m 3368) (meaning t m 3412) (meaning t m 3662) (meaning t m 4448) (meaning t m 4957)

theorem rule12740 (p3368 p3412 p3662 p4448 p4957 : Prop) : (p3662) ∨ (((¬ p3368) ∨ (¬ p4448) ∨ (¬ p3412) ∨ (¬ p3662) ∨ (¬ p4957))) := by
  classical
  tauto

theorem initial12740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3662) ∨ (meaning t m 5959) := by
  exact rule12740 (meaning t m 3368) (meaning t m 3412) (meaning t m 3662) (meaning t m 4448) (meaning t m 4957)

theorem rule12741 (p3368 p3412 p3662 p4448 p4957 : Prop) : (p4957) ∨ (((¬ p3368) ∨ (¬ p4448) ∨ (¬ p3412) ∨ (¬ p3662) ∨ (¬ p4957))) := by
  classical
  tauto

theorem initial12741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4957) ∨ (meaning t m 5959) := by
  exact rule12741 (meaning t m 3368) (meaning t m 3412) (meaning t m 3662) (meaning t m 4448) (meaning t m 4957)

theorem rule12743 (p2992 p4282 p4365 p4959 p4960 : Prop) : (p2992) ∨ (((¬ p2992) ∨ (¬ p4959) ∨ (¬ p4282) ∨ (¬ p4365) ∨ (¬ p4960))) := by
  classical
  tauto

theorem initial12743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2992) ∨ (meaning t m 5960) := by
  exact rule12743 (meaning t m 2992) (meaning t m 4282) (meaning t m 4365) (meaning t m 4959) (meaning t m 4960)

theorem rule12744 (p2992 p4282 p4365 p4959 p4960 : Prop) : (p4959) ∨ (((¬ p2992) ∨ (¬ p4959) ∨ (¬ p4282) ∨ (¬ p4365) ∨ (¬ p4960))) := by
  classical
  tauto

theorem initial12744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4959) ∨ (meaning t m 5960) := by
  exact rule12744 (meaning t m 2992) (meaning t m 4282) (meaning t m 4365) (meaning t m 4959) (meaning t m 4960)

theorem rule12745 (p2992 p4282 p4365 p4959 p4960 : Prop) : (p4282) ∨ (((¬ p2992) ∨ (¬ p4959) ∨ (¬ p4282) ∨ (¬ p4365) ∨ (¬ p4960))) := by
  classical
  tauto

theorem initial12745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4282) ∨ (meaning t m 5960) := by
  exact rule12745 (meaning t m 2992) (meaning t m 4282) (meaning t m 4365) (meaning t m 4959) (meaning t m 4960)

theorem rule12746 (p2992 p4282 p4365 p4959 p4960 : Prop) : (p4365) ∨ (((¬ p2992) ∨ (¬ p4959) ∨ (¬ p4282) ∨ (¬ p4365) ∨ (¬ p4960))) := by
  classical
  tauto

theorem initial12746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4365) ∨ (meaning t m 5960) := by
  exact rule12746 (meaning t m 2992) (meaning t m 4282) (meaning t m 4365) (meaning t m 4959) (meaning t m 4960)

theorem rule12751 (p5959 p5960 : Prop) : (¬ ((¬ p5959) ∨ (¬ p5960))) ∨ (¬ p5959) ∨ (¬ p5960) := by
  classical
  tauto

theorem initial12751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5958)) ∨ (¬ (meaning t m 5959)) ∨ (¬ (meaning t m 5960)) := by
  exact rule12751 (meaning t m 5959) (meaning t m 5960)

theorem rule12752 (p4955 p5958 : Prop) (h : (p4955 ↔ p5958)) : (¬ p4955) ∨ (p5958) := by
  classical
  tauto

theorem initial12752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4955)) ∨ (meaning t m 5958) := by
  have source := ElevenTheory.theory3305 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 5)
  exact rule12752 (meaning t m 4955) (meaning t m 5958) source

theorem rule12754 (p1985 p2997 p3097 p4558 : Prop) (h : p2997 ∨ p4558 ∨ (¬ p3097) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2997) ∨ (¬ p3097) ∨ (p4558) := by
  classical
  tauto

theorem initial12754 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (meaning t m 4558) := by
  have source := ElevenTheory.theory3306 t (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule12754 (meaning t m 1985) (meaning t m 2997) (meaning t m 3097) (meaning t m 4558) source

theorem rule12756 (p1977 p2027 p2427 p2765 p4110 p4111 p4320 p4700 : Prop) (h : (¬ p4110) ∨ (¬ p4111) ∨ p2765 ∨ p2027 ∨ (¬ p1977) ∨ (¬ p2427) ∨ (¬ p4700) ∨ (¬ p4320)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2427) ∨ (p2765) ∨ (¬ p4110) ∨ (¬ p4111) ∨ (¬ p4320) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial12756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory3308 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule12756 (meaning t m 1977) (meaning t m 2027) (meaning t m 2427) (meaning t m 2765) (meaning t m 4110) (meaning t m 4111) (meaning t m 4320) (meaning t m 4700) source

theorem rule12757 (p1977 p2027 p2589 p2633 p2662 p3570 p4111 p4235 : Prop) (h : (¬ p1977) ∨ p2633 ∨ (¬ p4235) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p2662) ∨ (¬ p2589) ∨ (¬ p3570)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2589) ∨ (p2633) ∨ (¬ p2662) ∨ (¬ p3570) ∨ (¬ p4111) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial12757 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory3309 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule12757 (meaning t m 1977) (meaning t m 2027) (meaning t m 2589) (meaning t m 2633) (meaning t m 2662) (meaning t m 3570) (meaning t m 4111) (meaning t m 4235) source

theorem rule12758 (p1982 p2027 p2210 p2459 p2699 p2881 p2891 : Prop) (h : p2027 ∨ (¬ p2459) ∨ p2699 ∨ (¬ p2210) ∨ (¬ p1982) ∨ (¬ p2881) ∨ (¬ p2891)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2459) ∨ (p2699) ∨ (¬ p2881) ∨ (¬ p2891) := by
  classical
  tauto

theorem initial12758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) := by
  have source := ElevenTheory.theory3310 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule12758 (meaning t m 1982) (meaning t m 2027) (meaning t m 2210) (meaning t m 2459) (meaning t m 2699) (meaning t m 2881) (meaning t m 2891) source

theorem rule12759 (p3877 p4364 p4963 p4964 p4965 : Prop) : (p4963) ∨ (((¬ p4963) ∨ (¬ p3877) ∨ (¬ p4364) ∨ (¬ p4964) ∨ (¬ p4965))) := by
  classical
  tauto

theorem initial12759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4963) ∨ (meaning t m 5962) := by
  exact rule12759 (meaning t m 3877) (meaning t m 4364) (meaning t m 4963) (meaning t m 4964) (meaning t m 4965)

theorem rule12760 (p3877 p4364 p4963 p4964 p4965 : Prop) : (p3877) ∨ (((¬ p4963) ∨ (¬ p3877) ∨ (¬ p4364) ∨ (¬ p4964) ∨ (¬ p4965))) := by
  classical
  tauto

theorem initial12760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3877) ∨ (meaning t m 5962) := by
  exact rule12760 (meaning t m 3877) (meaning t m 4364) (meaning t m 4963) (meaning t m 4964) (meaning t m 4965)

theorem rule12761 (p3877 p4364 p4963 p4964 p4965 : Prop) : (p4364) ∨ (((¬ p4963) ∨ (¬ p3877) ∨ (¬ p4364) ∨ (¬ p4964) ∨ (¬ p4965))) := by
  classical
  tauto

theorem initial12761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4364) ∨ (meaning t m 5962) := by
  exact rule12761 (meaning t m 3877) (meaning t m 4364) (meaning t m 4963) (meaning t m 4964) (meaning t m 4965)

theorem rule12765 (p3005 p4373 p4967 p4968 p4969 : Prop) : (p4967) ∨ (((¬ p4967) ∨ (¬ p4373) ∨ (¬ p3005) ∨ (¬ p4968) ∨ (¬ p4969))) := by
  classical
  tauto

theorem initial12765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4967) ∨ (meaning t m 5963) := by
  exact rule12765 (meaning t m 3005) (meaning t m 4373) (meaning t m 4967) (meaning t m 4968) (meaning t m 4969)

theorem rule12766 (p3005 p4373 p4967 p4968 p4969 : Prop) : (p4373) ∨ (((¬ p4967) ∨ (¬ p4373) ∨ (¬ p3005) ∨ (¬ p4968) ∨ (¬ p4969))) := by
  classical
  tauto

theorem initial12766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4373) ∨ (meaning t m 5963) := by
  exact rule12766 (meaning t m 3005) (meaning t m 4373) (meaning t m 4967) (meaning t m 4968) (meaning t m 4969)

theorem rule12767 (p3005 p4373 p4967 p4968 p4969 : Prop) : (p3005) ∨ (((¬ p4967) ∨ (¬ p4373) ∨ (¬ p3005) ∨ (¬ p4968) ∨ (¬ p4969))) := by
  classical
  tauto

theorem initial12767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3005) ∨ (meaning t m 5963) := by
  exact rule12767 (meaning t m 3005) (meaning t m 4373) (meaning t m 4967) (meaning t m 4968) (meaning t m 4969)

theorem rule12768 (p3005 p4373 p4967 p4968 p4969 : Prop) : (p4968) ∨ (((¬ p4967) ∨ (¬ p4373) ∨ (¬ p3005) ∨ (¬ p4968) ∨ (¬ p4969))) := by
  classical
  tauto

theorem initial12768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4968) ∨ (meaning t m 5963) := by
  exact rule12768 (meaning t m 3005) (meaning t m 4373) (meaning t m 4967) (meaning t m 4968) (meaning t m 4969)

theorem rule12769 (p3005 p4373 p4967 p4968 p4969 : Prop) : (p4969) ∨ (((¬ p4967) ∨ (¬ p4373) ∨ (¬ p3005) ∨ (¬ p4968) ∨ (¬ p4969))) := by
  classical
  tauto

theorem initial12769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4969) ∨ (meaning t m 5963) := by
  exact rule12769 (meaning t m 3005) (meaning t m 4373) (meaning t m 4967) (meaning t m 4968) (meaning t m 4969)

theorem rule12773 (p5962 p5963 : Prop) : (¬ ((¬ p5962) ∨ (¬ p5963))) ∨ (¬ p5962) ∨ (¬ p5963) := by
  classical
  tauto

theorem initial12773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5961)) ∨ (¬ (meaning t m 5962)) ∨ (¬ (meaning t m 5963)) := by
  exact rule12773 (meaning t m 5962) (meaning t m 5963)

theorem rule12774 (p4961 p5961 : Prop) (h : (p4961 ↔ p5961)) : (¬ p4961) ∨ (p5961) := by
  classical
  tauto

theorem initial12774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4961)) ∨ (meaning t m 5961) := by
  have source := ElevenTheory.theory3311 t (m.theta 2 3) (m.theta 2 8) (m.theta 3 8)
  exact rule12774 (meaning t m 4961) (meaning t m 5961) source

theorem rule12776 (p1982 p2027 p2611 p2651 p2810 p3005 p3256 p4117 : Prop) (h : (¬ p3005) ∨ (¬ p1982) ∨ p2611 ∨ p2027 ∨ (¬ p3256) ∨ (¬ p4117) ∨ (¬ p2810) ∨ (¬ p2651)) : (¬ p1982) ∨ (p2027) ∨ (p2611) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial12776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory3312 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule12776 (meaning t m 1982) (meaning t m 2027) (meaning t m 2611) (meaning t m 2651) (meaning t m 2810) (meaning t m 3005) (meaning t m 3256) (meaning t m 4117) source

theorem rule12777 (p2246 p2957 p2958 p3662 : Prop) (h : (¬ p3662) ∨ (¬ p2957) ∨ (¬ p2958) ∨ (¬ p2246)) : (¬ p2246) ∨ (¬ p2957) ∨ (¬ p2958) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial12777 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory3313 (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 5)
  exact rule12777 (meaning t m 2246) (meaning t m 2957) (meaning t m 2958) (meaning t m 3662) source

theorem rule12778 (p1990 p2563 p3008 p4715 : Prop) (h : (¬ p1990) ∨ p3008 ∨ p4715 ∨ (¬ p2563)) : (¬ p1990) ∨ (¬ p2563) ∨ (p3008) ∨ (p4715) := by
  classical
  tauto

theorem initial12778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 3008) ∨ (meaning t m 4715) := by
  have source := ElevenTheory.theory3314 t (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule12778 (meaning t m 1990) (meaning t m 2563) (meaning t m 3008) (meaning t m 4715) source

theorem rule12779 (p3574 p4194 p4389 p4972 p4973 : Prop) : (p4389) ∨ (((¬ p4389) ∨ (¬ p3574) ∨ (¬ p4194) ∨ (¬ p4972) ∨ (¬ p4973))) := by
  classical
  tauto

theorem initial12779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4389) ∨ (meaning t m 5965) := by
  exact rule12779 (meaning t m 3574) (meaning t m 4194) (meaning t m 4389) (meaning t m 4972) (meaning t m 4973)

theorem rule12780 (p3574 p4194 p4389 p4972 p4973 : Prop) : (p3574) ∨ (((¬ p4389) ∨ (¬ p3574) ∨ (¬ p4194) ∨ (¬ p4972) ∨ (¬ p4973))) := by
  classical
  tauto

theorem initial12780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3574) ∨ (meaning t m 5965) := by
  exact rule12780 (meaning t m 3574) (meaning t m 4194) (meaning t m 4389) (meaning t m 4972) (meaning t m 4973)

theorem rule12781 (p3574 p4194 p4389 p4972 p4973 : Prop) : (p4194) ∨ (((¬ p4389) ∨ (¬ p3574) ∨ (¬ p4194) ∨ (¬ p4972) ∨ (¬ p4973))) := by
  classical
  tauto

theorem initial12781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4194) ∨ (meaning t m 5965) := by
  exact rule12781 (meaning t m 3574) (meaning t m 4194) (meaning t m 4389) (meaning t m 4972) (meaning t m 4973)

theorem rule12782 (p3574 p4194 p4389 p4972 p4973 : Prop) : (p4972) ∨ (((¬ p4389) ∨ (¬ p3574) ∨ (¬ p4194) ∨ (¬ p4972) ∨ (¬ p4973))) := by
  classical
  tauto

theorem initial12782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4972) ∨ (meaning t m 5965) := by
  exact rule12782 (meaning t m 3574) (meaning t m 4194) (meaning t m 4389) (meaning t m 4972) (meaning t m 4973)

theorem rule12785 (p3016 p3019 p3984 p4975 p4976 : Prop) : (p3984) ∨ (((¬ p3984) ∨ (¬ p3019) ∨ (¬ p3016) ∨ (¬ p4975) ∨ (¬ p4976))) := by
  classical
  tauto

theorem initial12785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3984) ∨ (meaning t m 5966) := by
  exact rule12785 (meaning t m 3016) (meaning t m 3019) (meaning t m 3984) (meaning t m 4975) (meaning t m 4976)

theorem rule12786 (p3016 p3019 p3984 p4975 p4976 : Prop) : (p3019) ∨ (((¬ p3984) ∨ (¬ p3019) ∨ (¬ p3016) ∨ (¬ p4975) ∨ (¬ p4976))) := by
  classical
  tauto

theorem initial12786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3019) ∨ (meaning t m 5966) := by
  exact rule12786 (meaning t m 3016) (meaning t m 3019) (meaning t m 3984) (meaning t m 4975) (meaning t m 4976)

theorem rule12787 (p3016 p3019 p3984 p4975 p4976 : Prop) : (p3016) ∨ (((¬ p3984) ∨ (¬ p3019) ∨ (¬ p3016) ∨ (¬ p4975) ∨ (¬ p4976))) := by
  classical
  tauto

theorem initial12787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3016) ∨ (meaning t m 5966) := by
  exact rule12787 (meaning t m 3016) (meaning t m 3019) (meaning t m 3984) (meaning t m 4975) (meaning t m 4976)

theorem rule12793 (p5965 p5966 : Prop) : (¬ ((¬ p5965) ∨ (¬ p5966))) ∨ (¬ p5965) ∨ (¬ p5966) := by
  classical
  tauto

theorem initial12793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5964)) ∨ (¬ (meaning t m 5965)) ∨ (¬ (meaning t m 5966)) := by
  exact rule12793 (meaning t m 5965) (meaning t m 5966)

theorem rule12794 (p4970 p5964 : Prop) (h : (p4970 ↔ p5964)) : (¬ p4970) ∨ (p5964) := by
  classical
  tauto

theorem initial12794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4970)) ∨ (meaning t m 5964) := by
  have source := ElevenTheory.theory3315 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule12794 (meaning t m 4970) (meaning t m 5964) source

theorem rule12797 (p1977 p2027 p2622 p2651 p3005 p3172 p4111 : Prop) (h : p2622 ∨ (¬ p4111) ∨ (¬ p2651) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p3005) ∨ (¬ p3172)) : (¬ p1977) ∨ (p2027) ∨ (p2622) ∨ (¬ p2651) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial12797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory3317 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8)
  exact rule12797 (meaning t m 1977) (meaning t m 2027) (meaning t m 2622) (meaning t m 2651) (meaning t m 3005) (meaning t m 3172) (meaning t m 4111) source

theorem rule12798 (p1976 p2027 p2633 p3055 p3570 p3684 p4235 : Prop) (h : (¬ p1976) ∨ (¬ p4235) ∨ p2633 ∨ (¬ p3570) ∨ (¬ p3684) ∨ p2027 ∨ (¬ p3055)) : (¬ p1976) ∨ (p2027) ∨ (p2633) ∨ (¬ p3055) ∨ (¬ p3570) ∨ (¬ p3684) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial12798 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory3318 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule12798 (meaning t m 1976) (meaning t m 2027) (meaning t m 2633) (meaning t m 3055) (meaning t m 3570) (meaning t m 3684) (meaning t m 4235) source

theorem rule12799 (p1976 p2027 p2138 p2427 p3043 p4244 p4948 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p4948) ∨ p3043 ∨ (¬ p4244) ∨ (¬ p2138) ∨ (¬ p2427)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2427) ∨ (p3043) ∨ (¬ p4244) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial12799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory3319 t (m.theta 0 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9)
  exact rule12799 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2427) (meaning t m 3043) (meaning t m 4244) (meaning t m 4948) source

theorem rule12800 (p3556 p3691 p4984 p4985 p4986 : Prop) : (p4985) ∨ (((¬ p4985) ∨ (¬ p4984) ∨ (¬ p4986) ∨ (¬ p3556) ∨ (¬ p3691))) := by
  classical
  tauto

theorem initial12800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4985) ∨ (meaning t m 5968) := by
  exact rule12800 (meaning t m 3556) (meaning t m 3691) (meaning t m 4984) (meaning t m 4985) (meaning t m 4986)

theorem rule12801 (p3556 p3691 p4984 p4985 p4986 : Prop) : (p4984) ∨ (((¬ p4985) ∨ (¬ p4984) ∨ (¬ p4986) ∨ (¬ p3556) ∨ (¬ p3691))) := by
  classical
  tauto

theorem initial12801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4984) ∨ (meaning t m 5968) := by
  exact rule12801 (meaning t m 3556) (meaning t m 3691) (meaning t m 4984) (meaning t m 4985) (meaning t m 4986)

theorem rule12802 (p3556 p3691 p4984 p4985 p4986 : Prop) : (p4986) ∨ (((¬ p4985) ∨ (¬ p4984) ∨ (¬ p4986) ∨ (¬ p3556) ∨ (¬ p3691))) := by
  classical
  tauto

theorem initial12802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4986) ∨ (meaning t m 5968) := by
  exact rule12802 (meaning t m 3556) (meaning t m 3691) (meaning t m 4984) (meaning t m 4985) (meaning t m 4986)

theorem rule12803 (p3556 p3691 p4984 p4985 p4986 : Prop) : (p3556) ∨ (((¬ p4985) ∨ (¬ p4984) ∨ (¬ p4986) ∨ (¬ p3556) ∨ (¬ p3691))) := by
  classical
  tauto

theorem initial12803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3556) ∨ (meaning t m 5968) := by
  exact rule12803 (meaning t m 3556) (meaning t m 3691) (meaning t m 4984) (meaning t m 4985) (meaning t m 4986)

theorem rule12804 (p3556 p3691 p4984 p4985 p4986 : Prop) : (p3691) ∨ (((¬ p4985) ∨ (¬ p4984) ∨ (¬ p4986) ∨ (¬ p3556) ∨ (¬ p3691))) := by
  classical
  tauto

theorem initial12804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3691) ∨ (meaning t m 5968) := by
  exact rule12804 (meaning t m 3556) (meaning t m 3691) (meaning t m 4984) (meaning t m 4985) (meaning t m 4986)

theorem rule12807 (p3051 p4283 p4988 p4989 p4990 : Prop) : (p4990) ∨ (((¬ p4989) ∨ (¬ p4990) ∨ (¬ p4988) ∨ (¬ p3051) ∨ (¬ p4283))) := by
  classical
  tauto

theorem initial12807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4990) ∨ (meaning t m 5969) := by
  exact rule12807 (meaning t m 3051) (meaning t m 4283) (meaning t m 4988) (meaning t m 4989) (meaning t m 4990)

theorem rule12808 (p3051 p4283 p4988 p4989 p4990 : Prop) : (p4988) ∨ (((¬ p4989) ∨ (¬ p4990) ∨ (¬ p4988) ∨ (¬ p3051) ∨ (¬ p4283))) := by
  classical
  tauto

theorem initial12808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4988) ∨ (meaning t m 5969) := by
  exact rule12808 (meaning t m 3051) (meaning t m 4283) (meaning t m 4988) (meaning t m 4989) (meaning t m 4990)

theorem rule12809 (p3051 p4283 p4988 p4989 p4990 : Prop) : (p3051) ∨ (((¬ p4989) ∨ (¬ p4990) ∨ (¬ p4988) ∨ (¬ p3051) ∨ (¬ p4283))) := by
  classical
  tauto

theorem initial12809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3051) ∨ (meaning t m 5969) := by
  exact rule12809 (meaning t m 3051) (meaning t m 4283) (meaning t m 4988) (meaning t m 4989) (meaning t m 4990)

theorem rule12810 (p3051 p4283 p4988 p4989 p4990 : Prop) : (p4283) ∨ (((¬ p4989) ∨ (¬ p4990) ∨ (¬ p4988) ∨ (¬ p3051) ∨ (¬ p4283))) := by
  classical
  tauto

theorem initial12810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4283) ∨ (meaning t m 5969) := by
  exact rule12810 (meaning t m 3051) (meaning t m 4283) (meaning t m 4988) (meaning t m 4989) (meaning t m 4990)

theorem rule12814 (p5968 p5969 : Prop) : (¬ ((¬ p5968) ∨ (¬ p5969))) ∨ (¬ p5968) ∨ (¬ p5969) := by
  classical
  tauto

theorem initial12814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5967)) ∨ (¬ (meaning t m 5968)) ∨ (¬ (meaning t m 5969)) := by
  exact rule12814 (meaning t m 5968) (meaning t m 5969)

theorem rule12815 (p4982 p5967 : Prop) (h : (p4982 ↔ p5967)) : (¬ p4982) ∨ (p5967) := by
  classical
  tauto

theorem initial12815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4982)) ∨ (meaning t m 5967) := by
  have source := ElevenTheory.theory3320 t (m.theta 0 5) (m.theta 0 7) (m.theta 5 7)
  exact rule12815 (meaning t m 4982) (meaning t m 5967) source

theorem rule12818 (p3923 p4371 p4993 p4994 p4995 : Prop) : (p3923) ∨ (((¬ p4993) ∨ (¬ p3923) ∨ (¬ p4371) ∨ (¬ p4994) ∨ (¬ p4995))) := by
  classical
  tauto

theorem initial12818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3923) ∨ (meaning t m 5971) := by
  exact rule12818 (meaning t m 3923) (meaning t m 4371) (meaning t m 4993) (meaning t m 4994) (meaning t m 4995)

theorem rule12819 (p3923 p4371 p4993 p4994 p4995 : Prop) : (p4371) ∨ (((¬ p4993) ∨ (¬ p3923) ∨ (¬ p4371) ∨ (¬ p4994) ∨ (¬ p4995))) := by
  classical
  tauto

theorem initial12819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4371) ∨ (meaning t m 5971) := by
  exact rule12819 (meaning t m 3923) (meaning t m 4371) (meaning t m 4993) (meaning t m 4994) (meaning t m 4995)

theorem rule12823 (p3063 p4317 p4318 p4997 p4998 : Prop) : (p4318) ∨ (((¬ p4318) ∨ (¬ p4317) ∨ (¬ p3063) ∨ (¬ p4997) ∨ (¬ p4998))) := by
  classical
  tauto

theorem initial12823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4318) ∨ (meaning t m 5972) := by
  exact rule12823 (meaning t m 3063) (meaning t m 4317) (meaning t m 4318) (meaning t m 4997) (meaning t m 4998)

theorem rule12824 (p3063 p4317 p4318 p4997 p4998 : Prop) : (p4317) ∨ (((¬ p4318) ∨ (¬ p4317) ∨ (¬ p3063) ∨ (¬ p4997) ∨ (¬ p4998))) := by
  classical
  tauto

theorem initial12824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4317) ∨ (meaning t m 5972) := by
  exact rule12824 (meaning t m 3063) (meaning t m 4317) (meaning t m 4318) (meaning t m 4997) (meaning t m 4998)

theorem rule12825 (p3063 p4317 p4318 p4997 p4998 : Prop) : (p3063) ∨ (((¬ p4318) ∨ (¬ p4317) ∨ (¬ p3063) ∨ (¬ p4997) ∨ (¬ p4998))) := by
  classical
  tauto

theorem initial12825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3063) ∨ (meaning t m 5972) := by
  exact rule12825 (meaning t m 3063) (meaning t m 4317) (meaning t m 4318) (meaning t m 4997) (meaning t m 4998)

theorem rule12831 (p5971 p5972 : Prop) : (¬ ((¬ p5971) ∨ (¬ p5972))) ∨ (¬ p5971) ∨ (¬ p5972) := by
  classical
  tauto

theorem initial12831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5970)) ∨ (¬ (meaning t m 5971)) ∨ (¬ (meaning t m 5972)) := by
  exact rule12831 (meaning t m 5971) (meaning t m 5972)

theorem rule12832 (p4991 p5970 : Prop) (h : (p4991 ↔ p5970)) : (¬ p4991) ∨ (p5970) := by
  classical
  tauto

theorem initial12832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4991)) ∨ (meaning t m 5970) := by
  have source := ElevenTheory.theory3321 t (m.theta 1 6) (m.theta 1 8) (m.theta 6 8)
  exact rule12832 (meaning t m 4991) (meaning t m 5970) source

theorem rule12834 (p3438 p3440 p4261 p5001 p5002 : Prop) : (p3438) ∨ (((¬ p3438) ∨ (¬ p4261) ∨ (¬ p3440) ∨ (¬ p5001) ∨ (¬ p5002))) := by
  classical
  tauto

theorem initial12834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3438) ∨ (meaning t m 5974) := by
  exact rule12834 (meaning t m 3438) (meaning t m 3440) (meaning t m 4261) (meaning t m 5001) (meaning t m 5002)

theorem rule12835 (p3438 p3440 p4261 p5001 p5002 : Prop) : (p4261) ∨ (((¬ p3438) ∨ (¬ p4261) ∨ (¬ p3440) ∨ (¬ p5001) ∨ (¬ p5002))) := by
  classical
  tauto

theorem initial12835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4261) ∨ (meaning t m 5974) := by
  exact rule12835 (meaning t m 3438) (meaning t m 3440) (meaning t m 4261) (meaning t m 5001) (meaning t m 5002)

theorem rule12836 (p3438 p3440 p4261 p5001 p5002 : Prop) : (p3440) ∨ (((¬ p3438) ∨ (¬ p4261) ∨ (¬ p3440) ∨ (¬ p5001) ∨ (¬ p5002))) := by
  classical
  tauto

theorem initial12836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3440) ∨ (meaning t m 5974) := by
  exact rule12836 (meaning t m 3438) (meaning t m 3440) (meaning t m 4261) (meaning t m 5001) (meaning t m 5002)

theorem rule12840 (p3073 p4351 p4352 p5004 p5005 : Prop) : (p4352) ∨ (((¬ p4352) ∨ (¬ p4351) ∨ (¬ p3073) ∨ (¬ p5004) ∨ (¬ p5005))) := by
  classical
  tauto

theorem initial12840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4352) ∨ (meaning t m 5975) := by
  exact rule12840 (meaning t m 3073) (meaning t m 4351) (meaning t m 4352) (meaning t m 5004) (meaning t m 5005)

theorem rule12841 (p3073 p4351 p4352 p5004 p5005 : Prop) : (p4351) ∨ (((¬ p4352) ∨ (¬ p4351) ∨ (¬ p3073) ∨ (¬ p5004) ∨ (¬ p5005))) := by
  classical
  tauto

theorem initial12841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4351) ∨ (meaning t m 5975) := by
  exact rule12841 (meaning t m 3073) (meaning t m 4351) (meaning t m 4352) (meaning t m 5004) (meaning t m 5005)

theorem rule12842 (p3073 p4351 p4352 p5004 p5005 : Prop) : (p3073) ∨ (((¬ p4352) ∨ (¬ p4351) ∨ (¬ p3073) ∨ (¬ p5004) ∨ (¬ p5005))) := by
  classical
  tauto

theorem initial12842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3073) ∨ (meaning t m 5975) := by
  exact rule12842 (meaning t m 3073) (meaning t m 4351) (meaning t m 4352) (meaning t m 5004) (meaning t m 5005)

theorem rule12848 (p5974 p5975 : Prop) : (¬ ((¬ p5974) ∨ (¬ p5975))) ∨ (¬ p5974) ∨ (¬ p5975) := by
  classical
  tauto

theorem initial12848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5973)) ∨ (¬ (meaning t m 5974)) ∨ (¬ (meaning t m 5975)) := by
  exact rule12848 (meaning t m 5974) (meaning t m 5975)

theorem rule12849 (p4999 p5973 : Prop) (h : (p4999 ↔ p5973)) : (¬ p4999) ∨ (p5973) := by
  classical
  tauto

theorem initial12849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4999)) ∨ (meaning t m 5973) := by
  have source := ElevenTheory.theory3322 t (m.theta 1 8) (m.theta 1 9) (m.theta 8 9)
  exact rule12849 (meaning t m 4999) (meaning t m 5973) source

theorem rule12852 (p3878 p4256 p4437 p5008 p5009 : Prop) : (p4437) ∨ (((¬ p4437) ∨ (¬ p4256) ∨ (¬ p3878) ∨ (¬ p5008) ∨ (¬ p5009))) := by
  classical
  tauto

theorem initial12852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4437) ∨ (meaning t m 5977) := by
  exact rule12852 (meaning t m 3878) (meaning t m 4256) (meaning t m 4437) (meaning t m 5008) (meaning t m 5009)

theorem rule12853 (p3878 p4256 p4437 p5008 p5009 : Prop) : (p4256) ∨ (((¬ p4437) ∨ (¬ p4256) ∨ (¬ p3878) ∨ (¬ p5008) ∨ (¬ p5009))) := by
  classical
  tauto

theorem initial12853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4256) ∨ (meaning t m 5977) := by
  exact rule12853 (meaning t m 3878) (meaning t m 4256) (meaning t m 4437) (meaning t m 5008) (meaning t m 5009)

theorem rule12854 (p3878 p4256 p4437 p5008 p5009 : Prop) : (p3878) ∨ (((¬ p4437) ∨ (¬ p4256) ∨ (¬ p3878) ∨ (¬ p5008) ∨ (¬ p5009))) := by
  classical
  tauto

theorem initial12854 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3878) ∨ (meaning t m 5977) := by
  exact rule12854 (meaning t m 3878) (meaning t m 4256) (meaning t m 4437) (meaning t m 5008) (meaning t m 5009)

theorem rule12856 (p3878 p4256 p4437 p5008 p5009 : Prop) : (p5009) ∨ (((¬ p4437) ∨ (¬ p4256) ∨ (¬ p3878) ∨ (¬ p5008) ∨ (¬ p5009))) := by
  classical
  tauto

theorem initial12856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5009) ∨ (meaning t m 5977) := by
  exact rule12856 (meaning t m 3878) (meaning t m 4256) (meaning t m 4437) (meaning t m 5008) (meaning t m 5009)

theorem rule12858 (p3083 p4121 p4346 p5011 p5012 : Prop) : (p4346) ∨ (((¬ p4346) ∨ (¬ p4121) ∨ (¬ p3083) ∨ (¬ p5011) ∨ (¬ p5012))) := by
  classical
  tauto

theorem initial12858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4346) ∨ (meaning t m 5978) := by
  exact rule12858 (meaning t m 3083) (meaning t m 4121) (meaning t m 4346) (meaning t m 5011) (meaning t m 5012)

theorem rule12859 (p3083 p4121 p4346 p5011 p5012 : Prop) : (p4121) ∨ (((¬ p4346) ∨ (¬ p4121) ∨ (¬ p3083) ∨ (¬ p5011) ∨ (¬ p5012))) := by
  classical
  tauto

theorem initial12859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4121) ∨ (meaning t m 5978) := by
  exact rule12859 (meaning t m 3083) (meaning t m 4121) (meaning t m 4346) (meaning t m 5011) (meaning t m 5012)

theorem rule12860 (p3083 p4121 p4346 p5011 p5012 : Prop) : (p3083) ∨ (((¬ p4346) ∨ (¬ p4121) ∨ (¬ p3083) ∨ (¬ p5011) ∨ (¬ p5012))) := by
  classical
  tauto

theorem initial12860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3083) ∨ (meaning t m 5978) := by
  exact rule12860 (meaning t m 3083) (meaning t m 4121) (meaning t m 4346) (meaning t m 5011) (meaning t m 5012)

theorem rule12861 (p3083 p4121 p4346 p5011 p5012 : Prop) : (p5011) ∨ (((¬ p4346) ∨ (¬ p4121) ∨ (¬ p3083) ∨ (¬ p5011) ∨ (¬ p5012))) := by
  classical
  tauto

theorem initial12861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5011) ∨ (meaning t m 5978) := by
  exact rule12861 (meaning t m 3083) (meaning t m 4121) (meaning t m 4346) (meaning t m 5011) (meaning t m 5012)

theorem rule12862 (p3083 p4121 p4346 p5011 p5012 : Prop) : (p5012) ∨ (((¬ p4346) ∨ (¬ p4121) ∨ (¬ p3083) ∨ (¬ p5011) ∨ (¬ p5012))) := by
  classical
  tauto

theorem initial12862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5012) ∨ (meaning t m 5978) := by
  exact rule12862 (meaning t m 3083) (meaning t m 4121) (meaning t m 4346) (meaning t m 5011) (meaning t m 5012)

theorem rule12866 (p5977 p5978 : Prop) : (¬ ((¬ p5977) ∨ (¬ p5978))) ∨ (¬ p5977) ∨ (¬ p5978) := by
  classical
  tauto

theorem initial12866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5976)) ∨ (¬ (meaning t m 5977)) ∨ (¬ (meaning t m 5978)) := by
  exact rule12866 (meaning t m 5977) (meaning t m 5978)

theorem rule12867 (p5006 p5976 : Prop) (h : (p5006 ↔ p5976)) : (¬ p5006) ∨ (p5976) := by
  classical
  tauto

theorem initial12867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5006)) ∨ (meaning t m 5976) := by
  have source := ElevenTheory.theory3324 t (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule12867 (meaning t m 5006) (meaning t m 5976) source

theorem rule12869 (p3591 p5015 p5016 p5017 p5018 : Prop) : (p5018) ∨ (((¬ p5018) ∨ (¬ p3591) ∨ (¬ p5016) ∨ (¬ p5017) ∨ (¬ p5015))) := by
  classical
  tauto

theorem initial12869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5018) ∨ (meaning t m 5980) := by
  exact rule12869 (meaning t m 3591) (meaning t m 5015) (meaning t m 5016) (meaning t m 5017) (meaning t m 5018)

theorem rule12870 (p3591 p5015 p5016 p5017 p5018 : Prop) : (p3591) ∨ (((¬ p5018) ∨ (¬ p3591) ∨ (¬ p5016) ∨ (¬ p5017) ∨ (¬ p5015))) := by
  classical
  tauto

theorem initial12870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3591) ∨ (meaning t m 5980) := by
  exact rule12870 (meaning t m 3591) (meaning t m 5015) (meaning t m 5016) (meaning t m 5017) (meaning t m 5018)

theorem rule12871 (p3591 p5015 p5016 p5017 p5018 : Prop) : (p5016) ∨ (((¬ p5018) ∨ (¬ p3591) ∨ (¬ p5016) ∨ (¬ p5017) ∨ (¬ p5015))) := by
  classical
  tauto

theorem initial12871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5016) ∨ (meaning t m 5980) := by
  exact rule12871 (meaning t m 3591) (meaning t m 5015) (meaning t m 5016) (meaning t m 5017) (meaning t m 5018)

theorem rule12872 (p3591 p5015 p5016 p5017 p5018 : Prop) : (p5017) ∨ (((¬ p5018) ∨ (¬ p3591) ∨ (¬ p5016) ∨ (¬ p5017) ∨ (¬ p5015))) := by
  classical
  tauto

theorem initial12872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5017) ∨ (meaning t m 5980) := by
  exact rule12872 (meaning t m 3591) (meaning t m 5015) (meaning t m 5016) (meaning t m 5017) (meaning t m 5018)

theorem rule12873 (p3591 p5015 p5016 p5017 p5018 : Prop) : (p5015) ∨ (((¬ p5018) ∨ (¬ p3591) ∨ (¬ p5016) ∨ (¬ p5017) ∨ (¬ p5015))) := by
  classical
  tauto

theorem initial12873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5015) ∨ (meaning t m 5980) := by
  exact rule12873 (meaning t m 3591) (meaning t m 5015) (meaning t m 5016) (meaning t m 5017) (meaning t m 5018)

theorem rule12876 (p3093 p3204 p5020 p5021 p5022 : Prop) : (p3093) ∨ (((¬ p5022) ∨ (¬ p3093) ∨ (¬ p5021) ∨ (¬ p3204) ∨ (¬ p5020))) := by
  classical
  tauto

theorem initial12876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3093) ∨ (meaning t m 5981) := by
  exact rule12876 (meaning t m 3093) (meaning t m 3204) (meaning t m 5020) (meaning t m 5021) (meaning t m 5022)

theorem rule12877 (p3093 p3204 p5020 p5021 p5022 : Prop) : (p5021) ∨ (((¬ p5022) ∨ (¬ p3093) ∨ (¬ p5021) ∨ (¬ p3204) ∨ (¬ p5020))) := by
  classical
  tauto

theorem initial12877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5021) ∨ (meaning t m 5981) := by
  exact rule12877 (meaning t m 3093) (meaning t m 3204) (meaning t m 5020) (meaning t m 5021) (meaning t m 5022)

theorem rule12878 (p3093 p3204 p5020 p5021 p5022 : Prop) : (p3204) ∨ (((¬ p5022) ∨ (¬ p3093) ∨ (¬ p5021) ∨ (¬ p3204) ∨ (¬ p5020))) := by
  classical
  tauto

theorem initial12878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3204) ∨ (meaning t m 5981) := by
  exact rule12878 (meaning t m 3093) (meaning t m 3204) (meaning t m 5020) (meaning t m 5021) (meaning t m 5022)

theorem rule12879 (p3093 p3204 p5020 p5021 p5022 : Prop) : (p5020) ∨ (((¬ p5022) ∨ (¬ p3093) ∨ (¬ p5021) ∨ (¬ p3204) ∨ (¬ p5020))) := by
  classical
  tauto

theorem initial12879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5020) ∨ (meaning t m 5981) := by
  exact rule12879 (meaning t m 3093) (meaning t m 3204) (meaning t m 5020) (meaning t m 5021) (meaning t m 5022)

theorem rule12883 (p5980 p5981 : Prop) : (¬ ((¬ p5980) ∨ (¬ p5981))) ∨ (¬ p5980) ∨ (¬ p5981) := by
  classical
  tauto

theorem initial12883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5979)) ∨ (¬ (meaning t m 5980)) ∨ (¬ (meaning t m 5981)) := by
  exact rule12883 (meaning t m 5980) (meaning t m 5981)

theorem rule12884 (p5013 p5979 : Prop) (h : (p5013 ↔ p5979)) : (¬ p5013) ∨ (p5979) := by
  classical
  tauto

theorem initial12884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5013)) ∨ (meaning t m 5979) := by
  have source := ElevenTheory.theory3325 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 6)
  exact rule12884 (meaning t m 5013) (meaning t m 5979) source

theorem rule12886 (p1992 p2027 p2765 p2982 p3583 p4110 p4385 : Prop) (h : (¬ p1992) ∨ p2765 ∨ p2027 ∨ (¬ p4110) ∨ (¬ p4385) ∨ (¬ p3583) ∨ (¬ p2982)) : (¬ p1992) ∨ (p2027) ∨ (p2765) ∨ (¬ p2982) ∨ (¬ p3583) ∨ (¬ p4110) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial12886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory3326 t (m.theta 1 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule12886 (meaning t m 1992) (meaning t m 2027) (meaning t m 2765) (meaning t m 2982) (meaning t m 3583) (meaning t m 4110) (meaning t m 4385) source

theorem rule12887 (p4385 p5025 p5026 p5027 p5028 : Prop) : (p5026) ∨ (((¬ p5026) ∨ (¬ p4385) ∨ (¬ p5025) ∨ (¬ p5027) ∨ (¬ p5028))) := by
  classical
  tauto

theorem initial12887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5026) ∨ (meaning t m 5983) := by
  exact rule12887 (meaning t m 4385) (meaning t m 5025) (meaning t m 5026) (meaning t m 5027) (meaning t m 5028)

theorem rule12888 (p4385 p5025 p5026 p5027 p5028 : Prop) : (p4385) ∨ (((¬ p5026) ∨ (¬ p4385) ∨ (¬ p5025) ∨ (¬ p5027) ∨ (¬ p5028))) := by
  classical
  tauto

theorem initial12888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4385) ∨ (meaning t m 5983) := by
  exact rule12888 (meaning t m 4385) (meaning t m 5025) (meaning t m 5026) (meaning t m 5027) (meaning t m 5028)

theorem rule12889 (p4385 p5025 p5026 p5027 p5028 : Prop) : (p5025) ∨ (((¬ p5026) ∨ (¬ p4385) ∨ (¬ p5025) ∨ (¬ p5027) ∨ (¬ p5028))) := by
  classical
  tauto

theorem initial12889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5025) ∨ (meaning t m 5983) := by
  exact rule12889 (meaning t m 4385) (meaning t m 5025) (meaning t m 5026) (meaning t m 5027) (meaning t m 5028)

theorem rule12893 (p3105 p5030 p5031 p5032 p5033 : Prop) : (p5030) ∨ (((¬ p5030) ∨ (¬ p5031) ∨ (¬ p3105) ∨ (¬ p5032) ∨ (¬ p5033))) := by
  classical
  tauto

theorem initial12893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5030) ∨ (meaning t m 5984) := by
  exact rule12893 (meaning t m 3105) (meaning t m 5030) (meaning t m 5031) (meaning t m 5032) (meaning t m 5033)

theorem rule12894 (p3105 p5030 p5031 p5032 p5033 : Prop) : (p5031) ∨ (((¬ p5030) ∨ (¬ p5031) ∨ (¬ p3105) ∨ (¬ p5032) ∨ (¬ p5033))) := by
  classical
  tauto

theorem initial12894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5031) ∨ (meaning t m 5984) := by
  exact rule12894 (meaning t m 3105) (meaning t m 5030) (meaning t m 5031) (meaning t m 5032) (meaning t m 5033)

theorem rule12895 (p3105 p5030 p5031 p5032 p5033 : Prop) : (p3105) ∨ (((¬ p5030) ∨ (¬ p5031) ∨ (¬ p3105) ∨ (¬ p5032) ∨ (¬ p5033))) := by
  classical
  tauto

theorem initial12895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3105) ∨ (meaning t m 5984) := by
  exact rule12895 (meaning t m 3105) (meaning t m 5030) (meaning t m 5031) (meaning t m 5032) (meaning t m 5033)

theorem rule12901 (p5983 p5984 : Prop) : (¬ ((¬ p5983) ∨ (¬ p5984))) ∨ (¬ p5983) ∨ (¬ p5984) := by
  classical
  tauto

theorem initial12901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5982)) ∨ (¬ (meaning t m 5983)) ∨ (¬ (meaning t m 5984)) := by
  exact rule12901 (meaning t m 5983) (meaning t m 5984)

theorem rule12902 (p5023 p5982 : Prop) (h : (p5023 ↔ p5982)) : (¬ p5023) ∨ (p5982) := by
  classical
  tauto

theorem initial12902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5023)) ∨ (meaning t m 5982) := by
  have source := ElevenTheory.theory3327 t (m.theta 2 5) (m.theta 2 9) (m.theta 5 9)
  exact rule12902 (meaning t m 5023) (meaning t m 5982) source

theorem rule12905 (p4040 p4208 p4314 p4369 p5036 : Prop) : (p4040) ∨ (((¬ p4040) ∨ (¬ p4208) ∨ (¬ p4314) ∨ (¬ p5036) ∨ (¬ p4369))) := by
  classical
  tauto

theorem initial12905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4040) ∨ (meaning t m 5986) := by
  exact rule12905 (meaning t m 4040) (meaning t m 4208) (meaning t m 4314) (meaning t m 4369) (meaning t m 5036)

theorem rule12906 (p4040 p4208 p4314 p4369 p5036 : Prop) : (p4208) ∨ (((¬ p4040) ∨ (¬ p4208) ∨ (¬ p4314) ∨ (¬ p5036) ∨ (¬ p4369))) := by
  classical
  tauto

theorem initial12906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4208) ∨ (meaning t m 5986) := by
  exact rule12906 (meaning t m 4040) (meaning t m 4208) (meaning t m 4314) (meaning t m 4369) (meaning t m 5036)

theorem rule12907 (p4040 p4208 p4314 p4369 p5036 : Prop) : (p4314) ∨ (((¬ p4040) ∨ (¬ p4208) ∨ (¬ p4314) ∨ (¬ p5036) ∨ (¬ p4369))) := by
  classical
  tauto

theorem initial12907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4314) ∨ (meaning t m 5986) := by
  exact rule12907 (meaning t m 4040) (meaning t m 4208) (meaning t m 4314) (meaning t m 4369) (meaning t m 5036)

theorem rule12911 (p3115 p4039 p5038 p5039 p5040 : Prop) : (p4039) ∨ (((¬ p4039) ∨ (¬ p5038) ∨ (¬ p3115) ∨ (¬ p5039) ∨ (¬ p5040))) := by
  classical
  tauto

theorem initial12911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4039) ∨ (meaning t m 5987) := by
  exact rule12911 (meaning t m 3115) (meaning t m 4039) (meaning t m 5038) (meaning t m 5039) (meaning t m 5040)

theorem rule12912 (p3115 p4039 p5038 p5039 p5040 : Prop) : (p5038) ∨ (((¬ p4039) ∨ (¬ p5038) ∨ (¬ p3115) ∨ (¬ p5039) ∨ (¬ p5040))) := by
  classical
  tauto

theorem initial12912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5038) ∨ (meaning t m 5987) := by
  exact rule12912 (meaning t m 3115) (meaning t m 4039) (meaning t m 5038) (meaning t m 5039) (meaning t m 5040)

theorem rule12913 (p3115 p4039 p5038 p5039 p5040 : Prop) : (p3115) ∨ (((¬ p4039) ∨ (¬ p5038) ∨ (¬ p3115) ∨ (¬ p5039) ∨ (¬ p5040))) := by
  classical
  tauto

theorem initial12913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3115) ∨ (meaning t m 5987) := by
  exact rule12913 (meaning t m 3115) (meaning t m 4039) (meaning t m 5038) (meaning t m 5039) (meaning t m 5040)

theorem rule12914 (p3115 p4039 p5038 p5039 p5040 : Prop) : (p5039) ∨ (((¬ p4039) ∨ (¬ p5038) ∨ (¬ p3115) ∨ (¬ p5039) ∨ (¬ p5040))) := by
  classical
  tauto

theorem initial12914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5039) ∨ (meaning t m 5987) := by
  exact rule12914 (meaning t m 3115) (meaning t m 4039) (meaning t m 5038) (meaning t m 5039) (meaning t m 5040)

theorem rule12919 (p5986 p5987 : Prop) : (¬ ((¬ p5986) ∨ (¬ p5987))) ∨ (¬ p5986) ∨ (¬ p5987) := by
  classical
  tauto

theorem initial12919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5985)) ∨ (¬ (meaning t m 5986)) ∨ (¬ (meaning t m 5987)) := by
  exact rule12919 (meaning t m 5986) (meaning t m 5987)

theorem rule12920 (p5034 p5985 : Prop) (h : (p5034 ↔ p5985)) : (¬ p5034) ∨ (p5985) := by
  classical
  tauto

theorem initial12920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5034)) ∨ (meaning t m 5985) := by
  have source := ElevenTheory.theory3329 t (m.theta 3 5) (m.theta 3 9) (m.theta 5 9)
  exact rule12920 (meaning t m 5034) (meaning t m 5985) source

theorem rule12922 (p3744 p4033 p4205 p4397 p5043 : Prop) : (p4033) ∨ (((¬ p4033) ∨ (¬ p3744) ∨ (¬ p4205) ∨ (¬ p5043) ∨ (¬ p4397))) := by
  classical
  tauto

theorem initial12922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4033) ∨ (meaning t m 5989) := by
  exact rule12922 (meaning t m 3744) (meaning t m 4033) (meaning t m 4205) (meaning t m 4397) (meaning t m 5043)

theorem rule12923 (p3744 p4033 p4205 p4397 p5043 : Prop) : (p3744) ∨ (((¬ p4033) ∨ (¬ p3744) ∨ (¬ p4205) ∨ (¬ p5043) ∨ (¬ p4397))) := by
  classical
  tauto

theorem initial12923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3744) ∨ (meaning t m 5989) := by
  exact rule12923 (meaning t m 3744) (meaning t m 4033) (meaning t m 4205) (meaning t m 4397) (meaning t m 5043)

theorem rule12924 (p3744 p4033 p4205 p4397 p5043 : Prop) : (p4205) ∨ (((¬ p4033) ∨ (¬ p3744) ∨ (¬ p4205) ∨ (¬ p5043) ∨ (¬ p4397))) := by
  classical
  tauto

theorem initial12924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4205) ∨ (meaning t m 5989) := by
  exact rule12924 (meaning t m 3744) (meaning t m 4033) (meaning t m 4205) (meaning t m 4397) (meaning t m 5043)

theorem rule12926 (p3744 p4033 p4205 p4397 p5043 : Prop) : (p4397) ∨ (((¬ p4033) ∨ (¬ p3744) ∨ (¬ p4205) ∨ (¬ p5043) ∨ (¬ p4397))) := by
  classical
  tauto

theorem initial12926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4397) ∨ (meaning t m 5989) := by
  exact rule12926 (meaning t m 3744) (meaning t m 4033) (meaning t m 4205) (meaning t m 4397) (meaning t m 5043)

theorem rule12928 (p3125 p4334 p4368 p5045 p5046 : Prop) : (p5045) ∨ (((¬ p5045) ∨ (¬ p4334) ∨ (¬ p3125) ∨ (¬ p5046) ∨ (¬ p4368))) := by
  classical
  tauto

theorem initial12928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5045) ∨ (meaning t m 5990) := by
  exact rule12928 (meaning t m 3125) (meaning t m 4334) (meaning t m 4368) (meaning t m 5045) (meaning t m 5046)

theorem rule12929 (p3125 p4334 p4368 p5045 p5046 : Prop) : (p4334) ∨ (((¬ p5045) ∨ (¬ p4334) ∨ (¬ p3125) ∨ (¬ p5046) ∨ (¬ p4368))) := by
  classical
  tauto

theorem initial12929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4334) ∨ (meaning t m 5990) := by
  exact rule12929 (meaning t m 3125) (meaning t m 4334) (meaning t m 4368) (meaning t m 5045) (meaning t m 5046)

theorem rule12930 (p3125 p4334 p4368 p5045 p5046 : Prop) : (p3125) ∨ (((¬ p5045) ∨ (¬ p4334) ∨ (¬ p3125) ∨ (¬ p5046) ∨ (¬ p4368))) := by
  classical
  tauto

theorem initial12930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3125) ∨ (meaning t m 5990) := by
  exact rule12930 (meaning t m 3125) (meaning t m 4334) (meaning t m 4368) (meaning t m 5045) (meaning t m 5046)

theorem rule12932 (p3125 p4334 p4368 p5045 p5046 : Prop) : (p4368) ∨ (((¬ p5045) ∨ (¬ p4334) ∨ (¬ p3125) ∨ (¬ p5046) ∨ (¬ p4368))) := by
  classical
  tauto

theorem initial12932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4368) ∨ (meaning t m 5990) := by
  exact rule12932 (meaning t m 3125) (meaning t m 4334) (meaning t m 4368) (meaning t m 5045) (meaning t m 5046)

theorem rule12936 (p5989 p5990 : Prop) : (¬ ((¬ p5989) ∨ (¬ p5990))) ∨ (¬ p5989) ∨ (¬ p5990) := by
  classical
  tauto

theorem initial12936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5988)) ∨ (¬ (meaning t m 5989)) ∨ (¬ (meaning t m 5990)) := by
  exact rule12936 (meaning t m 5989) (meaning t m 5990)

theorem rule12937 (p5041 p5988 : Prop) (h : (p5041 ↔ p5988)) : (¬ p5041) ∨ (p5988) := by
  classical
  tauto

theorem initial12937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5041)) ∨ (meaning t m 5988) := by
  have source := ElevenTheory.theory3330 t (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule12937 (meaning t m 5041) (meaning t m 5988) source

theorem rule12939 (p1977 p2027 p2622 p2651 p2797 p2963 p4111 : Prop) (h : (¬ p2963) ∨ (¬ p2797) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p4111) ∨ p2622) : (¬ p1977) ∨ (p2027) ∨ (p2622) ∨ (¬ p2651) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial12939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory3331 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule12939 (meaning t m 1977) (meaning t m 2027) (meaning t m 2622) (meaning t m 2651) (meaning t m 2797) (meaning t m 2963) (meaning t m 4111) source

theorem rule12940 (p4315 p4316 p4392 p4906 p5049 : Prop) : (p4316) ∨ (((¬ p4316) ∨ (¬ p4315) ∨ (¬ p4392) ∨ (¬ p5049) ∨ (¬ p4906))) := by
  classical
  tauto

theorem initial12940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4316) ∨ (meaning t m 5992) := by
  exact rule12940 (meaning t m 4315) (meaning t m 4316) (meaning t m 4392) (meaning t m 4906) (meaning t m 5049)

theorem rule12941 (p4315 p4316 p4392 p4906 p5049 : Prop) : (p4315) ∨ (((¬ p4316) ∨ (¬ p4315) ∨ (¬ p4392) ∨ (¬ p5049) ∨ (¬ p4906))) := by
  classical
  tauto

theorem initial12941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4315) ∨ (meaning t m 5992) := by
  exact rule12941 (meaning t m 4315) (meaning t m 4316) (meaning t m 4392) (meaning t m 4906) (meaning t m 5049)

theorem rule12942 (p4315 p4316 p4392 p4906 p5049 : Prop) : (p4392) ∨ (((¬ p4316) ∨ (¬ p4315) ∨ (¬ p4392) ∨ (¬ p5049) ∨ (¬ p4906))) := by
  classical
  tauto

theorem initial12942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4392) ∨ (meaning t m 5992) := by
  exact rule12942 (meaning t m 4315) (meaning t m 4316) (meaning t m 4392) (meaning t m 4906) (meaning t m 5049)

theorem rule12943 (p4315 p4316 p4392 p4906 p5049 : Prop) : (p5049) ∨ (((¬ p4316) ∨ (¬ p4315) ∨ (¬ p4392) ∨ (¬ p5049) ∨ (¬ p4906))) := by
  classical
  tauto

theorem initial12943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5049) ∨ (meaning t m 5992) := by
  exact rule12943 (meaning t m 4315) (meaning t m 4316) (meaning t m 4392) (meaning t m 4906) (meaning t m 5049)

theorem rule12946 (p3136 p4313 p5051 p5052 p5053 : Prop) : (p5051) ∨ (((¬ p5051) ∨ (¬ p4313) ∨ (¬ p3136) ∨ (¬ p5052) ∨ (¬ p5053))) := by
  classical
  tauto

theorem initial12946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5051) ∨ (meaning t m 5993) := by
  exact rule12946 (meaning t m 3136) (meaning t m 4313) (meaning t m 5051) (meaning t m 5052) (meaning t m 5053)

theorem rule12947 (p3136 p4313 p5051 p5052 p5053 : Prop) : (p4313) ∨ (((¬ p5051) ∨ (¬ p4313) ∨ (¬ p3136) ∨ (¬ p5052) ∨ (¬ p5053))) := by
  classical
  tauto

theorem initial12947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4313) ∨ (meaning t m 5993) := by
  exact rule12947 (meaning t m 3136) (meaning t m 4313) (meaning t m 5051) (meaning t m 5052) (meaning t m 5053)

theorem rule12948 (p3136 p4313 p5051 p5052 p5053 : Prop) : (p3136) ∨ (((¬ p5051) ∨ (¬ p4313) ∨ (¬ p3136) ∨ (¬ p5052) ∨ (¬ p5053))) := by
  classical
  tauto

theorem initial12948 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3136) ∨ (meaning t m 5993) := by
  exact rule12948 (meaning t m 3136) (meaning t m 4313) (meaning t m 5051) (meaning t m 5052) (meaning t m 5053)

theorem rule12950 (p3136 p4313 p5051 p5052 p5053 : Prop) : (p5053) ∨ (((¬ p5051) ∨ (¬ p4313) ∨ (¬ p3136) ∨ (¬ p5052) ∨ (¬ p5053))) := by
  classical
  tauto

theorem initial12950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5053) ∨ (meaning t m 5993) := by
  exact rule12950 (meaning t m 3136) (meaning t m 4313) (meaning t m 5051) (meaning t m 5052) (meaning t m 5053)

theorem rule12954 (p5992 p5993 : Prop) : (¬ ((¬ p5992) ∨ (¬ p5993))) ∨ (¬ p5992) ∨ (¬ p5993) := by
  classical
  tauto

theorem initial12954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5991)) ∨ (¬ (meaning t m 5992)) ∨ (¬ (meaning t m 5993)) := by
  exact rule12954 (meaning t m 5992) (meaning t m 5993)

theorem rule12955 (p5047 p5991 : Prop) (h : (p5047 ↔ p5991)) : (¬ p5047) ∨ (p5991) := by
  classical
  tauto

theorem initial12955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5047)) ∨ (meaning t m 5991) := by
  have source := ElevenTheory.theory3332 t (m.theta 2 3) (m.theta 2 5) (m.theta 3 5)
  exact rule12955 (meaning t m 5047) (meaning t m 5991) source

theorem rule12957 (p3692 p3949 p4335 p4450 p5056 : Prop) : (p3949) ∨ (((¬ p3949) ∨ (¬ p3692) ∨ (¬ p4335) ∨ (¬ p5056) ∨ (¬ p4450))) := by
  classical
  tauto

theorem initial12957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3949) ∨ (meaning t m 5995) := by
  exact rule12957 (meaning t m 3692) (meaning t m 3949) (meaning t m 4335) (meaning t m 4450) (meaning t m 5056)

end SunPrize.SMT
