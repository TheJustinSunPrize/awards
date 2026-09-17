import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory000
import SunPrize.Certificate.Theory001
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule3502 (p2044 p2688 : Prop) (h : ((¬ p2044) ↔ (¬ p2688))) : (p2044) ∨ (¬ p2688) := by
  classical
  tauto

theorem initial3502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2044) ∨ (¬ (meaning t m 2688)) := by
  have source := ElevenTheory.theory144 t (m.theta 1 3)
  exact rule3502 (meaning t m 2044) (meaning t m 2688) source

theorem rule3504 (p566 p572 : Prop) : (¬ p566) ∨ ((p566 ∨ p572)) := by
  classical
  tauto

theorem initial3504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 566)) ∨ (meaning t m 2689) := by
  exact rule3504 (meaning t m 566) (meaning t m 572)

theorem rule3505 (p566 p572 : Prop) : (¬ p572) ∨ ((p566 ∨ p572)) := by
  classical
  tauto

theorem initial3505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 572)) ∨ (meaning t m 2689) := by
  exact rule3505 (meaning t m 566) (meaning t m 572)

theorem rule3522 (p2689 p2690 : Prop) (h : (p2689 ↔ p2690)) : (¬ p2689) ∨ (p2690) := by
  classical
  tauto

theorem initial3522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2689)) ∨ (meaning t m 2690) := by
  have source := ElevenTheory.theory145 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3)
  exact rule3522 (meaning t m 2689) (meaning t m 2690) source

theorem rule3524 (p2045 p2699 : Prop) (h : ((¬ p2045) ↔ (¬ p2699))) : (p2045) ∨ (¬ p2699) := by
  classical
  tauto

theorem initial3524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2045) ∨ (¬ (meaning t m 2699)) := by
  have source := ElevenTheory.theory146 t (m.theta 0 1)
  exact rule3524 (meaning t m 2045) (meaning t m 2699) source

theorem rule3526 (p578 p584 : Prop) : (¬ p578) ∨ ((p578 ∨ p584)) := by
  classical
  tauto

theorem initial3526 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 578)) ∨ (meaning t m 2700) := by
  exact rule3526 (meaning t m 578) (meaning t m 584)

theorem rule3527 (p578 p584 : Prop) : (¬ p584) ∨ ((p578 ∨ p584)) := by
  classical
  tauto

theorem initial3527 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 584)) ∨ (meaning t m 2700) := by
  exact rule3527 (meaning t m 578) (meaning t m 584)

theorem rule3544 (p2700 p2701 : Prop) (h : (p2700 ↔ p2701)) : (¬ p2700) ∨ (p2701) := by
  classical
  tauto

theorem initial3544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2700)) ∨ (meaning t m 2701) := by
  have source := ElevenTheory.theory147 t (m.theta 1 2) (m.theta 1 7) (m.theta 2 7)
  exact rule3544 (meaning t m 2700) (meaning t m 2701) source

theorem rule3546 (p590 p596 : Prop) : (¬ p590) ∨ ((p590 ∨ p596)) := by
  classical
  tauto

theorem initial3546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 590)) ∨ (meaning t m 2710) := by
  exact rule3546 (meaning t m 590) (meaning t m 596)

theorem rule3547 (p590 p596 : Prop) : (¬ p596) ∨ ((p590 ∨ p596)) := by
  classical
  tauto

theorem initial3547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 596)) ∨ (meaning t m 2710) := by
  exact rule3547 (meaning t m 590) (meaning t m 596)

theorem rule3564 (p2710 p2711 : Prop) (h : (p2710 ↔ p2711)) : (¬ p2710) ∨ (p2711) := by
  classical
  tauto

theorem initial3564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2710)) ∨ (meaning t m 2711) := by
  have source := ElevenTheory.theory148 t (m.theta 2 7) (m.theta 2 8) (m.theta 7 8)
  exact rule3564 (meaning t m 2710) (meaning t m 2711) source

theorem rule3566 (p602 p608 : Prop) : (¬ p602) ∨ ((p602 ∨ p608)) := by
  classical
  tauto

theorem initial3566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 602)) ∨ (meaning t m 2720) := by
  exact rule3566 (meaning t m 602) (meaning t m 608)

theorem rule3567 (p602 p608 : Prop) : (¬ p608) ∨ ((p602 ∨ p608)) := by
  classical
  tauto

theorem initial3567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 608)) ∨ (meaning t m 2720) := by
  exact rule3567 (meaning t m 602) (meaning t m 608)

theorem rule3584 (p2720 p2721 : Prop) (h : (p2720 ↔ p2721)) : (¬ p2720) ∨ (p2721) := by
  classical
  tauto

theorem initial3584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2720)) ∨ (meaning t m 2721) := by
  have source := ElevenTheory.theory149 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 4)
  exact rule3584 (meaning t m 2720) (meaning t m 2721) source

theorem rule3586 (p614 p620 : Prop) : (¬ p614) ∨ ((p614 ∨ p620)) := by
  classical
  tauto

theorem initial3586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 614)) ∨ (meaning t m 2730) := by
  exact rule3586 (meaning t m 614) (meaning t m 620)

theorem rule3587 (p614 p620 : Prop) : (¬ p620) ∨ ((p614 ∨ p620)) := by
  classical
  tauto

theorem initial3587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 620)) ∨ (meaning t m 2730) := by
  exact rule3587 (meaning t m 614) (meaning t m 620)

theorem rule3604 (p2730 p2731 : Prop) (h : (p2730 ↔ p2731)) : (¬ p2730) ∨ (p2731) := by
  classical
  tauto

theorem initial3604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2730)) ∨ (meaning t m 2731) := by
  have source := ElevenTheory.theory150 t (m.theta 1 2) (m.theta 1 3) (m.theta 2 3)
  exact rule3604 (meaning t m 2730) (meaning t m 2731) source

theorem rule3606 (p2741 p2742 p2743 p2744 p2745 : Prop) : (¬ (p2741 ∧ p2742 ∧ p2743 ∧ p2744 ∧ p2745)) ∨ (p2741) := by
  classical
  tauto

theorem initial3606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2740)) ∨ (meaning t m 2741) := by
  exact rule3606 (meaning t m 2741) (meaning t m 2742) (meaning t m 2743) (meaning t m 2744) (meaning t m 2745)

theorem rule3607 (p2741 p2742 p2743 p2744 p2745 : Prop) : (¬ (p2741 ∧ p2742 ∧ p2743 ∧ p2744 ∧ p2745)) ∨ (p2742) := by
  classical
  tauto

theorem initial3607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2740)) ∨ (meaning t m 2742) := by
  exact rule3607 (meaning t m 2741) (meaning t m 2742) (meaning t m 2743) (meaning t m 2744) (meaning t m 2745)

theorem rule3608 (p2741 p2742 p2743 p2744 p2745 : Prop) : (¬ (p2741 ∧ p2742 ∧ p2743 ∧ p2744 ∧ p2745)) ∨ (p2743) := by
  classical
  tauto

theorem initial3608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2740)) ∨ (meaning t m 2743) := by
  exact rule3608 (meaning t m 2741) (meaning t m 2742) (meaning t m 2743) (meaning t m 2744) (meaning t m 2745)

theorem rule3609 (p2741 p2742 p2743 p2744 p2745 : Prop) : (¬ (p2741 ∧ p2742 ∧ p2743 ∧ p2744 ∧ p2745)) ∨ (p2744) := by
  classical
  tauto

theorem initial3609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2740)) ∨ (meaning t m 2744) := by
  exact rule3609 (meaning t m 2741) (meaning t m 2742) (meaning t m 2743) (meaning t m 2744) (meaning t m 2745)

theorem rule3610 (p2741 p2742 p2743 p2744 p2745 : Prop) : (¬ (p2741 ∧ p2742 ∧ p2743 ∧ p2744 ∧ p2745)) ∨ (p2745) := by
  classical
  tauto

theorem initial3610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2740)) ∨ (meaning t m 2745) := by
  exact rule3610 (meaning t m 2741) (meaning t m 2742) (meaning t m 2743) (meaning t m 2744) (meaning t m 2745)

theorem rule3612 (p2741 p2742 p2743 p2744 p2745 : Prop) : (p2744) ∨ (((¬ p2744) ∨ (¬ p2745) ∨ (¬ p2742) ∨ (¬ p2743) ∨ (¬ p2741))) := by
  classical
  tauto

theorem initial3612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2744) ∨ (meaning t m 2746) := by
  exact rule3612 (meaning t m 2741) (meaning t m 2742) (meaning t m 2743) (meaning t m 2744) (meaning t m 2745)

theorem rule3614 (p2741 p2742 p2743 p2744 p2745 : Prop) : (p2742) ∨ (((¬ p2744) ∨ (¬ p2745) ∨ (¬ p2742) ∨ (¬ p2743) ∨ (¬ p2741))) := by
  classical
  tauto

theorem initial3614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2742) ∨ (meaning t m 2746) := by
  exact rule3614 (meaning t m 2741) (meaning t m 2742) (meaning t m 2743) (meaning t m 2744) (meaning t m 2745)

theorem rule3616 (p2741 p2742 p2743 p2744 p2745 : Prop) : (p2741) ∨ (((¬ p2744) ∨ (¬ p2745) ∨ (¬ p2742) ∨ (¬ p2743) ∨ (¬ p2741))) := by
  classical
  tauto

theorem initial3616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2741) ∨ (meaning t m 2746) := by
  exact rule3616 (meaning t m 2741) (meaning t m 2742) (meaning t m 2743) (meaning t m 2744) (meaning t m 2745)

theorem rule3618 (p2740 p2746 : Prop) (h : (p2740 ↔ (¬ p2746))) : (¬ p2740) ∨ (¬ p2746) := by
  classical
  tauto

theorem initial3618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2740)) ∨ (¬ (meaning t m 2746)) := by
  have source := ElevenTheory.theory151 t (m.theta 1 2) (m.theta 1 3) (m.theta 2 3)
  exact rule3618 (meaning t m 2740) (meaning t m 2746) source

theorem rule3620 (p2737 p2748 p2749 p2750 p2751 : Prop) : (¬ (p2748 ∧ p2749 ∧ p2737 ∧ p2750 ∧ p2751)) ∨ (p2748) := by
  classical
  tauto

theorem initial3620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2747)) ∨ (meaning t m 2748) := by
  exact rule3620 (meaning t m 2737) (meaning t m 2748) (meaning t m 2749) (meaning t m 2750) (meaning t m 2751)

theorem rule3621 (p2737 p2748 p2749 p2750 p2751 : Prop) : (¬ (p2748 ∧ p2749 ∧ p2737 ∧ p2750 ∧ p2751)) ∨ (p2749) := by
  classical
  tauto

theorem initial3621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2747)) ∨ (meaning t m 2749) := by
  exact rule3621 (meaning t m 2737) (meaning t m 2748) (meaning t m 2749) (meaning t m 2750) (meaning t m 2751)

theorem rule3622 (p2737 p2748 p2749 p2750 p2751 : Prop) : (p2737) ∨ (¬ (p2748 ∧ p2749 ∧ p2737 ∧ p2750 ∧ p2751)) := by
  classical
  tauto

theorem initial3622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2737) ∨ (¬ (meaning t m 2747)) := by
  exact rule3622 (meaning t m 2737) (meaning t m 2748) (meaning t m 2749) (meaning t m 2750) (meaning t m 2751)

theorem rule3623 (p2737 p2748 p2749 p2750 p2751 : Prop) : (¬ (p2748 ∧ p2749 ∧ p2737 ∧ p2750 ∧ p2751)) ∨ (p2750) := by
  classical
  tauto

theorem initial3623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2747)) ∨ (meaning t m 2750) := by
  exact rule3623 (meaning t m 2737) (meaning t m 2748) (meaning t m 2749) (meaning t m 2750) (meaning t m 2751)

theorem rule3624 (p2737 p2748 p2749 p2750 p2751 : Prop) : (¬ (p2748 ∧ p2749 ∧ p2737 ∧ p2750 ∧ p2751)) ∨ (p2751) := by
  classical
  tauto

theorem initial3624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2747)) ∨ (meaning t m 2751) := by
  exact rule3624 (meaning t m 2737) (meaning t m 2748) (meaning t m 2749) (meaning t m 2750) (meaning t m 2751)

theorem rule3627 (p2737 p2748 p2749 p2750 p2751 : Prop) : (p2750) ∨ (((¬ p2737) ∨ (¬ p2750) ∨ (¬ p2748) ∨ (¬ p2749) ∨ (¬ p2751))) := by
  classical
  tauto

theorem initial3627 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2750) ∨ (meaning t m 2752) := by
  exact rule3627 (meaning t m 2737) (meaning t m 2748) (meaning t m 2749) (meaning t m 2750) (meaning t m 2751)

theorem rule3628 (p2737 p2748 p2749 p2750 p2751 : Prop) : (p2748) ∨ (((¬ p2737) ∨ (¬ p2750) ∨ (¬ p2748) ∨ (¬ p2749) ∨ (¬ p2751))) := by
  classical
  tauto

theorem initial3628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2748) ∨ (meaning t m 2752) := by
  exact rule3628 (meaning t m 2737) (meaning t m 2748) (meaning t m 2749) (meaning t m 2750) (meaning t m 2751)

theorem rule3629 (p2737 p2748 p2749 p2750 p2751 : Prop) : (p2749) ∨ (((¬ p2737) ∨ (¬ p2750) ∨ (¬ p2748) ∨ (¬ p2749) ∨ (¬ p2751))) := by
  classical
  tauto

theorem initial3629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2749) ∨ (meaning t m 2752) := by
  exact rule3629 (meaning t m 2737) (meaning t m 2748) (meaning t m 2749) (meaning t m 2750) (meaning t m 2751)

theorem rule3632 (p2747 p2752 : Prop) (h : (p2747 ↔ (¬ p2752))) : (¬ p2747) ∨ (¬ p2752) := by
  classical
  tauto

theorem initial3632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2747)) ∨ (¬ (meaning t m 2752)) := by
  have source := ElevenTheory.theory152 t (m.theta 1 2) (m.theta 1 3) (m.theta 2 3)
  exact rule3632 (meaning t m 2747) (meaning t m 2752) source

theorem rule3634 (p2696 p2743 p2753 : Prop) (h : (¬ p2753) ∨ (¬ p2696) ∨ (¬ p2743)) : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2753) := by
  classical
  tauto

theorem initial3634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2753)) := by
  have source := ElevenTheory.theory153 (m.theta 0 2) (m.theta 1 2) (m.theta 2 3)
  exact rule3634 (meaning t m 2696) (meaning t m 2743) (meaning t m 2753) source

theorem rule3635 (p626 p632 : Prop) : (¬ p626) ∨ ((p626 ∨ p632)) := by
  classical
  tauto

theorem initial3635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 626)) ∨ (meaning t m 2754) := by
  exact rule3635 (meaning t m 626) (meaning t m 632)

theorem rule3636 (p626 p632 : Prop) : (¬ p632) ∨ ((p626 ∨ p632)) := by
  classical
  tauto

theorem initial3636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 632)) ∨ (meaning t m 2754) := by
  exact rule3636 (meaning t m 626) (meaning t m 632)

theorem rule3653 (p2754 p2755 : Prop) (h : (p2754 ↔ p2755)) : (¬ p2754) ∨ (p2755) := by
  classical
  tauto

theorem initial3653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2754)) ∨ (meaning t m 2755) := by
  have source := ElevenTheory.theory154 t (m.theta 7 10) (m.theta 7 9) (m.theta 9 10)
  exact rule3653 (meaning t m 2754) (meaning t m 2755) source

theorem rule3655 (p2046 p2764 : Prop) (h : ((¬ p2046) ↔ (¬ p2764))) : (p2046) ∨ (¬ p2764) := by
  classical
  tauto

theorem initial3655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2046) ∨ (¬ (meaning t m 2764)) := by
  have source := ElevenTheory.theory155 t (m.theta 9 10)
  exact rule3655 (meaning t m 2046) (meaning t m 2764) source

theorem rule3657 (p2047 p2765 : Prop) (h : ((¬ p2047) ↔ (¬ p2765))) : (p2047) ∨ (¬ p2765) := by
  classical
  tauto

theorem initial3657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2047) ∨ (¬ (meaning t m 2765)) := by
  have source := ElevenTheory.theory156 t (m.theta 5 6)
  exact rule3657 (meaning t m 2047) (meaning t m 2765) source

theorem rule3659 (p2048 p2766 : Prop) (h : ((¬ p2048) ↔ (¬ p2766))) : (p2048) ∨ (¬ p2766) := by
  classical
  tauto

theorem initial3659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2048) ∨ (¬ (meaning t m 2766)) := by
  have source := ElevenTheory.theory157 t (m.theta 8 9)
  exact rule3659 (meaning t m 2048) (meaning t m 2766) source

theorem rule3661 (p638 p644 : Prop) : (¬ p638) ∨ ((p638 ∨ p644)) := by
  classical
  tauto

theorem initial3661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 638)) ∨ (meaning t m 2767) := by
  exact rule3661 (meaning t m 638) (meaning t m 644)

theorem rule3662 (p638 p644 : Prop) : (¬ p644) ∨ ((p638 ∨ p644)) := by
  classical
  tauto

theorem initial3662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 644)) ∨ (meaning t m 2767) := by
  exact rule3662 (meaning t m 638) (meaning t m 644)

theorem rule3679 (p2767 p2768 : Prop) (h : (p2767 ↔ p2768)) : (¬ p2767) ∨ (p2768) := by
  classical
  tauto

theorem initial3679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2767)) ∨ (meaning t m 2768) := by
  have source := ElevenTheory.theory158 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 6)
  exact rule3679 (meaning t m 2767) (meaning t m 2768) source

theorem rule3681 (p2778 p2779 p2780 p2781 p2782 : Prop) : (¬ (p2778 ∧ p2779 ∧ p2780 ∧ p2781 ∧ p2782)) ∨ (p2778) := by
  classical
  tauto

theorem initial3681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2777)) ∨ (meaning t m 2778) := by
  exact rule3681 (meaning t m 2778) (meaning t m 2779) (meaning t m 2780) (meaning t m 2781) (meaning t m 2782)

theorem rule3682 (p2778 p2779 p2780 p2781 p2782 : Prop) : (¬ (p2778 ∧ p2779 ∧ p2780 ∧ p2781 ∧ p2782)) ∨ (p2779) := by
  classical
  tauto

theorem initial3682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2777)) ∨ (meaning t m 2779) := by
  exact rule3682 (meaning t m 2778) (meaning t m 2779) (meaning t m 2780) (meaning t m 2781) (meaning t m 2782)

theorem rule3683 (p2778 p2779 p2780 p2781 p2782 : Prop) : (¬ (p2778 ∧ p2779 ∧ p2780 ∧ p2781 ∧ p2782)) ∨ (p2780) := by
  classical
  tauto

theorem initial3683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2777)) ∨ (meaning t m 2780) := by
  exact rule3683 (meaning t m 2778) (meaning t m 2779) (meaning t m 2780) (meaning t m 2781) (meaning t m 2782)

theorem rule3684 (p2778 p2779 p2780 p2781 p2782 : Prop) : (¬ (p2778 ∧ p2779 ∧ p2780 ∧ p2781 ∧ p2782)) ∨ (p2781) := by
  classical
  tauto

theorem initial3684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2777)) ∨ (meaning t m 2781) := by
  exact rule3684 (meaning t m 2778) (meaning t m 2779) (meaning t m 2780) (meaning t m 2781) (meaning t m 2782)

theorem rule3685 (p2778 p2779 p2780 p2781 p2782 : Prop) : (¬ (p2778 ∧ p2779 ∧ p2780 ∧ p2781 ∧ p2782)) ∨ (p2782) := by
  classical
  tauto

theorem initial3685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2777)) ∨ (meaning t m 2782) := by
  exact rule3685 (meaning t m 2778) (meaning t m 2779) (meaning t m 2780) (meaning t m 2781) (meaning t m 2782)

theorem rule3687 (p2778 p2779 p2780 p2781 p2782 : Prop) : (p2781) ∨ (((¬ p2781) ∨ (¬ p2780) ∨ (¬ p2782) ∨ (¬ p2778) ∨ (¬ p2779))) := by
  classical
  tauto

theorem initial3687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2781) ∨ (meaning t m 2783) := by
  exact rule3687 (meaning t m 2778) (meaning t m 2779) (meaning t m 2780) (meaning t m 2781) (meaning t m 2782)

theorem rule3690 (p2778 p2779 p2780 p2781 p2782 : Prop) : (p2778) ∨ (((¬ p2781) ∨ (¬ p2780) ∨ (¬ p2782) ∨ (¬ p2778) ∨ (¬ p2779))) := by
  classical
  tauto

theorem initial3690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2778) ∨ (meaning t m 2783) := by
  exact rule3690 (meaning t m 2778) (meaning t m 2779) (meaning t m 2780) (meaning t m 2781) (meaning t m 2782)

theorem rule3691 (p2778 p2779 p2780 p2781 p2782 : Prop) : (p2779) ∨ (((¬ p2781) ∨ (¬ p2780) ∨ (¬ p2782) ∨ (¬ p2778) ∨ (¬ p2779))) := by
  classical
  tauto

theorem initial3691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2779) ∨ (meaning t m 2783) := by
  exact rule3691 (meaning t m 2778) (meaning t m 2779) (meaning t m 2780) (meaning t m 2781) (meaning t m 2782)

theorem rule3693 (p2777 p2783 : Prop) (h : (p2777 ↔ (¬ p2783))) : (¬ p2777) ∨ (¬ p2783) := by
  classical
  tauto

theorem initial3693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2777)) ∨ (¬ (meaning t m 2783)) := by
  have source := ElevenTheory.theory159 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 6)
  exact rule3693 (meaning t m 2777) (meaning t m 2783) source

theorem rule3695 (p2774 p2785 p2786 p2787 p2788 : Prop) : (¬ (p2785 ∧ p2786 ∧ p2774 ∧ p2787 ∧ p2788)) ∨ (p2785) := by
  classical
  tauto

theorem initial3695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2784)) ∨ (meaning t m 2785) := by
  exact rule3695 (meaning t m 2774) (meaning t m 2785) (meaning t m 2786) (meaning t m 2787) (meaning t m 2788)

theorem rule3696 (p2774 p2785 p2786 p2787 p2788 : Prop) : (¬ (p2785 ∧ p2786 ∧ p2774 ∧ p2787 ∧ p2788)) ∨ (p2786) := by
  classical
  tauto

theorem initial3696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2784)) ∨ (meaning t m 2786) := by
  exact rule3696 (meaning t m 2774) (meaning t m 2785) (meaning t m 2786) (meaning t m 2787) (meaning t m 2788)

theorem rule3697 (p2774 p2785 p2786 p2787 p2788 : Prop) : (p2774) ∨ (¬ (p2785 ∧ p2786 ∧ p2774 ∧ p2787 ∧ p2788)) := by
  classical
  tauto

theorem initial3697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2774) ∨ (¬ (meaning t m 2784)) := by
  exact rule3697 (meaning t m 2774) (meaning t m 2785) (meaning t m 2786) (meaning t m 2787) (meaning t m 2788)

theorem rule3698 (p2774 p2785 p2786 p2787 p2788 : Prop) : (¬ (p2785 ∧ p2786 ∧ p2774 ∧ p2787 ∧ p2788)) ∨ (p2787) := by
  classical
  tauto

theorem initial3698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2784)) ∨ (meaning t m 2787) := by
  exact rule3698 (meaning t m 2774) (meaning t m 2785) (meaning t m 2786) (meaning t m 2787) (meaning t m 2788)

theorem rule3699 (p2774 p2785 p2786 p2787 p2788 : Prop) : (¬ (p2785 ∧ p2786 ∧ p2774 ∧ p2787 ∧ p2788)) ∨ (p2788) := by
  classical
  tauto

theorem initial3699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2784)) ∨ (meaning t m 2788) := by
  exact rule3699 (meaning t m 2774) (meaning t m 2785) (meaning t m 2786) (meaning t m 2787) (meaning t m 2788)

theorem rule3701 (p2774 p2785 p2786 p2787 p2788 : Prop) : (p2786) ∨ (((¬ p2786) ∨ (¬ p2774) ∨ (¬ p2785) ∨ (¬ p2787) ∨ (¬ p2788))) := by
  classical
  tauto

theorem initial3701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2786) ∨ (meaning t m 2789) := by
  exact rule3701 (meaning t m 2774) (meaning t m 2785) (meaning t m 2786) (meaning t m 2787) (meaning t m 2788)

theorem rule3703 (p2774 p2785 p2786 p2787 p2788 : Prop) : (p2785) ∨ (((¬ p2786) ∨ (¬ p2774) ∨ (¬ p2785) ∨ (¬ p2787) ∨ (¬ p2788))) := by
  classical
  tauto

theorem initial3703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2785) ∨ (meaning t m 2789) := by
  exact rule3703 (meaning t m 2774) (meaning t m 2785) (meaning t m 2786) (meaning t m 2787) (meaning t m 2788)

theorem rule3707 (p2784 p2789 : Prop) (h : (p2784 ↔ (¬ p2789))) : (¬ p2784) ∨ (¬ p2789) := by
  classical
  tauto

theorem initial3707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2784)) ∨ (¬ (meaning t m 2789)) := by
  have source := ElevenTheory.theory160 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 6)
  exact rule3707 (meaning t m 2784) (meaning t m 2789) source

theorem rule3709 (p650 p656 : Prop) : (¬ p650) ∨ ((p650 ∨ p656)) := by
  classical
  tauto

theorem initial3709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 650)) ∨ (meaning t m 2790) := by
  exact rule3709 (meaning t m 650) (meaning t m 656)

theorem rule3710 (p650 p656 : Prop) : (¬ p656) ∨ ((p650 ∨ p656)) := by
  classical
  tauto

theorem initial3710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 656)) ∨ (meaning t m 2790) := by
  exact rule3710 (meaning t m 650) (meaning t m 656)

theorem rule3727 (p2790 p2791 : Prop) (h : (p2790 ↔ p2791)) : (¬ p2790) ∨ (p2791) := by
  classical
  tauto

theorem initial3727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2790)) ∨ (meaning t m 2791) := by
  have source := ElevenTheory.theory161 t (m.theta 2 3) (m.theta 2 6) (m.theta 3 6)
  exact rule3727 (meaning t m 2790) (meaning t m 2791) source

theorem rule3729 (p662 p668 : Prop) : (¬ p662) ∨ ((p662 ∨ p668)) := by
  classical
  tauto

theorem initial3729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 662)) ∨ (meaning t m 2800) := by
  exact rule3729 (meaning t m 662) (meaning t m 668)

theorem rule3730 (p662 p668 : Prop) : (¬ p668) ∨ ((p662 ∨ p668)) := by
  classical
  tauto

theorem initial3730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 668)) ∨ (meaning t m 2800) := by
  exact rule3730 (meaning t m 662) (meaning t m 668)

theorem rule3747 (p2800 p2801 : Prop) (h : (p2800 ↔ p2801)) : (¬ p2800) ∨ (p2801) := by
  classical
  tauto

theorem initial3747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2800)) ∨ (meaning t m 2801) := by
  have source := ElevenTheory.theory162 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 7)
  exact rule3747 (meaning t m 2800) (meaning t m 2801) source

theorem rule3749 (p2651 p2810 p2811 : Prop) (h : (¬ p2810) ∨ (¬ p2811) ∨ (¬ p2651)) : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2811) := by
  classical
  tauto

theorem initial3749 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2811)) := by
  have source := ElevenTheory.theory163 (m.theta 0 3) (m.theta 2 3) (m.theta 3 4)
  exact rule3749 (meaning t m 2651) (meaning t m 2810) (meaning t m 2811) source

theorem rule3750 (p674 p680 : Prop) : (¬ p674) ∨ ((p674 ∨ p680)) := by
  classical
  tauto

theorem initial3750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 674)) ∨ (meaning t m 2812) := by
  exact rule3750 (meaning t m 674) (meaning t m 680)

theorem rule3751 (p674 p680 : Prop) : (¬ p680) ∨ ((p674 ∨ p680)) := by
  classical
  tauto

theorem initial3751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 680)) ∨ (meaning t m 2812) := by
  exact rule3751 (meaning t m 674) (meaning t m 680)

theorem rule3768 (p2812 p2813 : Prop) (h : (p2812 ↔ p2813)) : (¬ p2812) ∨ (p2813) := by
  classical
  tauto

theorem initial3768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2812)) ∨ (meaning t m 2813) := by
  have source := ElevenTheory.theory164 t (m.theta 2 6) (m.theta 2 8) (m.theta 6 8)
  exact rule3768 (meaning t m 2812) (meaning t m 2813) source

theorem rule3770 (p686 p692 : Prop) : (¬ p686) ∨ ((p686 ∨ p692)) := by
  classical
  tauto

theorem initial3770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 686)) ∨ (meaning t m 2822) := by
  exact rule3770 (meaning t m 686) (meaning t m 692)

theorem rule3771 (p686 p692 : Prop) : (¬ p692) ∨ ((p686 ∨ p692)) := by
  classical
  tauto

theorem initial3771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 692)) ∨ (meaning t m 2822) := by
  exact rule3771 (meaning t m 686) (meaning t m 692)

theorem rule3788 (p2822 p2823 : Prop) (h : (p2822 ↔ p2823)) : (¬ p2822) ∨ (p2823) := by
  classical
  tauto

theorem initial3788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2822)) ∨ (meaning t m 2823) := by
  have source := ElevenTheory.theory165 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 6)
  exact rule3788 (meaning t m 2822) (meaning t m 2823) source

theorem rule3790 (p698 p704 : Prop) : (¬ p698) ∨ ((p698 ∨ p704)) := by
  classical
  tauto

theorem initial3790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 698)) ∨ (meaning t m 2832) := by
  exact rule3790 (meaning t m 698) (meaning t m 704)

theorem rule3791 (p698 p704 : Prop) : (¬ p704) ∨ ((p698 ∨ p704)) := by
  classical
  tauto

theorem initial3791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 704)) ∨ (meaning t m 2832) := by
  exact rule3791 (meaning t m 698) (meaning t m 704)

theorem rule3808 (p2832 p2833 : Prop) (h : (p2832 ↔ p2833)) : (¬ p2832) ∨ (p2833) := by
  classical
  tauto

theorem initial3808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2832)) ∨ (meaning t m 2833) := by
  have source := ElevenTheory.theory166 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 5)
  exact rule3808 (meaning t m 2832) (meaning t m 2833) source

theorem rule3810 (p2049 p2842 : Prop) (h : ((¬ p2049) ↔ (¬ p2842))) : (p2049) ∨ (¬ p2842) := by
  classical
  tauto

theorem initial3810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2049) ∨ (¬ (meaning t m 2842)) := by
  have source := ElevenTheory.theory167 t (m.theta 2 4)
  exact rule3810 (meaning t m 2049) (meaning t m 2842) source

theorem rule3812 (p710 p716 : Prop) : (¬ p710) ∨ ((p710 ∨ p716)) := by
  classical
  tauto

theorem initial3812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 710)) ∨ (meaning t m 2843) := by
  exact rule3812 (meaning t m 710) (meaning t m 716)

theorem rule3813 (p710 p716 : Prop) : (¬ p716) ∨ ((p710 ∨ p716)) := by
  classical
  tauto

theorem initial3813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 716)) ∨ (meaning t m 2843) := by
  exact rule3813 (meaning t m 710) (meaning t m 716)

theorem rule3830 (p2843 p2844 : Prop) (h : (p2843 ↔ p2844)) : (¬ p2843) ∨ (p2844) := by
  classical
  tauto

theorem initial3830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2843)) ∨ (meaning t m 2844) := by
  have source := ElevenTheory.theory168 t (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule3830 (meaning t m 2843) (meaning t m 2844) source

theorem rule3832 (p722 p728 : Prop) : (¬ p722) ∨ ((p722 ∨ p728)) := by
  classical
  tauto

theorem initial3832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 722)) ∨ (meaning t m 2853) := by
  exact rule3832 (meaning t m 722) (meaning t m 728)

theorem rule3833 (p722 p728 : Prop) : (¬ p728) ∨ ((p722 ∨ p728)) := by
  classical
  tauto

theorem initial3833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 728)) ∨ (meaning t m 2853) := by
  exact rule3833 (meaning t m 722) (meaning t m 728)

theorem rule3850 (p2853 p2854 : Prop) (h : (p2853 ↔ p2854)) : (¬ p2853) ∨ (p2854) := by
  classical
  tauto

theorem initial3850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2853)) ∨ (meaning t m 2854) := by
  have source := ElevenTheory.theory169 t (m.theta 2 5) (m.theta 2 6) (m.theta 5 6)
  exact rule3850 (meaning t m 2853) (meaning t m 2854) source

theorem rule3852 (p734 p740 : Prop) : (¬ p734) ∨ ((p734 ∨ p740)) := by
  classical
  tauto

theorem initial3852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 734)) ∨ (meaning t m 2863) := by
  exact rule3852 (meaning t m 734) (meaning t m 740)

theorem rule3853 (p734 p740 : Prop) : (¬ p740) ∨ ((p734 ∨ p740)) := by
  classical
  tauto

theorem initial3853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 740)) ∨ (meaning t m 2863) := by
  exact rule3853 (meaning t m 734) (meaning t m 740)

theorem rule3870 (p2863 p2864 : Prop) (h : (p2863 ↔ p2864)) : (¬ p2863) ∨ (p2864) := by
  classical
  tauto

theorem initial3870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2863)) ∨ (meaning t m 2864) := by
  have source := ElevenTheory.theory170 t (m.theta 2 5) (m.theta 2 7) (m.theta 5 7)
  exact rule3870 (meaning t m 2863) (meaning t m 2864) source

theorem rule3872 (p2050 p2873 : Prop) (h : ((¬ p2050) ↔ (¬ p2873))) : (p2050) ∨ (¬ p2873) := by
  classical
  tauto

theorem initial3872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2050) ∨ (¬ (meaning t m 2873)) := by
  have source := ElevenTheory.theory171 t (m.theta 1 5)
  exact rule3872 (meaning t m 2050) (meaning t m 2873) source

theorem rule3874 (p746 p752 : Prop) : (¬ p746) ∨ ((p746 ∨ p752)) := by
  classical
  tauto

theorem initial3874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 746)) ∨ (meaning t m 2874) := by
  exact rule3874 (meaning t m 746) (meaning t m 752)

theorem rule3875 (p746 p752 : Prop) : (¬ p752) ∨ ((p746 ∨ p752)) := by
  classical
  tauto

theorem initial3875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 752)) ∨ (meaning t m 2874) := by
  exact rule3875 (meaning t m 746) (meaning t m 752)

theorem rule3892 (p2874 p2875 : Prop) (h : (p2874 ↔ p2875)) : (¬ p2874) ∨ (p2875) := by
  classical
  tauto

theorem initial3892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2874)) ∨ (meaning t m 2875) := by
  have source := ElevenTheory.theory172 t (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule3892 (meaning t m 2874) (meaning t m 2875) source

theorem rule3894 (p758 p764 : Prop) : (¬ p758) ∨ ((p758 ∨ p764)) := by
  classical
  tauto

theorem initial3894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 758)) ∨ (meaning t m 2884) := by
  exact rule3894 (meaning t m 758) (meaning t m 764)

theorem rule3895 (p758 p764 : Prop) : (¬ p764) ∨ ((p758 ∨ p764)) := by
  classical
  tauto

theorem initial3895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 764)) ∨ (meaning t m 2884) := by
  exact rule3895 (meaning t m 758) (meaning t m 764)

theorem rule3912 (p2884 p2885 : Prop) (h : (p2884 ↔ p2885)) : (¬ p2884) ∨ (p2885) := by
  classical
  tauto

theorem initial3912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2884)) ∨ (meaning t m 2885) := by
  have source := ElevenTheory.theory173 t (m.theta 1 5) (m.theta 1 7) (m.theta 5 7)
  exact rule3912 (meaning t m 2884) (meaning t m 2885) source

theorem rule3914 (p770 p776 : Prop) : (¬ p770) ∨ ((p770 ∨ p776)) := by
  classical
  tauto

theorem initial3914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 770)) ∨ (meaning t m 2894) := by
  exact rule3914 (meaning t m 770) (meaning t m 776)

theorem rule3915 (p770 p776 : Prop) : (¬ p776) ∨ ((p770 ∨ p776)) := by
  classical
  tauto

theorem initial3915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 776)) ∨ (meaning t m 2894) := by
  exact rule3915 (meaning t m 770) (meaning t m 776)

theorem rule3932 (p2894 p2895 : Prop) (h : (p2894 ↔ p2895)) : (¬ p2894) ∨ (p2895) := by
  classical
  tauto

theorem initial3932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2894)) ∨ (meaning t m 2895) := by
  have source := ElevenTheory.theory174 t (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule3932 (meaning t m 2894) (meaning t m 2895) source

theorem rule3934 (p782 p788 : Prop) : (¬ p782) ∨ ((p782 ∨ p788)) := by
  classical
  tauto

theorem initial3934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 782)) ∨ (meaning t m 2904) := by
  exact rule3934 (meaning t m 782) (meaning t m 788)

theorem rule3935 (p782 p788 : Prop) : (¬ p788) ∨ ((p782 ∨ p788)) := by
  classical
  tauto

theorem initial3935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 788)) ∨ (meaning t m 2904) := by
  exact rule3935 (meaning t m 782) (meaning t m 788)

theorem rule3952 (p2904 p2905 : Prop) (h : (p2904 ↔ p2905)) : (¬ p2904) ∨ (p2905) := by
  classical
  tauto

theorem initial3952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2904)) ∨ (meaning t m 2905) := by
  have source := ElevenTheory.theory175 t (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule3952 (meaning t m 2904) (meaning t m 2905) source

theorem rule3954 (p2051 p2914 : Prop) (h : ((¬ p2051) ↔ (¬ p2914))) : (p2051) ∨ (¬ p2914) := by
  classical
  tauto

theorem initial3954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2051) ∨ (¬ (meaning t m 2914)) := by
  have source := ElevenTheory.theory176 t (m.theta 4 7)
  exact rule3954 (meaning t m 2051) (meaning t m 2914) source

theorem rule3956 (p794 p800 : Prop) : (¬ p794) ∨ ((p794 ∨ p800)) := by
  classical
  tauto

theorem initial3956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 794)) ∨ (meaning t m 2915) := by
  exact rule3956 (meaning t m 794) (meaning t m 800)

theorem rule3957 (p794 p800 : Prop) : (¬ p800) ∨ ((p794 ∨ p800)) := by
  classical
  tauto

theorem initial3957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 800)) ∨ (meaning t m 2915) := by
  exact rule3957 (meaning t m 794) (meaning t m 800)

theorem rule3974 (p2915 p2916 : Prop) (h : (p2915 ↔ p2916)) : (¬ p2915) ∨ (p2916) := by
  classical
  tauto

theorem initial3974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2915)) ∨ (meaning t m 2916) := by
  have source := ElevenTheory.theory177 t (m.theta 1 4) (m.theta 1 7) (m.theta 4 7)
  exact rule3974 (meaning t m 2915) (meaning t m 2916) source

theorem rule3976 (p2926 p2927 p2928 p2929 p2930 : Prop) : (¬ (p2926 ∧ p2927 ∧ p2928 ∧ p2929 ∧ p2930)) ∨ (p2926) := by
  classical
  tauto

theorem initial3976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2925)) ∨ (meaning t m 2926) := by
  exact rule3976 (meaning t m 2926) (meaning t m 2927) (meaning t m 2928) (meaning t m 2929) (meaning t m 2930)

theorem rule3977 (p2926 p2927 p2928 p2929 p2930 : Prop) : (¬ (p2926 ∧ p2927 ∧ p2928 ∧ p2929 ∧ p2930)) ∨ (p2927) := by
  classical
  tauto

theorem initial3977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2925)) ∨ (meaning t m 2927) := by
  exact rule3977 (meaning t m 2926) (meaning t m 2927) (meaning t m 2928) (meaning t m 2929) (meaning t m 2930)

theorem rule3978 (p2926 p2927 p2928 p2929 p2930 : Prop) : (¬ (p2926 ∧ p2927 ∧ p2928 ∧ p2929 ∧ p2930)) ∨ (p2928) := by
  classical
  tauto

theorem initial3978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2925)) ∨ (meaning t m 2928) := by
  exact rule3978 (meaning t m 2926) (meaning t m 2927) (meaning t m 2928) (meaning t m 2929) (meaning t m 2930)

theorem rule3980 (p2926 p2927 p2928 p2929 p2930 : Prop) : (¬ (p2926 ∧ p2927 ∧ p2928 ∧ p2929 ∧ p2930)) ∨ (p2930) := by
  classical
  tauto

theorem initial3980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2925)) ∨ (meaning t m 2930) := by
  exact rule3980 (meaning t m 2926) (meaning t m 2927) (meaning t m 2928) (meaning t m 2929) (meaning t m 2930)

theorem rule3985 (p2926 p2927 p2928 p2929 p2930 : Prop) : (p2927) ∨ (((¬ p2930) ∨ (¬ p2928) ∨ (¬ p2929) ∨ (¬ p2927) ∨ (¬ p2926))) := by
  classical
  tauto

theorem initial3985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2927) ∨ (meaning t m 2931) := by
  exact rule3985 (meaning t m 2926) (meaning t m 2927) (meaning t m 2928) (meaning t m 2929) (meaning t m 2930)

theorem rule3986 (p2926 p2927 p2928 p2929 p2930 : Prop) : (p2926) ∨ (((¬ p2930) ∨ (¬ p2928) ∨ (¬ p2929) ∨ (¬ p2927) ∨ (¬ p2926))) := by
  classical
  tauto

theorem initial3986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2926) ∨ (meaning t m 2931) := by
  exact rule3986 (meaning t m 2926) (meaning t m 2927) (meaning t m 2928) (meaning t m 2929) (meaning t m 2930)

theorem rule3988 (p2925 p2931 : Prop) (h : (p2925 ↔ (¬ p2931))) : (¬ p2925) ∨ (¬ p2931) := by
  classical
  tauto

theorem initial3988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2925)) ∨ (¬ (meaning t m 2931)) := by
  have source := ElevenTheory.theory178 t (m.theta 1 4) (m.theta 1 7) (m.theta 4 7)
  exact rule3988 (meaning t m 2925) (meaning t m 2931) source

theorem rule3990 (p2922 p2933 p2934 p2935 p2936 : Prop) : (¬ (p2933 ∧ p2934 ∧ p2922 ∧ p2935 ∧ p2936)) ∨ (p2933) := by
  classical
  tauto

theorem initial3990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2932)) ∨ (meaning t m 2933) := by
  exact rule3990 (meaning t m 2922) (meaning t m 2933) (meaning t m 2934) (meaning t m 2935) (meaning t m 2936)

theorem rule3991 (p2922 p2933 p2934 p2935 p2936 : Prop) : (¬ (p2933 ∧ p2934 ∧ p2922 ∧ p2935 ∧ p2936)) ∨ (p2934) := by
  classical
  tauto

theorem initial3991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2932)) ∨ (meaning t m 2934) := by
  exact rule3991 (meaning t m 2922) (meaning t m 2933) (meaning t m 2934) (meaning t m 2935) (meaning t m 2936)

theorem rule3992 (p2922 p2933 p2934 p2935 p2936 : Prop) : (p2922) ∨ (¬ (p2933 ∧ p2934 ∧ p2922 ∧ p2935 ∧ p2936)) := by
  classical
  tauto

theorem initial3992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2922) ∨ (¬ (meaning t m 2932)) := by
  exact rule3992 (meaning t m 2922) (meaning t m 2933) (meaning t m 2934) (meaning t m 2935) (meaning t m 2936)

theorem rule3994 (p2922 p2933 p2934 p2935 p2936 : Prop) : (¬ (p2933 ∧ p2934 ∧ p2922 ∧ p2935 ∧ p2936)) ∨ (p2936) := by
  classical
  tauto

theorem initial3994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2932)) ∨ (meaning t m 2936) := by
  exact rule3994 (meaning t m 2922) (meaning t m 2933) (meaning t m 2934) (meaning t m 2935) (meaning t m 2936)

theorem rule3997 (p2922 p2933 p2934 p2935 p2936 : Prop) : (p2934) ∨ (((¬ p2922) ∨ (¬ p2934) ∨ (¬ p2935) ∨ (¬ p2936) ∨ (¬ p2933))) := by
  classical
  tauto

theorem initial3997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2934) ∨ (meaning t m 2937) := by
  exact rule3997 (meaning t m 2922) (meaning t m 2933) (meaning t m 2934) (meaning t m 2935) (meaning t m 2936)

theorem rule3999 (p2922 p2933 p2934 p2935 p2936 : Prop) : (p2936) ∨ (((¬ p2922) ∨ (¬ p2934) ∨ (¬ p2935) ∨ (¬ p2936) ∨ (¬ p2933))) := by
  classical
  tauto

theorem initial3999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2936) ∨ (meaning t m 2937) := by
  exact rule3999 (meaning t m 2922) (meaning t m 2933) (meaning t m 2934) (meaning t m 2935) (meaning t m 2936)

theorem rule4000 (p2922 p2933 p2934 p2935 p2936 : Prop) : (p2933) ∨ (((¬ p2922) ∨ (¬ p2934) ∨ (¬ p2935) ∨ (¬ p2936) ∨ (¬ p2933))) := by
  classical
  tauto

theorem initial4000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2933) ∨ (meaning t m 2937) := by
  exact rule4000 (meaning t m 2922) (meaning t m 2933) (meaning t m 2934) (meaning t m 2935) (meaning t m 2936)

theorem rule4002 (p2932 p2937 : Prop) (h : (p2932 ↔ (¬ p2937))) : (¬ p2932) ∨ (¬ p2937) := by
  classical
  tauto

theorem initial4002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2932)) ∨ (¬ (meaning t m 2937)) := by
  have source := ElevenTheory.theory179 t (m.theta 1 4) (m.theta 1 7) (m.theta 4 7)
  exact rule4002 (meaning t m 2932) (meaning t m 2937) source

theorem rule4004 (p2052 p2938 : Prop) (h : ((¬ p2052) ↔ (¬ p2938))) : (p2052) ∨ (¬ p2938) := by
  classical
  tauto

theorem initial4004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2052) ∨ (¬ (meaning t m 2938)) := by
  have source := ElevenTheory.theory180 t (m.theta 5 7)
  exact rule4004 (meaning t m 2052) (meaning t m 2938) source

theorem rule4006 (p806 p812 : Prop) : (¬ p806) ∨ ((p806 ∨ p812)) := by
  classical
  tauto

theorem initial4006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 806)) ∨ (meaning t m 2939) := by
  exact rule4006 (meaning t m 806) (meaning t m 812)

theorem rule4007 (p806 p812 : Prop) : (¬ p812) ∨ ((p806 ∨ p812)) := by
  classical
  tauto

theorem initial4007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 812)) ∨ (meaning t m 2939) := by
  exact rule4007 (meaning t m 806) (meaning t m 812)

theorem rule4024 (p2939 p2940 : Prop) (h : (p2939 ↔ p2940)) : (¬ p2939) ∨ (p2940) := by
  classical
  tauto

theorem initial4024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2939)) ∨ (meaning t m 2940) := by
  have source := ElevenTheory.theory181 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 5)
  exact rule4024 (meaning t m 2939) (meaning t m 2940) source

theorem rule4026 (p2950 p2951 p2952 p2953 p2954 : Prop) : (¬ (p2950 ∧ p2951 ∧ p2952 ∧ p2953 ∧ p2954)) ∨ (p2950) := by
  classical
  tauto

theorem initial4026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2949)) ∨ (meaning t m 2950) := by
  exact rule4026 (meaning t m 2950) (meaning t m 2951) (meaning t m 2952) (meaning t m 2953) (meaning t m 2954)

theorem rule4027 (p2950 p2951 p2952 p2953 p2954 : Prop) : (¬ (p2950 ∧ p2951 ∧ p2952 ∧ p2953 ∧ p2954)) ∨ (p2951) := by
  classical
  tauto

theorem initial4027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2949)) ∨ (meaning t m 2951) := by
  exact rule4027 (meaning t m 2950) (meaning t m 2951) (meaning t m 2952) (meaning t m 2953) (meaning t m 2954)

theorem rule4028 (p2950 p2951 p2952 p2953 p2954 : Prop) : (¬ (p2950 ∧ p2951 ∧ p2952 ∧ p2953 ∧ p2954)) ∨ (p2952) := by
  classical
  tauto

theorem initial4028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2949)) ∨ (meaning t m 2952) := by
  exact rule4028 (meaning t m 2950) (meaning t m 2951) (meaning t m 2952) (meaning t m 2953) (meaning t m 2954)

theorem rule4030 (p2950 p2951 p2952 p2953 p2954 : Prop) : (¬ (p2950 ∧ p2951 ∧ p2952 ∧ p2953 ∧ p2954)) ∨ (p2954) := by
  classical
  tauto

theorem initial4030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2949)) ∨ (meaning t m 2954) := by
  exact rule4030 (meaning t m 2950) (meaning t m 2951) (meaning t m 2952) (meaning t m 2953) (meaning t m 2954)

theorem rule4034 (p2950 p2951 p2952 p2953 p2954 : Prop) : (p2950) ∨ (((¬ p2953) ∨ (¬ p2954) ∨ (¬ p2950) ∨ (¬ p2951) ∨ (¬ p2952))) := by
  classical
  tauto

theorem initial4034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2950) ∨ (meaning t m 2955) := by
  exact rule4034 (meaning t m 2950) (meaning t m 2951) (meaning t m 2952) (meaning t m 2953) (meaning t m 2954)

theorem rule4035 (p2950 p2951 p2952 p2953 p2954 : Prop) : (p2951) ∨ (((¬ p2953) ∨ (¬ p2954) ∨ (¬ p2950) ∨ (¬ p2951) ∨ (¬ p2952))) := by
  classical
  tauto

theorem initial4035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2951) ∨ (meaning t m 2955) := by
  exact rule4035 (meaning t m 2950) (meaning t m 2951) (meaning t m 2952) (meaning t m 2953) (meaning t m 2954)

theorem rule4038 (p2949 p2955 : Prop) (h : (p2949 ↔ (¬ p2955))) : (¬ p2949) ∨ (¬ p2955) := by
  classical
  tauto

theorem initial4038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2949)) ∨ (¬ (meaning t m 2955)) := by
  have source := ElevenTheory.theory182 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 5)
  exact rule4038 (meaning t m 2949) (meaning t m 2955) source

theorem rule4040 (p2946 p2957 p2958 p2959 p2960 : Prop) : (¬ (p2957 ∧ p2958 ∧ p2946 ∧ p2959 ∧ p2960)) ∨ (p2957) := by
  classical
  tauto

theorem initial4040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2956)) ∨ (meaning t m 2957) := by
  exact rule4040 (meaning t m 2946) (meaning t m 2957) (meaning t m 2958) (meaning t m 2959) (meaning t m 2960)

theorem rule4041 (p2946 p2957 p2958 p2959 p2960 : Prop) : (¬ (p2957 ∧ p2958 ∧ p2946 ∧ p2959 ∧ p2960)) ∨ (p2958) := by
  classical
  tauto

theorem initial4041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2956)) ∨ (meaning t m 2958) := by
  exact rule4041 (meaning t m 2946) (meaning t m 2957) (meaning t m 2958) (meaning t m 2959) (meaning t m 2960)

theorem rule4042 (p2946 p2957 p2958 p2959 p2960 : Prop) : (p2946) ∨ (¬ (p2957 ∧ p2958 ∧ p2946 ∧ p2959 ∧ p2960)) := by
  classical
  tauto

theorem initial4042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2946) ∨ (¬ (meaning t m 2956)) := by
  exact rule4042 (meaning t m 2946) (meaning t m 2957) (meaning t m 2958) (meaning t m 2959) (meaning t m 2960)

theorem rule4044 (p2946 p2957 p2958 p2959 p2960 : Prop) : (¬ (p2957 ∧ p2958 ∧ p2946 ∧ p2959 ∧ p2960)) ∨ (p2960) := by
  classical
  tauto

theorem initial4044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2956)) ∨ (meaning t m 2960) := by
  exact rule4044 (meaning t m 2946) (meaning t m 2957) (meaning t m 2958) (meaning t m 2959) (meaning t m 2960)

theorem rule4047 (p2946 p2957 p2958 p2959 p2960 : Prop) : (p2959) ∨ (((¬ p2946) ∨ (¬ p2959) ∨ (¬ p2960) ∨ (¬ p2957) ∨ (¬ p2958))) := by
  classical
  tauto

theorem initial4047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2959) ∨ (meaning t m 2961) := by
  exact rule4047 (meaning t m 2946) (meaning t m 2957) (meaning t m 2958) (meaning t m 2959) (meaning t m 2960)

theorem rule4049 (p2946 p2957 p2958 p2959 p2960 : Prop) : (p2957) ∨ (((¬ p2946) ∨ (¬ p2959) ∨ (¬ p2960) ∨ (¬ p2957) ∨ (¬ p2958))) := by
  classical
  tauto

theorem initial4049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2957) ∨ (meaning t m 2961) := by
  exact rule4049 (meaning t m 2946) (meaning t m 2957) (meaning t m 2958) (meaning t m 2959) (meaning t m 2960)

theorem rule4050 (p2946 p2957 p2958 p2959 p2960 : Prop) : (p2958) ∨ (((¬ p2946) ∨ (¬ p2959) ∨ (¬ p2960) ∨ (¬ p2957) ∨ (¬ p2958))) := by
  classical
  tauto

theorem initial4050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2958) ∨ (meaning t m 2961) := by
  exact rule4050 (meaning t m 2946) (meaning t m 2957) (meaning t m 2958) (meaning t m 2959) (meaning t m 2960)

theorem rule4052 (p2956 p2961 : Prop) (h : (p2956 ↔ (¬ p2961))) : (¬ p2956) ∨ (¬ p2961) := by
  classical
  tauto

theorem initial4052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2956)) ∨ (¬ (meaning t m 2961)) := by
  have source := ElevenTheory.theory183 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 5)
  exact rule4052 (meaning t m 2956) (meaning t m 2961) source

theorem rule4054 (p2667 p2958 p2962 p2963 : Prop) (h : (¬ p2667) ∨ (¬ p2958) ∨ (¬ p2962) ∨ (¬ p2963)) : (¬ p2667) ∨ (¬ p2958) ∨ (¬ p2962) ∨ (¬ p2963) := by
  classical
  tauto

theorem initial4054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 2963)) := by
  have source := ElevenTheory.theory184 (m.theta 0 3) (m.theta 0 5) (m.theta 0 6) (m.theta 3 6)
  exact rule4054 (meaning t m 2667) (meaning t m 2958) (meaning t m 2962) (meaning t m 2963) source

theorem rule4055 (p2053 p2964 : Prop) (h : ((¬ p2053) ↔ (¬ p2964))) : (p2053) ∨ (¬ p2964) := by
  classical
  tauto

theorem initial4055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2053) ∨ (¬ (meaning t m 2964)) := by
  have source := ElevenTheory.theory185 t (m.theta 4 9)
  exact rule4055 (meaning t m 2053) (meaning t m 2964) source

theorem rule4057 (p818 p824 : Prop) : (¬ p818) ∨ ((p818 ∨ p824)) := by
  classical
  tauto

theorem initial4057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 818)) ∨ (meaning t m 2965) := by
  exact rule4057 (meaning t m 818) (meaning t m 824)

theorem rule4058 (p818 p824 : Prop) : (¬ p824) ∨ ((p818 ∨ p824)) := by
  classical
  tauto

theorem initial4058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 824)) ∨ (meaning t m 2965) := by
  exact rule4058 (meaning t m 818) (meaning t m 824)

theorem rule4075 (p2965 p2966 : Prop) (h : (p2965 ↔ p2966)) : (¬ p2965) ∨ (p2966) := by
  classical
  tauto

theorem initial4075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2965)) ∨ (meaning t m 2966) := by
  have source := ElevenTheory.theory186 t (m.theta 1 5) (m.theta 1 9) (m.theta 5 9)
  exact rule4075 (meaning t m 2965) (meaning t m 2966) source

theorem rule4077 (p830 p836 : Prop) : (¬ p830) ∨ ((p830 ∨ p836)) := by
  classical
  tauto

theorem initial4077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 830)) ∨ (meaning t m 2975) := by
  exact rule4077 (meaning t m 830) (meaning t m 836)

theorem rule4078 (p830 p836 : Prop) : (¬ p836) ∨ ((p830 ∨ p836)) := by
  classical
  tauto

theorem initial4078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 836)) ∨ (meaning t m 2975) := by
  exact rule4078 (meaning t m 830) (meaning t m 836)

theorem rule4095 (p2975 p2976 : Prop) (h : (p2975 ↔ p2976)) : (¬ p2975) ∨ (p2976) := by
  classical
  tauto

theorem initial4095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2975)) ∨ (meaning t m 2976) := by
  have source := ElevenTheory.theory187 t (m.theta 4 5) (m.theta 4 9) (m.theta 5 9)
  exact rule4095 (meaning t m 2975) (meaning t m 2976) source

theorem rule4097 (p842 p848 : Prop) : (¬ p842) ∨ ((p842 ∨ p848)) := by
  classical
  tauto

theorem initial4097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 842)) ∨ (meaning t m 2985) := by
  exact rule4097 (meaning t m 842) (meaning t m 848)

theorem rule4098 (p842 p848 : Prop) : (¬ p848) ∨ ((p842 ∨ p848)) := by
  classical
  tauto

theorem initial4098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 848)) ∨ (meaning t m 2985) := by
  exact rule4098 (meaning t m 842) (meaning t m 848)

theorem rule4115 (p2985 p2986 : Prop) (h : (p2985 ↔ p2986)) : (¬ p2985) ∨ (p2986) := by
  classical
  tauto

theorem initial4115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2985)) ∨ (meaning t m 2986) := by
  have source := ElevenTheory.theory188 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 5)
  exact rule4115 (meaning t m 2985) (meaning t m 2986) source

theorem rule4117 (p2992 p2995 p2996 : Prop) (h : (¬ p2995) ∨ (¬ p2992) ∨ (¬ p2996)) : (¬ p2992) ∨ (¬ p2995) ∨ (¬ p2996) := by
  classical
  tauto

theorem initial4117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 2996)) := by
  have source := ElevenTheory.theory189 (m.theta 1 3) (m.theta 3 5) (m.theta 3 7)
  exact rule4117 (meaning t m 2992) (meaning t m 2995) (meaning t m 2996) source

theorem rule4118 (p2054 p2997 : Prop) (h : ((¬ p2054) ↔ (¬ p2997))) : (p2054) ∨ (¬ p2997) := by
  classical
  tauto

theorem initial4118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2054) ∨ (¬ (meaning t m 2997)) := by
  have source := ElevenTheory.theory190 t (m.theta 6 7)
  exact rule4118 (meaning t m 2054) (meaning t m 2997) source

theorem rule4120 (p854 p860 : Prop) : (¬ p854) ∨ ((p854 ∨ p860)) := by
  classical
  tauto

theorem initial4120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 854)) ∨ (meaning t m 2998) := by
  exact rule4120 (meaning t m 854) (meaning t m 860)

theorem rule4121 (p854 p860 : Prop) : (¬ p860) ∨ ((p854 ∨ p860)) := by
  classical
  tauto

theorem initial4121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 860)) ∨ (meaning t m 2998) := by
  exact rule4121 (meaning t m 854) (meaning t m 860)

theorem rule4138 (p2998 p2999 : Prop) (h : (p2998 ↔ p2999)) : (¬ p2998) ∨ (p2999) := by
  classical
  tauto

theorem initial4138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2998)) ∨ (meaning t m 2999) := by
  have source := ElevenTheory.theory191 t (m.theta 2 3) (m.theta 2 8) (m.theta 3 8)
  exact rule4138 (meaning t m 2998) (meaning t m 2999) source

theorem rule4140 (p2055 p3008 : Prop) (h : ((¬ p2055) ↔ (¬ p3008))) : (p2055) ∨ (¬ p3008) := by
  classical
  tauto

theorem initial4140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2055) ∨ (¬ (meaning t m 3008)) := by
  have source := ElevenTheory.theory192 t (m.theta 4 6)
  exact rule4140 (meaning t m 2055) (meaning t m 3008) source

theorem rule4142 (p866 p872 : Prop) : (¬ p866) ∨ ((p866 ∨ p872)) := by
  classical
  tauto

theorem initial4142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 866)) ∨ (meaning t m 3009) := by
  exact rule4142 (meaning t m 866) (meaning t m 872)

theorem rule4143 (p866 p872 : Prop) : (¬ p872) ∨ ((p866 ∨ p872)) := by
  classical
  tauto

theorem initial4143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 872)) ∨ (meaning t m 3009) := by
  exact rule4143 (meaning t m 866) (meaning t m 872)

theorem rule4160 (p3009 p3010 : Prop) (h : (p3009 ↔ p3010)) : (¬ p3009) ∨ (p3010) := by
  classical
  tauto

theorem initial4160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3009)) ∨ (meaning t m 3010) := by
  have source := ElevenTheory.theory193 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule4160 (meaning t m 3009) (meaning t m 3010) source

theorem rule4162 (p2651 p2963 p3019 : Prop) (h : (¬ p3019) ∨ (¬ p2963) ∨ (¬ p2651)) : (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3019) := by
  classical
  tauto

theorem initial4162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3019)) := by
  have source := ElevenTheory.theory194 (m.theta 0 3) (m.theta 3 4) (m.theta 3 6)
  exact rule4162 (meaning t m 2651) (meaning t m 2963) (meaning t m 3019) source

theorem rule4163 (p878 p884 : Prop) : (¬ p878) ∨ ((p878 ∨ p884)) := by
  classical
  tauto

theorem initial4163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 878)) ∨ (meaning t m 3020) := by
  exact rule4163 (meaning t m 878) (meaning t m 884)

theorem rule4164 (p878 p884 : Prop) : (¬ p884) ∨ ((p878 ∨ p884)) := by
  classical
  tauto

theorem initial4164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 884)) ∨ (meaning t m 3020) := by
  exact rule4164 (meaning t m 878) (meaning t m 884)

theorem rule4181 (p3020 p3021 : Prop) (h : (p3020 ↔ p3021)) : (¬ p3020) ∨ (p3021) := by
  classical
  tauto

theorem initial4181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3020)) ∨ (meaning t m 3021) := by
  have source := ElevenTheory.theory195 t (m.theta 1 3) (m.theta 1 7) (m.theta 3 7)
  exact rule4181 (meaning t m 3020) (meaning t m 3021) source

theorem rule4183 (p2996 p3031 p3032 p3033 p3034 : Prop) : (¬ (p3031 ∧ p3032 ∧ p2996 ∧ p3033 ∧ p3034)) ∨ (p3031) := by
  classical
  tauto

theorem initial4183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3030)) ∨ (meaning t m 3031) := by
  exact rule4183 (meaning t m 2996) (meaning t m 3031) (meaning t m 3032) (meaning t m 3033) (meaning t m 3034)

theorem rule4184 (p2996 p3031 p3032 p3033 p3034 : Prop) : (¬ (p3031 ∧ p3032 ∧ p2996 ∧ p3033 ∧ p3034)) ∨ (p3032) := by
  classical
  tauto

theorem initial4184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3030)) ∨ (meaning t m 3032) := by
  exact rule4184 (meaning t m 2996) (meaning t m 3031) (meaning t m 3032) (meaning t m 3033) (meaning t m 3034)

theorem rule4185 (p2996 p3031 p3032 p3033 p3034 : Prop) : (p2996) ∨ (¬ (p3031 ∧ p3032 ∧ p2996 ∧ p3033 ∧ p3034)) := by
  classical
  tauto

theorem initial4185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2996) ∨ (¬ (meaning t m 3030)) := by
  exact rule4185 (meaning t m 2996) (meaning t m 3031) (meaning t m 3032) (meaning t m 3033) (meaning t m 3034)

theorem rule4187 (p2996 p3031 p3032 p3033 p3034 : Prop) : (¬ (p3031 ∧ p3032 ∧ p2996 ∧ p3033 ∧ p3034)) ∨ (p3034) := by
  classical
  tauto

theorem initial4187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3030)) ∨ (meaning t m 3034) := by
  exact rule4187 (meaning t m 2996) (meaning t m 3031) (meaning t m 3032) (meaning t m 3033) (meaning t m 3034)

theorem rule4189 (p2996 p3031 p3032 p3033 p3034 : Prop) : (p3034) ∨ (((¬ p3034) ∨ (¬ p3033) ∨ (¬ p2996) ∨ (¬ p3031) ∨ (¬ p3032))) := by
  classical
  tauto

theorem initial4189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3034) ∨ (meaning t m 3035) := by
  exact rule4189 (meaning t m 2996) (meaning t m 3031) (meaning t m 3032) (meaning t m 3033) (meaning t m 3034)

theorem rule4192 (p2996 p3031 p3032 p3033 p3034 : Prop) : (p3031) ∨ (((¬ p3034) ∨ (¬ p3033) ∨ (¬ p2996) ∨ (¬ p3031) ∨ (¬ p3032))) := by
  classical
  tauto

theorem initial4192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3031) ∨ (meaning t m 3035) := by
  exact rule4192 (meaning t m 2996) (meaning t m 3031) (meaning t m 3032) (meaning t m 3033) (meaning t m 3034)

theorem rule4193 (p2996 p3031 p3032 p3033 p3034 : Prop) : (p3032) ∨ (((¬ p3034) ∨ (¬ p3033) ∨ (¬ p2996) ∨ (¬ p3031) ∨ (¬ p3032))) := by
  classical
  tauto

theorem initial4193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3032) ∨ (meaning t m 3035) := by
  exact rule4193 (meaning t m 2996) (meaning t m 3031) (meaning t m 3032) (meaning t m 3033) (meaning t m 3034)

theorem rule4195 (p3030 p3035 : Prop) (h : (p3030 ↔ (¬ p3035))) : (¬ p3030) ∨ (¬ p3035) := by
  classical
  tauto

theorem initial4195 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3030)) ∨ (¬ (meaning t m 3035)) := by
  have source := ElevenTheory.theory196 t (m.theta 1 3) (m.theta 1 7) (m.theta 3 7)
  exact rule4195 (meaning t m 3030) (meaning t m 3035) source

theorem rule4197 (p3027 p3037 p3038 p3039 p3040 : Prop) : (¬ (p3037 ∧ p3038 ∧ p3027 ∧ p3039 ∧ p3040)) ∨ (p3037) := by
  classical
  tauto

theorem initial4197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3036)) ∨ (meaning t m 3037) := by
  exact rule4197 (meaning t m 3027) (meaning t m 3037) (meaning t m 3038) (meaning t m 3039) (meaning t m 3040)

theorem rule4198 (p3027 p3037 p3038 p3039 p3040 : Prop) : (¬ (p3037 ∧ p3038 ∧ p3027 ∧ p3039 ∧ p3040)) ∨ (p3038) := by
  classical
  tauto

theorem initial4198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3036)) ∨ (meaning t m 3038) := by
  exact rule4198 (meaning t m 3027) (meaning t m 3037) (meaning t m 3038) (meaning t m 3039) (meaning t m 3040)

theorem rule4199 (p3027 p3037 p3038 p3039 p3040 : Prop) : (p3027) ∨ (¬ (p3037 ∧ p3038 ∧ p3027 ∧ p3039 ∧ p3040)) := by
  classical
  tauto

theorem initial4199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3027) ∨ (¬ (meaning t m 3036)) := by
  exact rule4199 (meaning t m 3027) (meaning t m 3037) (meaning t m 3038) (meaning t m 3039) (meaning t m 3040)

theorem rule4200 (p3027 p3037 p3038 p3039 p3040 : Prop) : (¬ (p3037 ∧ p3038 ∧ p3027 ∧ p3039 ∧ p3040)) ∨ (p3039) := by
  classical
  tauto

theorem initial4200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3036)) ∨ (meaning t m 3039) := by
  exact rule4200 (meaning t m 3027) (meaning t m 3037) (meaning t m 3038) (meaning t m 3039) (meaning t m 3040)

theorem rule4201 (p3027 p3037 p3038 p3039 p3040 : Prop) : (¬ (p3037 ∧ p3038 ∧ p3027 ∧ p3039 ∧ p3040)) ∨ (p3040) := by
  classical
  tauto

theorem initial4201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3036)) ∨ (meaning t m 3040) := by
  exact rule4201 (meaning t m 3027) (meaning t m 3037) (meaning t m 3038) (meaning t m 3039) (meaning t m 3040)

theorem rule4203 (p3027 p3037 p3038 p3039 p3040 : Prop) : (p3037) ∨ (((¬ p3037) ∨ (¬ p3038) ∨ (¬ p3040) ∨ (¬ p3027) ∨ (¬ p3039))) := by
  classical
  tauto

theorem initial4203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3037) ∨ (meaning t m 3041) := by
  exact rule4203 (meaning t m 3027) (meaning t m 3037) (meaning t m 3038) (meaning t m 3039) (meaning t m 3040)

theorem rule4204 (p3027 p3037 p3038 p3039 p3040 : Prop) : (p3038) ∨ (((¬ p3037) ∨ (¬ p3038) ∨ (¬ p3040) ∨ (¬ p3027) ∨ (¬ p3039))) := by
  classical
  tauto

theorem initial4204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3038) ∨ (meaning t m 3041) := by
  exact rule4204 (meaning t m 3027) (meaning t m 3037) (meaning t m 3038) (meaning t m 3039) (meaning t m 3040)

theorem rule4205 (p3027 p3037 p3038 p3039 p3040 : Prop) : (p3040) ∨ (((¬ p3037) ∨ (¬ p3038) ∨ (¬ p3040) ∨ (¬ p3027) ∨ (¬ p3039))) := by
  classical
  tauto

theorem initial4205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3040) ∨ (meaning t m 3041) := by
  exact rule4205 (meaning t m 3027) (meaning t m 3037) (meaning t m 3038) (meaning t m 3039) (meaning t m 3040)

theorem rule4207 (p3027 p3037 p3038 p3039 p3040 : Prop) : (p3039) ∨ (((¬ p3037) ∨ (¬ p3038) ∨ (¬ p3040) ∨ (¬ p3027) ∨ (¬ p3039))) := by
  classical
  tauto

theorem initial4207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3039) ∨ (meaning t m 3041) := by
  exact rule4207 (meaning t m 3027) (meaning t m 3037) (meaning t m 3038) (meaning t m 3039) (meaning t m 3040)

theorem rule4209 (p3036 p3041 : Prop) (h : (p3036 ↔ (¬ p3041))) : (¬ p3036) ∨ (¬ p3041) := by
  classical
  tauto

theorem initial4209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3036)) ∨ (¬ (meaning t m 3041)) := by
  have source := ElevenTheory.theory197 t (m.theta 1 3) (m.theta 1 7) (m.theta 3 7)
  exact rule4209 (meaning t m 3036) (meaning t m 3041) source

theorem rule4211 (p2056 p3042 : Prop) (h : ((¬ p2056) ↔ (¬ p3042))) : (p2056) ∨ (¬ p3042) := by
  classical
  tauto

theorem initial4211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2056) ∨ (¬ (meaning t m 3042)) := by
  have source := ElevenTheory.theory198 t (m.theta 3 8)
  exact rule4211 (meaning t m 2056) (meaning t m 3042) source

theorem rule4213 (p2057 p3043 : Prop) (h : ((¬ p2057) ↔ (¬ p3043))) : (p2057) ∨ (¬ p3043) := by
  classical
  tauto

theorem initial4213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2057) ∨ (¬ (meaning t m 3043)) := by
  have source := ElevenTheory.theory199 t (m.theta 5 9)
  exact rule4213 (meaning t m 2057) (meaning t m 3043) source

theorem rule4215 (p890 p896 : Prop) : (¬ p890) ∨ ((p890 ∨ p896)) := by
  classical
  tauto

theorem initial4215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 890)) ∨ (meaning t m 3044) := by
  exact rule4215 (meaning t m 890) (meaning t m 896)

theorem rule4216 (p890 p896 : Prop) : (¬ p896) ∨ ((p890 ∨ p896)) := by
  classical
  tauto

theorem initial4216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 896)) ∨ (meaning t m 3044) := by
  exact rule4216 (meaning t m 890) (meaning t m 896)

theorem rule4233 (p3044 p3045 : Prop) (h : (p3044 ↔ p3045)) : (¬ p3044) ∨ (p3045) := by
  classical
  tauto

theorem initial4233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3044)) ∨ (meaning t m 3045) := by
  have source := ElevenTheory.theory200 t (m.theta 0 5) (m.theta 0 7) (m.theta 5 7)
  exact rule4233 (meaning t m 3044) (meaning t m 3045) source

theorem rule4235 (p2132 p3054 p3055 : Prop) (h : (¬ p2132) ∨ (¬ p3054) ∨ (¬ p3055)) : (¬ p2132) ∨ (¬ p3054) ∨ (¬ p3055) := by
  classical
  tauto

theorem initial4235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3055)) := by
  have source := ElevenTheory.theory201 (m.theta 0 2) (m.theta 2 4) (m.theta 2 5)
  exact rule4235 (meaning t m 2132) (meaning t m 3054) (meaning t m 3055) source

theorem rule4236 (p902 p908 : Prop) : (¬ p902) ∨ ((p902 ∨ p908)) := by
  classical
  tauto

theorem initial4236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 902)) ∨ (meaning t m 3056) := by
  exact rule4236 (meaning t m 902) (meaning t m 908)

theorem rule4237 (p902 p908 : Prop) : (¬ p908) ∨ ((p902 ∨ p908)) := by
  classical
  tauto

theorem initial4237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 908)) ∨ (meaning t m 3056) := by
  exact rule4237 (meaning t m 902) (meaning t m 908)

theorem rule4254 (p3056 p3057 : Prop) (h : (p3056 ↔ p3057)) : (¬ p3056) ∨ (p3057) := by
  classical
  tauto

theorem initial4254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3056)) ∨ (meaning t m 3057) := by
  have source := ElevenTheory.theory202 t (m.theta 1 6) (m.theta 1 8) (m.theta 6 8)
  exact rule4254 (meaning t m 3056) (meaning t m 3057) source

theorem rule4256 (p914 p920 : Prop) : (¬ p914) ∨ ((p914 ∨ p920)) := by
  classical
  tauto

theorem initial4256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 914)) ∨ (meaning t m 3066) := by
  exact rule4256 (meaning t m 914) (meaning t m 920)

theorem rule4257 (p914 p920 : Prop) : (¬ p920) ∨ ((p914 ∨ p920)) := by
  classical
  tauto

theorem initial4257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 920)) ∨ (meaning t m 3066) := by
  exact rule4257 (meaning t m 914) (meaning t m 920)

theorem rule4274 (p3066 p3067 : Prop) (h : (p3066 ↔ p3067)) : (¬ p3066) ∨ (p3067) := by
  classical
  tauto

theorem initial4274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3066)) ∨ (meaning t m 3067) := by
  have source := ElevenTheory.theory203 t (m.theta 1 8) (m.theta 1 9) (m.theta 8 9)
  exact rule4274 (meaning t m 3066) (meaning t m 3067) source

theorem rule4276 (p926 p932 : Prop) : (¬ p926) ∨ ((p926 ∨ p932)) := by
  classical
  tauto

theorem initial4276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 926)) ∨ (meaning t m 3076) := by
  exact rule4276 (meaning t m 926) (meaning t m 932)

theorem rule4277 (p926 p932 : Prop) : (¬ p932) ∨ ((p926 ∨ p932)) := by
  classical
  tauto

theorem initial4277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 932)) ∨ (meaning t m 3076) := by
  exact rule4277 (meaning t m 926) (meaning t m 932)

theorem rule4294 (p3076 p3077 : Prop) (h : (p3076 ↔ p3077)) : (¬ p3076) ∨ (p3077) := by
  classical
  tauto

theorem initial4294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3076)) ∨ (meaning t m 3077) := by
  have source := ElevenTheory.theory204 t (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule4294 (meaning t m 3076) (meaning t m 3077) source

theorem rule4296 (p938 p944 : Prop) : (¬ p938) ∨ ((p938 ∨ p944)) := by
  classical
  tauto

theorem initial4296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 938)) ∨ (meaning t m 3086) := by
  exact rule4296 (meaning t m 938) (meaning t m 944)

theorem rule4297 (p938 p944 : Prop) : (¬ p944) ∨ ((p938 ∨ p944)) := by
  classical
  tauto

theorem initial4297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 944)) ∨ (meaning t m 3086) := by
  exact rule4297 (meaning t m 938) (meaning t m 944)

theorem rule4314 (p3086 p3087 : Prop) (h : (p3086 ↔ p3087)) : (¬ p3086) ∨ (p3087) := by
  classical
  tauto

theorem initial4314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3086)) ∨ (meaning t m 3087) := by
  have source := ElevenTheory.theory205 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 6)
  exact rule4314 (meaning t m 3086) (meaning t m 3087) source

theorem rule4316 (p2553 p3096 p3097 : Prop) (h : (¬ p3096) ∨ (¬ p3097) ∨ (¬ p2553)) : (¬ p2553) ∨ (¬ p3096) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial4316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory206 (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule4316 (meaning t m 2553) (meaning t m 3096) (meaning t m 3097) source

end SunPrize.SMT
