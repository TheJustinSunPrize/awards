import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule7572 (p2528 p3358 p4695 p4696 p4697 : Prop) : (p3358) ∨ (¬ (p4695 ∧ p3358 ∧ p2528 ∧ p4696 ∧ p4697)) := by
  classical
  tauto

theorem initial7572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3358) ∨ (¬ (meaning t m 4694)) := by
  exact rule7572 (meaning t m 2528) (meaning t m 3358) (meaning t m 4695) (meaning t m 4696) (meaning t m 4697)

theorem rule7573 (p2528 p3358 p4695 p4696 p4697 : Prop) : (p2528) ∨ (¬ (p4695 ∧ p3358 ∧ p2528 ∧ p4696 ∧ p4697)) := by
  classical
  tauto

theorem initial7573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2528) ∨ (¬ (meaning t m 4694)) := by
  exact rule7573 (meaning t m 2528) (meaning t m 3358) (meaning t m 4695) (meaning t m 4696) (meaning t m 4697)

theorem rule7575 (p2528 p3358 p4695 p4696 p4697 : Prop) : (¬ (p4695 ∧ p3358 ∧ p2528 ∧ p4696 ∧ p4697)) ∨ (p4697) := by
  classical
  tauto

theorem initial7575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4694)) ∨ (meaning t m 4697) := by
  exact rule7575 (meaning t m 2528) (meaning t m 3358) (meaning t m 4695) (meaning t m 4696) (meaning t m 4697)

theorem rule7579 (p4692 p4694 : Prop) : (¬ (p4692 ∨ p4694)) ∨ (p4692) ∨ (p4694) := by
  classical
  tauto

theorem initial7579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4691)) ∨ (meaning t m 4692) ∨ (meaning t m 4694) := by
  exact rule7579 (meaning t m 4692) (meaning t m 4694)

theorem rule7580 (p2522 p4691 : Prop) (h : (p2522 ↔ p4691)) : (¬ p2522) ∨ (p4691) := by
  classical
  tauto

theorem initial7580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2522)) ∨ (meaning t m 4691) := by
  have source := ElevenTheory.theory1140 t (m.theta 4 8) (m.theta 4 9) (m.theta 8 9)
  exact rule7580 (meaning t m 2522) (meaning t m 4691) source

theorem rule7582 (p2440 p3879 p4700 p4701 p4702 : Prop) : (¬ (p4700 ∧ p3879 ∧ p2440 ∧ p4701 ∧ p4702)) ∨ (p4700) := by
  classical
  tauto

theorem initial7582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4699)) ∨ (meaning t m 4700) := by
  exact rule7582 (meaning t m 2440) (meaning t m 3879) (meaning t m 4700) (meaning t m 4701) (meaning t m 4702)

theorem rule7583 (p2440 p3879 p4700 p4701 p4702 : Prop) : (p3879) ∨ (¬ (p4700 ∧ p3879 ∧ p2440 ∧ p4701 ∧ p4702)) := by
  classical
  tauto

theorem initial7583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3879) ∨ (¬ (meaning t m 4699)) := by
  exact rule7583 (meaning t m 2440) (meaning t m 3879) (meaning t m 4700) (meaning t m 4701) (meaning t m 4702)

theorem rule7584 (p2440 p3879 p4700 p4701 p4702 : Prop) : (p2440) ∨ (¬ (p4700 ∧ p3879 ∧ p2440 ∧ p4701 ∧ p4702)) := by
  classical
  tauto

theorem initial7584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2440) ∨ (¬ (meaning t m 4699)) := by
  exact rule7584 (meaning t m 2440) (meaning t m 3879) (meaning t m 4700) (meaning t m 4701) (meaning t m 4702)

theorem rule7585 (p2440 p3879 p4700 p4701 p4702 : Prop) : (¬ (p4700 ∧ p3879 ∧ p2440 ∧ p4701 ∧ p4702)) ∨ (p4701) := by
  classical
  tauto

theorem initial7585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4699)) ∨ (meaning t m 4701) := by
  exact rule7585 (meaning t m 2440) (meaning t m 3879) (meaning t m 4700) (meaning t m 4701) (meaning t m 4702)

theorem rule7586 (p2440 p3879 p4700 p4701 p4702 : Prop) : (¬ (p4700 ∧ p3879 ∧ p2440 ∧ p4701 ∧ p4702)) ∨ (p4702) := by
  classical
  tauto

theorem initial7586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4699)) ∨ (meaning t m 4702) := by
  exact rule7586 (meaning t m 2440) (meaning t m 3879) (meaning t m 4700) (meaning t m 4701) (meaning t m 4702)

theorem rule7588 (p2542 p3413 p4241 p4704 p4705 : Prop) : (p4241) ∨ (¬ (p4241 ∧ p3413 ∧ p2542 ∧ p4704 ∧ p4705)) := by
  classical
  tauto

theorem initial7588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4241) ∨ (¬ (meaning t m 4703)) := by
  exact rule7588 (meaning t m 2542) (meaning t m 3413) (meaning t m 4241) (meaning t m 4704) (meaning t m 4705)

theorem rule7589 (p2542 p3413 p4241 p4704 p4705 : Prop) : (p3413) ∨ (¬ (p4241 ∧ p3413 ∧ p2542 ∧ p4704 ∧ p4705)) := by
  classical
  tauto

theorem initial7589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3413) ∨ (¬ (meaning t m 4703)) := by
  exact rule7589 (meaning t m 2542) (meaning t m 3413) (meaning t m 4241) (meaning t m 4704) (meaning t m 4705)

theorem rule7590 (p2542 p3413 p4241 p4704 p4705 : Prop) : (p2542) ∨ (¬ (p4241 ∧ p3413 ∧ p2542 ∧ p4704 ∧ p4705)) := by
  classical
  tauto

theorem initial7590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2542) ∨ (¬ (meaning t m 4703)) := by
  exact rule7590 (meaning t m 2542) (meaning t m 3413) (meaning t m 4241) (meaning t m 4704) (meaning t m 4705)

theorem rule7591 (p2542 p3413 p4241 p4704 p4705 : Prop) : (¬ (p4241 ∧ p3413 ∧ p2542 ∧ p4704 ∧ p4705)) ∨ (p4704) := by
  classical
  tauto

theorem initial7591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4703)) ∨ (meaning t m 4704) := by
  exact rule7591 (meaning t m 2542) (meaning t m 3413) (meaning t m 4241) (meaning t m 4704) (meaning t m 4705)

theorem rule7592 (p2542 p3413 p4241 p4704 p4705 : Prop) : (¬ (p4241 ∧ p3413 ∧ p2542 ∧ p4704 ∧ p4705)) ∨ (p4705) := by
  classical
  tauto

theorem initial7592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4703)) ∨ (meaning t m 4705) := by
  exact rule7592 (meaning t m 2542) (meaning t m 3413) (meaning t m 4241) (meaning t m 4704) (meaning t m 4705)

theorem rule7596 (p4699 p4703 : Prop) : (¬ (p4699 ∨ p4703)) ∨ (p4699) ∨ (p4703) := by
  classical
  tauto

theorem initial7596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4698)) ∨ (meaning t m 4699) ∨ (meaning t m 4703) := by
  exact rule7596 (meaning t m 4699) (meaning t m 4703)

theorem rule7597 (p2536 p4698 : Prop) (h : (p2536 ↔ p4698)) : (¬ p2536) ∨ (p4698) := by
  classical
  tauto

theorem initial7597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2536)) ∨ (meaning t m 4698) := by
  have source := ElevenTheory.theory1141 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule7597 (meaning t m 2536) (meaning t m 4698) source

theorem rule7599 (p2588 p3581 p3921 p4276 p4708 : Prop) : (p3581) ∨ (¬ (p3581 ∧ p3921 ∧ p2588 ∧ p4708 ∧ p4276)) := by
  classical
  tauto

theorem initial7599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3581) ∨ (¬ (meaning t m 4707)) := by
  exact rule7599 (meaning t m 2588) (meaning t m 3581) (meaning t m 3921) (meaning t m 4276) (meaning t m 4708)

theorem rule7600 (p2588 p3581 p3921 p4276 p4708 : Prop) : (p3921) ∨ (¬ (p3581 ∧ p3921 ∧ p2588 ∧ p4708 ∧ p4276)) := by
  classical
  tauto

theorem initial7600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3921) ∨ (¬ (meaning t m 4707)) := by
  exact rule7600 (meaning t m 2588) (meaning t m 3581) (meaning t m 3921) (meaning t m 4276) (meaning t m 4708)

theorem rule7601 (p2588 p3581 p3921 p4276 p4708 : Prop) : (p2588) ∨ (¬ (p3581 ∧ p3921 ∧ p2588 ∧ p4708 ∧ p4276)) := by
  classical
  tauto

theorem initial7601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2588) ∨ (¬ (meaning t m 4707)) := by
  exact rule7601 (meaning t m 2588) (meaning t m 3581) (meaning t m 3921) (meaning t m 4276) (meaning t m 4708)

theorem rule7602 (p2588 p3581 p3921 p4276 p4708 : Prop) : (¬ (p3581 ∧ p3921 ∧ p2588 ∧ p4708 ∧ p4276)) ∨ (p4708) := by
  classical
  tauto

theorem initial7602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4707)) ∨ (meaning t m 4708) := by
  exact rule7602 (meaning t m 2588) (meaning t m 3581) (meaning t m 3921) (meaning t m 4276) (meaning t m 4708)

theorem rule7603 (p2588 p3581 p3921 p4276 p4708 : Prop) : (p4276) ∨ (¬ (p3581 ∧ p3921 ∧ p2588 ∧ p4708 ∧ p4276)) := by
  classical
  tauto

theorem initial7603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4276) ∨ (¬ (meaning t m 4707)) := by
  exact rule7603 (meaning t m 2588) (meaning t m 3581) (meaning t m 3921) (meaning t m 4276) (meaning t m 4708)

theorem rule7605 (p2553 p3920 p4710 p4711 p4712 : Prop) : (¬ (p4710 ∧ p3920 ∧ p2553 ∧ p4711 ∧ p4712)) ∨ (p4710) := by
  classical
  tauto

theorem initial7605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4709)) ∨ (meaning t m 4710) := by
  exact rule7605 (meaning t m 2553) (meaning t m 3920) (meaning t m 4710) (meaning t m 4711) (meaning t m 4712)

theorem rule7606 (p2553 p3920 p4710 p4711 p4712 : Prop) : (p3920) ∨ (¬ (p4710 ∧ p3920 ∧ p2553 ∧ p4711 ∧ p4712)) := by
  classical
  tauto

theorem initial7606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3920) ∨ (¬ (meaning t m 4709)) := by
  exact rule7606 (meaning t m 2553) (meaning t m 3920) (meaning t m 4710) (meaning t m 4711) (meaning t m 4712)

theorem rule7607 (p2553 p3920 p4710 p4711 p4712 : Prop) : (p2553) ∨ (¬ (p4710 ∧ p3920 ∧ p2553 ∧ p4711 ∧ p4712)) := by
  classical
  tauto

theorem initial7607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2553) ∨ (¬ (meaning t m 4709)) := by
  exact rule7607 (meaning t m 2553) (meaning t m 3920) (meaning t m 4710) (meaning t m 4711) (meaning t m 4712)

theorem rule7608 (p2553 p3920 p4710 p4711 p4712 : Prop) : (¬ (p4710 ∧ p3920 ∧ p2553 ∧ p4711 ∧ p4712)) ∨ (p4711) := by
  classical
  tauto

theorem initial7608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4709)) ∨ (meaning t m 4711) := by
  exact rule7608 (meaning t m 2553) (meaning t m 3920) (meaning t m 4710) (meaning t m 4711) (meaning t m 4712)

theorem rule7609 (p2553 p3920 p4710 p4711 p4712 : Prop) : (¬ (p4710 ∧ p3920 ∧ p2553 ∧ p4711 ∧ p4712)) ∨ (p4712) := by
  classical
  tauto

theorem initial7609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4709)) ∨ (meaning t m 4712) := by
  exact rule7609 (meaning t m 2553) (meaning t m 3920) (meaning t m 4710) (meaning t m 4711) (meaning t m 4712)

theorem rule7613 (p4707 p4709 : Prop) : (¬ (p4707 ∨ p4709)) ∨ (p4707) ∨ (p4709) := by
  classical
  tauto

theorem initial7613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4706)) ∨ (meaning t m 4707) ∨ (meaning t m 4709) := by
  exact rule7613 (meaning t m 4707) (meaning t m 4709)

theorem rule7614 (p2547 p4706 : Prop) (h : (p2547 ↔ p4706)) : (¬ p2547) ∨ (p4706) := by
  classical
  tauto

theorem initial7614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2547)) ∨ (meaning t m 4706) := by
  have source := ElevenTheory.theory1142 t (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule7614 (meaning t m 2547) (meaning t m 4706) source

theorem rule7616 (p2590 p3096 p3958 p4110 p4715 : Prop) : (p2590) ∨ (¬ (p2590 ∧ p3096 ∧ p4110 ∧ p4715 ∧ p3958)) := by
  classical
  tauto

theorem initial7616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2590) ∨ (¬ (meaning t m 4714)) := by
  exact rule7616 (meaning t m 2590) (meaning t m 3096) (meaning t m 3958) (meaning t m 4110) (meaning t m 4715)

theorem rule7617 (p2590 p3096 p3958 p4110 p4715 : Prop) : (p3096) ∨ (¬ (p2590 ∧ p3096 ∧ p4110 ∧ p4715 ∧ p3958)) := by
  classical
  tauto

theorem initial7617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3096) ∨ (¬ (meaning t m 4714)) := by
  exact rule7617 (meaning t m 2590) (meaning t m 3096) (meaning t m 3958) (meaning t m 4110) (meaning t m 4715)

theorem rule7618 (p2590 p3096 p3958 p4110 p4715 : Prop) : (p4110) ∨ (¬ (p2590 ∧ p3096 ∧ p4110 ∧ p4715 ∧ p3958)) := by
  classical
  tauto

theorem initial7618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4110) ∨ (¬ (meaning t m 4714)) := by
  exact rule7618 (meaning t m 2590) (meaning t m 3096) (meaning t m 3958) (meaning t m 4110) (meaning t m 4715)

theorem rule7619 (p2590 p3096 p3958 p4110 p4715 : Prop) : (¬ (p2590 ∧ p3096 ∧ p4110 ∧ p4715 ∧ p3958)) ∨ (p4715) := by
  classical
  tauto

theorem initial7619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4714)) ∨ (meaning t m 4715) := by
  exact rule7619 (meaning t m 2590) (meaning t m 3096) (meaning t m 3958) (meaning t m 4110) (meaning t m 4715)

theorem rule7620 (p2590 p3096 p3958 p4110 p4715 : Prop) : (p3958) ∨ (¬ (p2590 ∧ p3096 ∧ p4110 ∧ p4715 ∧ p3958)) := by
  classical
  tauto

theorem initial7620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3958) ∨ (¬ (meaning t m 4714)) := by
  exact rule7620 (meaning t m 2590) (meaning t m 3096) (meaning t m 3958) (meaning t m 4110) (meaning t m 4715)

theorem rule7622 (p2563 p3660 p4203 p4717 p4718 : Prop) : (p4203) ∨ (¬ (p4203 ∧ p3660 ∧ p2563 ∧ p4717 ∧ p4718)) := by
  classical
  tauto

theorem initial7622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4203) ∨ (¬ (meaning t m 4716)) := by
  exact rule7622 (meaning t m 2563) (meaning t m 3660) (meaning t m 4203) (meaning t m 4717) (meaning t m 4718)

theorem rule7623 (p2563 p3660 p4203 p4717 p4718 : Prop) : (p3660) ∨ (¬ (p4203 ∧ p3660 ∧ p2563 ∧ p4717 ∧ p4718)) := by
  classical
  tauto

theorem initial7623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3660) ∨ (¬ (meaning t m 4716)) := by
  exact rule7623 (meaning t m 2563) (meaning t m 3660) (meaning t m 4203) (meaning t m 4717) (meaning t m 4718)

theorem rule7624 (p2563 p3660 p4203 p4717 p4718 : Prop) : (p2563) ∨ (¬ (p4203 ∧ p3660 ∧ p2563 ∧ p4717 ∧ p4718)) := by
  classical
  tauto

theorem initial7624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2563) ∨ (¬ (meaning t m 4716)) := by
  exact rule7624 (meaning t m 2563) (meaning t m 3660) (meaning t m 4203) (meaning t m 4717) (meaning t m 4718)

theorem rule7625 (p2563 p3660 p4203 p4717 p4718 : Prop) : (¬ (p4203 ∧ p3660 ∧ p2563 ∧ p4717 ∧ p4718)) ∨ (p4717) := by
  classical
  tauto

theorem initial7625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4716)) ∨ (meaning t m 4717) := by
  exact rule7625 (meaning t m 2563) (meaning t m 3660) (meaning t m 4203) (meaning t m 4717) (meaning t m 4718)

theorem rule7626 (p2563 p3660 p4203 p4717 p4718 : Prop) : (¬ (p4203 ∧ p3660 ∧ p2563 ∧ p4717 ∧ p4718)) ∨ (p4718) := by
  classical
  tauto

theorem initial7626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4716)) ∨ (meaning t m 4718) := by
  exact rule7626 (meaning t m 2563) (meaning t m 3660) (meaning t m 4203) (meaning t m 4717) (meaning t m 4718)

theorem rule7630 (p4714 p4716 : Prop) : (¬ (p4714 ∨ p4716)) ∨ (p4714) ∨ (p4716) := by
  classical
  tauto

theorem initial7630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4713)) ∨ (meaning t m 4714) ∨ (meaning t m 4716) := by
  exact rule7630 (meaning t m 4714) (meaning t m 4716)

theorem rule7631 (p2557 p4713 : Prop) (h : (p2557 ↔ p4713)) : (¬ p2557) ∨ (p4713) := by
  classical
  tauto

theorem initial7631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2557)) ∨ (meaning t m 4713) := by
  have source := ElevenTheory.theory1143 t (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule7631 (meaning t m 2557) (meaning t m 4713) source

theorem rule7633 (p2027 p2307 p2584 p2588 p2589 p4717 : Prop) (h : p2027 ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p4717) ∨ (¬ p2589) ∨ (¬ p2584)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2589) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial7633 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory1144 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule7633 (meaning t m 2027) (meaning t m 2307) (meaning t m 2584) (meaning t m 2588) (meaning t m 2589) (meaning t m 4717) source

theorem rule7636 (p2576 p2583 : Prop) : (p2576) ∨ (p2583) ∨ (¬ (p2576 ∨ p2583)) := by
  classical
  tauto

theorem initial7636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2576) ∨ (meaning t m 2583) ∨ (¬ (meaning t m 4719)) := by
  exact rule7636 (meaning t m 2576) (meaning t m 2583)

theorem rule7637 (p2567 p4719 : Prop) (h : (p2567 ↔ p4719)) : (¬ p2567) ∨ (p4719) := by
  classical
  tauto

theorem initial7637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2567)) ∨ (meaning t m 4719) := by
  have source := ElevenTheory.theory1145 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6)
  exact rule7637 (meaning t m 2567) (meaning t m 4719) source

theorem rule7660 (p2307 p2313 : Prop) (h : (¬ p2313) ∨ (¬ p2307)) : (¬ p2307) ∨ (¬ p2313) := by
  classical
  tauto

theorem initial7660 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2313)) := by
  have source := ElevenTheory.theory1148 (m.theta 0 6) (m.theta 6 7)
  exact rule7660 (meaning t m 2307) (meaning t m 2313) source

theorem rule7661 (p2027 p2295 p2313 p2386 p2440 p3019 p4717 : Prop) (h : p2027 ∨ (¬ p3019) ∨ (¬ p2295) ∨ (¬ p2386) ∨ (¬ p4717) ∨ (¬ p2313) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2440) ∨ (¬ p3019) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial7661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory1149 t (m.theta 0 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule7661 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2386) (meaning t m 2440) (meaning t m 3019) (meaning t m 4717) source

theorem rule7662 (p3055 p3759 p3905 p4419 p4727 : Prop) : (p3905) ∨ (¬ (p3905 ∧ p3759 ∧ p3055 ∧ p4419 ∧ p4727)) := by
  classical
  tauto

theorem initial7662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3905) ∨ (¬ (meaning t m 4726)) := by
  exact rule7662 (meaning t m 3055) (meaning t m 3759) (meaning t m 3905) (meaning t m 4419) (meaning t m 4727)

theorem rule7663 (p3055 p3759 p3905 p4419 p4727 : Prop) : (p3759) ∨ (¬ (p3905 ∧ p3759 ∧ p3055 ∧ p4419 ∧ p4727)) := by
  classical
  tauto

theorem initial7663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3759) ∨ (¬ (meaning t m 4726)) := by
  exact rule7663 (meaning t m 3055) (meaning t m 3759) (meaning t m 3905) (meaning t m 4419) (meaning t m 4727)

theorem rule7664 (p3055 p3759 p3905 p4419 p4727 : Prop) : (p3055) ∨ (¬ (p3905 ∧ p3759 ∧ p3055 ∧ p4419 ∧ p4727)) := by
  classical
  tauto

theorem initial7664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3055) ∨ (¬ (meaning t m 4726)) := by
  exact rule7664 (meaning t m 3055) (meaning t m 3759) (meaning t m 3905) (meaning t m 4419) (meaning t m 4727)

theorem rule7665 (p3055 p3759 p3905 p4419 p4727 : Prop) : (p4419) ∨ (¬ (p3905 ∧ p3759 ∧ p3055 ∧ p4419 ∧ p4727)) := by
  classical
  tauto

theorem initial7665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4419) ∨ (¬ (meaning t m 4726)) := by
  exact rule7665 (meaning t m 3055) (meaning t m 3759) (meaning t m 3905) (meaning t m 4419) (meaning t m 4727)

theorem rule7666 (p3055 p3759 p3905 p4419 p4727 : Prop) : (¬ (p3905 ∧ p3759 ∧ p3055 ∧ p4419 ∧ p4727)) ∨ (p4727) := by
  classical
  tauto

theorem initial7666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4726)) ∨ (meaning t m 4727) := by
  exact rule7666 (meaning t m 3055) (meaning t m 3759) (meaning t m 3905) (meaning t m 4419) (meaning t m 4727)

theorem rule7668 (p2598 p3362 p3363 p4729 p4730 : Prop) : (p3363) ∨ (¬ (p3363 ∧ p3362 ∧ p2598 ∧ p4729 ∧ p4730)) := by
  classical
  tauto

theorem initial7668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3363) ∨ (¬ (meaning t m 4728)) := by
  exact rule7668 (meaning t m 2598) (meaning t m 3362) (meaning t m 3363) (meaning t m 4729) (meaning t m 4730)

theorem rule7669 (p2598 p3362 p3363 p4729 p4730 : Prop) : (p3362) ∨ (¬ (p3363 ∧ p3362 ∧ p2598 ∧ p4729 ∧ p4730)) := by
  classical
  tauto

theorem initial7669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3362) ∨ (¬ (meaning t m 4728)) := by
  exact rule7669 (meaning t m 2598) (meaning t m 3362) (meaning t m 3363) (meaning t m 4729) (meaning t m 4730)

theorem rule7670 (p2598 p3362 p3363 p4729 p4730 : Prop) : (p2598) ∨ (¬ (p3363 ∧ p3362 ∧ p2598 ∧ p4729 ∧ p4730)) := by
  classical
  tauto

theorem initial7670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2598) ∨ (¬ (meaning t m 4728)) := by
  exact rule7670 (meaning t m 2598) (meaning t m 3362) (meaning t m 3363) (meaning t m 4729) (meaning t m 4730)

theorem rule7671 (p2598 p3362 p3363 p4729 p4730 : Prop) : (¬ (p3363 ∧ p3362 ∧ p2598 ∧ p4729 ∧ p4730)) ∨ (p4729) := by
  classical
  tauto

theorem initial7671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4728)) ∨ (meaning t m 4729) := by
  exact rule7671 (meaning t m 2598) (meaning t m 3362) (meaning t m 3363) (meaning t m 4729) (meaning t m 4730)

theorem rule7672 (p2598 p3362 p3363 p4729 p4730 : Prop) : (¬ (p3363 ∧ p3362 ∧ p2598 ∧ p4729 ∧ p4730)) ∨ (p4730) := by
  classical
  tauto

theorem initial7672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4728)) ∨ (meaning t m 4730) := by
  exact rule7672 (meaning t m 2598) (meaning t m 3362) (meaning t m 3363) (meaning t m 4729) (meaning t m 4730)

theorem rule7676 (p4726 p4728 : Prop) : (¬ (p4726 ∨ p4728)) ∨ (p4726) ∨ (p4728) := by
  classical
  tauto

theorem initial7676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4725)) ∨ (meaning t m 4726) ∨ (meaning t m 4728) := by
  exact rule7676 (meaning t m 4726) (meaning t m 4728)

theorem rule7677 (p2592 p4725 : Prop) (h : (p2592 ↔ p4725)) : (¬ p2592) ∨ (p4725) := by
  classical
  tauto

theorem initial7677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2592)) ∨ (meaning t m 4725) := by
  have source := ElevenTheory.theory1150 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4)
  exact rule7677 (meaning t m 2592) (meaning t m 4725) source

theorem rule7679 (p2753 p3873 p3954 p4733 p4734 : Prop) : (p3873) ∨ (¬ (p3873 ∧ p2753 ∧ p3954 ∧ p4733 ∧ p4734)) := by
  classical
  tauto

theorem initial7679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3873) ∨ (¬ (meaning t m 4732)) := by
  exact rule7679 (meaning t m 2753) (meaning t m 3873) (meaning t m 3954) (meaning t m 4733) (meaning t m 4734)

theorem rule7680 (p2753 p3873 p3954 p4733 p4734 : Prop) : (p2753) ∨ (¬ (p3873 ∧ p2753 ∧ p3954 ∧ p4733 ∧ p4734)) := by
  classical
  tauto

theorem initial7680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2753) ∨ (¬ (meaning t m 4732)) := by
  exact rule7680 (meaning t m 2753) (meaning t m 3873) (meaning t m 3954) (meaning t m 4733) (meaning t m 4734)

theorem rule7681 (p2753 p3873 p3954 p4733 p4734 : Prop) : (p3954) ∨ (¬ (p3873 ∧ p2753 ∧ p3954 ∧ p4733 ∧ p4734)) := by
  classical
  tauto

theorem initial7681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3954) ∨ (¬ (meaning t m 4732)) := by
  exact rule7681 (meaning t m 2753) (meaning t m 3873) (meaning t m 3954) (meaning t m 4733) (meaning t m 4734)

theorem rule7682 (p2753 p3873 p3954 p4733 p4734 : Prop) : (¬ (p3873 ∧ p2753 ∧ p3954 ∧ p4733 ∧ p4734)) ∨ (p4733) := by
  classical
  tauto

theorem initial7682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4732)) ∨ (meaning t m 4733) := by
  exact rule7682 (meaning t m 2753) (meaning t m 3873) (meaning t m 3954) (meaning t m 4733) (meaning t m 4734)

theorem rule7683 (p2753 p3873 p3954 p4733 p4734 : Prop) : (¬ (p3873 ∧ p2753 ∧ p3954 ∧ p4733 ∧ p4734)) ∨ (p4734) := by
  classical
  tauto

theorem initial7683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4732)) ∨ (meaning t m 4734) := by
  exact rule7683 (meaning t m 2753) (meaning t m 3873) (meaning t m 3954) (meaning t m 4733) (meaning t m 4734)

theorem rule7685 (p2608 p3366 p3589 p4736 p4737 : Prop) : (p3366) ∨ (¬ (p3366 ∧ p3589 ∧ p2608 ∧ p4736 ∧ p4737)) := by
  classical
  tauto

theorem initial7685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3366) ∨ (¬ (meaning t m 4735)) := by
  exact rule7685 (meaning t m 2608) (meaning t m 3366) (meaning t m 3589) (meaning t m 4736) (meaning t m 4737)

theorem rule7686 (p2608 p3366 p3589 p4736 p4737 : Prop) : (p3589) ∨ (¬ (p3366 ∧ p3589 ∧ p2608 ∧ p4736 ∧ p4737)) := by
  classical
  tauto

theorem initial7686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3589) ∨ (¬ (meaning t m 4735)) := by
  exact rule7686 (meaning t m 2608) (meaning t m 3366) (meaning t m 3589) (meaning t m 4736) (meaning t m 4737)

theorem rule7687 (p2608 p3366 p3589 p4736 p4737 : Prop) : (p2608) ∨ (¬ (p3366 ∧ p3589 ∧ p2608 ∧ p4736 ∧ p4737)) := by
  classical
  tauto

theorem initial7687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2608) ∨ (¬ (meaning t m 4735)) := by
  exact rule7687 (meaning t m 2608) (meaning t m 3366) (meaning t m 3589) (meaning t m 4736) (meaning t m 4737)

theorem rule7688 (p2608 p3366 p3589 p4736 p4737 : Prop) : (¬ (p3366 ∧ p3589 ∧ p2608 ∧ p4736 ∧ p4737)) ∨ (p4736) := by
  classical
  tauto

theorem initial7688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4735)) ∨ (meaning t m 4736) := by
  exact rule7688 (meaning t m 2608) (meaning t m 3366) (meaning t m 3589) (meaning t m 4736) (meaning t m 4737)

theorem rule7689 (p2608 p3366 p3589 p4736 p4737 : Prop) : (¬ (p3366 ∧ p3589 ∧ p2608 ∧ p4736 ∧ p4737)) ∨ (p4737) := by
  classical
  tauto

theorem initial7689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4735)) ∨ (meaning t m 4737) := by
  exact rule7689 (meaning t m 2608) (meaning t m 3366) (meaning t m 3589) (meaning t m 4736) (meaning t m 4737)

theorem rule7693 (p4732 p4735 : Prop) : (¬ (p4732 ∨ p4735)) ∨ (p4732) ∨ (p4735) := by
  classical
  tauto

theorem initial7693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4731)) ∨ (meaning t m 4732) ∨ (meaning t m 4735) := by
  exact rule7693 (meaning t m 4732) (meaning t m 4735)

theorem rule7694 (p2602 p4731 : Prop) (h : (p2602 ↔ p4731)) : (¬ p2602) ∨ (p4731) := by
  classical
  tauto

theorem initial7694 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2602)) ∨ (meaning t m 4731) := by
  have source := ElevenTheory.theory1151 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2)
  exact rule7694 (meaning t m 2602) (meaning t m 4731) source

theorem rule7696 (p3694 p4359 p4740 p4741 p4742 : Prop) : (p4359) ∨ (¬ (p4359 ∧ p4740 ∧ p3694 ∧ p4741 ∧ p4742)) := by
  classical
  tauto

theorem initial7696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4359) ∨ (¬ (meaning t m 4739)) := by
  exact rule7696 (meaning t m 3694) (meaning t m 4359) (meaning t m 4740) (meaning t m 4741) (meaning t m 4742)

theorem rule7697 (p3694 p4359 p4740 p4741 p4742 : Prop) : (¬ (p4359 ∧ p4740 ∧ p3694 ∧ p4741 ∧ p4742)) ∨ (p4740) := by
  classical
  tauto

theorem initial7697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4739)) ∨ (meaning t m 4740) := by
  exact rule7697 (meaning t m 3694) (meaning t m 4359) (meaning t m 4740) (meaning t m 4741) (meaning t m 4742)

theorem rule7698 (p3694 p4359 p4740 p4741 p4742 : Prop) : (p3694) ∨ (¬ (p4359 ∧ p4740 ∧ p3694 ∧ p4741 ∧ p4742)) := by
  classical
  tauto

theorem initial7698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3694) ∨ (¬ (meaning t m 4739)) := by
  exact rule7698 (meaning t m 3694) (meaning t m 4359) (meaning t m 4740) (meaning t m 4741) (meaning t m 4742)

theorem rule7699 (p3694 p4359 p4740 p4741 p4742 : Prop) : (¬ (p4359 ∧ p4740 ∧ p3694 ∧ p4741 ∧ p4742)) ∨ (p4741) := by
  classical
  tauto

theorem initial7699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4739)) ∨ (meaning t m 4741) := by
  exact rule7699 (meaning t m 3694) (meaning t m 4359) (meaning t m 4740) (meaning t m 4741) (meaning t m 4742)

theorem rule7702 (p2619 p4188 p4744 p4745 p4746 : Prop) : (p4188) ∨ (¬ (p4188 ∧ p4744 ∧ p2619 ∧ p4745 ∧ p4746)) := by
  classical
  tauto

theorem initial7702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4188) ∨ (¬ (meaning t m 4743)) := by
  exact rule7702 (meaning t m 2619) (meaning t m 4188) (meaning t m 4744) (meaning t m 4745) (meaning t m 4746)

theorem rule7703 (p2619 p4188 p4744 p4745 p4746 : Prop) : (¬ (p4188 ∧ p4744 ∧ p2619 ∧ p4745 ∧ p4746)) ∨ (p4744) := by
  classical
  tauto

theorem initial7703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4743)) ∨ (meaning t m 4744) := by
  exact rule7703 (meaning t m 2619) (meaning t m 4188) (meaning t m 4744) (meaning t m 4745) (meaning t m 4746)

theorem rule7704 (p2619 p4188 p4744 p4745 p4746 : Prop) : (p2619) ∨ (¬ (p4188 ∧ p4744 ∧ p2619 ∧ p4745 ∧ p4746)) := by
  classical
  tauto

theorem initial7704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2619) ∨ (¬ (meaning t m 4743)) := by
  exact rule7704 (meaning t m 2619) (meaning t m 4188) (meaning t m 4744) (meaning t m 4745) (meaning t m 4746)

theorem rule7710 (p4739 p4743 : Prop) : (¬ (p4739 ∨ p4743)) ∨ (p4739) ∨ (p4743) := by
  classical
  tauto

theorem initial7710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4738)) ∨ (meaning t m 4739) ∨ (meaning t m 4743) := by
  exact rule7710 (meaning t m 4739) (meaning t m 4743)

theorem rule7711 (p2613 p4738 : Prop) (h : (p2613 ↔ p4738)) : (¬ p2613) ∨ (p4738) := by
  classical
  tauto

theorem initial7711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2613)) ∨ (meaning t m 4738) := by
  have source := ElevenTheory.theory1152 t (m.theta 2 5) (m.theta 2 8) (m.theta 5 8)
  exact rule7711 (meaning t m 2613) (meaning t m 4738) source

theorem rule7713 (p2810 p3364 p4343 p4749 p4750 : Prop) : (p3364) ∨ (¬ (p3364 ∧ p4343 ∧ p2810 ∧ p4749 ∧ p4750)) := by
  classical
  tauto

theorem initial7713 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3364) ∨ (¬ (meaning t m 4748)) := by
  exact rule7713 (meaning t m 2810) (meaning t m 3364) (meaning t m 4343) (meaning t m 4749) (meaning t m 4750)

theorem rule7714 (p2810 p3364 p4343 p4749 p4750 : Prop) : (p4343) ∨ (¬ (p3364 ∧ p4343 ∧ p2810 ∧ p4749 ∧ p4750)) := by
  classical
  tauto

theorem initial7714 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4343) ∨ (¬ (meaning t m 4748)) := by
  exact rule7714 (meaning t m 2810) (meaning t m 3364) (meaning t m 4343) (meaning t m 4749) (meaning t m 4750)

theorem rule7715 (p2810 p3364 p4343 p4749 p4750 : Prop) : (p2810) ∨ (¬ (p3364 ∧ p4343 ∧ p2810 ∧ p4749 ∧ p4750)) := by
  classical
  tauto

theorem initial7715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2810) ∨ (¬ (meaning t m 4748)) := by
  exact rule7715 (meaning t m 2810) (meaning t m 3364) (meaning t m 4343) (meaning t m 4749) (meaning t m 4750)

theorem rule7716 (p2810 p3364 p4343 p4749 p4750 : Prop) : (¬ (p3364 ∧ p4343 ∧ p2810 ∧ p4749 ∧ p4750)) ∨ (p4749) := by
  classical
  tauto

theorem initial7716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4748)) ∨ (meaning t m 4749) := by
  exact rule7716 (meaning t m 2810) (meaning t m 3364) (meaning t m 4343) (meaning t m 4749) (meaning t m 4750)

theorem rule7717 (p2810 p3364 p4343 p4749 p4750 : Prop) : (¬ (p3364 ∧ p4343 ∧ p2810 ∧ p4749 ∧ p4750)) ∨ (p4750) := by
  classical
  tauto

theorem initial7717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4748)) ∨ (meaning t m 4750) := by
  exact rule7717 (meaning t m 2810) (meaning t m 3364) (meaning t m 4343) (meaning t m 4749) (meaning t m 4750)

theorem rule7719 (p2630 p3475 p3683 p4752 p4753 : Prop) : (p3683) ∨ (¬ (p3683 ∧ p3475 ∧ p2630 ∧ p4752 ∧ p4753)) := by
  classical
  tauto

theorem initial7719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3683) ∨ (¬ (meaning t m 4751)) := by
  exact rule7719 (meaning t m 2630) (meaning t m 3475) (meaning t m 3683) (meaning t m 4752) (meaning t m 4753)

theorem rule7720 (p2630 p3475 p3683 p4752 p4753 : Prop) : (p3475) ∨ (¬ (p3683 ∧ p3475 ∧ p2630 ∧ p4752 ∧ p4753)) := by
  classical
  tauto

theorem initial7720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3475) ∨ (¬ (meaning t m 4751)) := by
  exact rule7720 (meaning t m 2630) (meaning t m 3475) (meaning t m 3683) (meaning t m 4752) (meaning t m 4753)

theorem rule7721 (p2630 p3475 p3683 p4752 p4753 : Prop) : (p2630) ∨ (¬ (p3683 ∧ p3475 ∧ p2630 ∧ p4752 ∧ p4753)) := by
  classical
  tauto

theorem initial7721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2630) ∨ (¬ (meaning t m 4751)) := by
  exact rule7721 (meaning t m 2630) (meaning t m 3475) (meaning t m 3683) (meaning t m 4752) (meaning t m 4753)

theorem rule7722 (p2630 p3475 p3683 p4752 p4753 : Prop) : (¬ (p3683 ∧ p3475 ∧ p2630 ∧ p4752 ∧ p4753)) ∨ (p4752) := by
  classical
  tauto

theorem initial7722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4751)) ∨ (meaning t m 4752) := by
  exact rule7722 (meaning t m 2630) (meaning t m 3475) (meaning t m 3683) (meaning t m 4752) (meaning t m 4753)

theorem rule7723 (p2630 p3475 p3683 p4752 p4753 : Prop) : (¬ (p3683 ∧ p3475 ∧ p2630 ∧ p4752 ∧ p4753)) ∨ (p4753) := by
  classical
  tauto

theorem initial7723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4751)) ∨ (meaning t m 4753) := by
  exact rule7723 (meaning t m 2630) (meaning t m 3475) (meaning t m 3683) (meaning t m 4752) (meaning t m 4753)

theorem rule7727 (p4748 p4751 : Prop) : (¬ (p4748 ∨ p4751)) ∨ (p4748) ∨ (p4751) := by
  classical
  tauto

theorem initial7727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4747)) ∨ (meaning t m 4748) ∨ (meaning t m 4751) := by
  exact rule7727 (meaning t m 4748) (meaning t m 4751)

theorem rule7728 (p2624 p4747 : Prop) (h : (p2624 ↔ p4747)) : (¬ p2624) ∨ (p4747) := by
  classical
  tauto

theorem initial7728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2624)) ∨ (meaning t m 4747) := by
  have source := ElevenTheory.theory1153 t (m.theta 2 3) (m.theta 2 4) (m.theta 3 4)
  exact rule7728 (meaning t m 2624) (meaning t m 4747) source

theorem rule7730 (p2027 p2373 p2542 p2659 p3904 p4120 : Prop) (h : p2027 ∨ (¬ p2659) ∨ (¬ p3904) ∨ (¬ p2373) ∨ (¬ p4120) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2659) ∨ (¬ p3904) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial7730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory1154 t (m.theta 0 4) (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8)
  exact rule7730 (meaning t m 2027) (meaning t m 2373) (meaning t m 2542) (meaning t m 2659) (meaning t m 3904) (meaning t m 4120) source

theorem rule7731 (p4154 p4245 p4319 p4756 p4757 : Prop) : (p4245) ∨ (¬ (p4245 ∧ p4319 ∧ p4154 ∧ p4756 ∧ p4757)) := by
  classical
  tauto

theorem initial7731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4245) ∨ (¬ (meaning t m 4755)) := by
  exact rule7731 (meaning t m 4154) (meaning t m 4245) (meaning t m 4319) (meaning t m 4756) (meaning t m 4757)

theorem rule7732 (p4154 p4245 p4319 p4756 p4757 : Prop) : (p4319) ∨ (¬ (p4245 ∧ p4319 ∧ p4154 ∧ p4756 ∧ p4757)) := by
  classical
  tauto

theorem initial7732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4319) ∨ (¬ (meaning t m 4755)) := by
  exact rule7732 (meaning t m 4154) (meaning t m 4245) (meaning t m 4319) (meaning t m 4756) (meaning t m 4757)

theorem rule7733 (p4154 p4245 p4319 p4756 p4757 : Prop) : (p4154) ∨ (¬ (p4245 ∧ p4319 ∧ p4154 ∧ p4756 ∧ p4757)) := by
  classical
  tauto

theorem initial7733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4154) ∨ (¬ (meaning t m 4755)) := by
  exact rule7733 (meaning t m 4154) (meaning t m 4245) (meaning t m 4319) (meaning t m 4756) (meaning t m 4757)

theorem rule7734 (p4154 p4245 p4319 p4756 p4757 : Prop) : (¬ (p4245 ∧ p4319 ∧ p4154 ∧ p4756 ∧ p4757)) ∨ (p4756) := by
  classical
  tauto

theorem initial7734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4755)) ∨ (meaning t m 4756) := by
  exact rule7734 (meaning t m 4154) (meaning t m 4245) (meaning t m 4319) (meaning t m 4756) (meaning t m 4757)

theorem rule7735 (p4154 p4245 p4319 p4756 p4757 : Prop) : (¬ (p4245 ∧ p4319 ∧ p4154 ∧ p4756 ∧ p4757)) ∨ (p4757) := by
  classical
  tauto

theorem initial7735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4755)) ∨ (meaning t m 4757) := by
  exact rule7735 (meaning t m 4154) (meaning t m 4245) (meaning t m 4319) (meaning t m 4756) (meaning t m 4757)

theorem rule7737 (p2641 p3922 p4759 p4760 p4761 : Prop) : (p3922) ∨ (¬ (p3922 ∧ p4759 ∧ p2641 ∧ p4760 ∧ p4761)) := by
  classical
  tauto

theorem initial7737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3922) ∨ (¬ (meaning t m 4758)) := by
  exact rule7737 (meaning t m 2641) (meaning t m 3922) (meaning t m 4759) (meaning t m 4760) (meaning t m 4761)

theorem rule7738 (p2641 p3922 p4759 p4760 p4761 : Prop) : (¬ (p3922 ∧ p4759 ∧ p2641 ∧ p4760 ∧ p4761)) ∨ (p4759) := by
  classical
  tauto

theorem initial7738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4758)) ∨ (meaning t m 4759) := by
  exact rule7738 (meaning t m 2641) (meaning t m 3922) (meaning t m 4759) (meaning t m 4760) (meaning t m 4761)

theorem rule7739 (p2641 p3922 p4759 p4760 p4761 : Prop) : (p2641) ∨ (¬ (p3922 ∧ p4759 ∧ p2641 ∧ p4760 ∧ p4761)) := by
  classical
  tauto

theorem initial7739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2641) ∨ (¬ (meaning t m 4758)) := by
  exact rule7739 (meaning t m 2641) (meaning t m 3922) (meaning t m 4759) (meaning t m 4760) (meaning t m 4761)

theorem rule7741 (p2641 p3922 p4759 p4760 p4761 : Prop) : (¬ (p3922 ∧ p4759 ∧ p2641 ∧ p4760 ∧ p4761)) ∨ (p4761) := by
  classical
  tauto

theorem initial7741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4758)) ∨ (meaning t m 4761) := by
  exact rule7741 (meaning t m 2641) (meaning t m 3922) (meaning t m 4759) (meaning t m 4760) (meaning t m 4761)

theorem rule7745 (p4755 p4758 : Prop) : (¬ (p4755 ∨ p4758)) ∨ (p4755) ∨ (p4758) := by
  classical
  tauto

theorem initial7745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4754)) ∨ (meaning t m 4755) ∨ (meaning t m 4758) := by
  exact rule7745 (meaning t m 4755) (meaning t m 4758)

theorem rule7746 (p2635 p4754 : Prop) (h : (p2635 ↔ p4754)) : (¬ p2635) ∨ (p4754) := by
  classical
  tauto

theorem initial7746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2635)) ∨ (meaning t m 4754) := by
  have source := ElevenTheory.theory1155 t (m.theta 1 3) (m.theta 1 6) (m.theta 3 6)
  exact rule7746 (meaning t m 2635) (meaning t m 4754) source

theorem rule7750 (p2654 p2661 : Prop) : (p2654) ∨ (p2661) ∨ (¬ (p2654 ∨ p2661)) := by
  classical
  tauto

theorem initial7750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2654) ∨ (meaning t m 2661) ∨ (¬ (meaning t m 4762)) := by
  exact rule7750 (meaning t m 2654) (meaning t m 2661)

theorem rule7751 (p2645 p4762 : Prop) (h : (p2645 ↔ p4762)) : (¬ p2645) ∨ (p4762) := by
  classical
  tauto

theorem initial7751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2645)) ∨ (meaning t m 4762) := by
  have source := ElevenTheory.theory1156 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4)
  exact rule7751 (meaning t m 2645) (meaning t m 4762) source

theorem rule7769 (p3324 p4196 p4769 p4770 p4771 : Prop) : (p4196) ∨ (¬ (p4196 ∧ p4769 ∧ p3324 ∧ p4770 ∧ p4771)) := by
  classical
  tauto

theorem initial7769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4196) ∨ (¬ (meaning t m 4768)) := by
  exact rule7769 (meaning t m 3324) (meaning t m 4196) (meaning t m 4769) (meaning t m 4770) (meaning t m 4771)

theorem rule7770 (p3324 p4196 p4769 p4770 p4771 : Prop) : (¬ (p4196 ∧ p4769 ∧ p3324 ∧ p4770 ∧ p4771)) ∨ (p4769) := by
  classical
  tauto

theorem initial7770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4768)) ∨ (meaning t m 4769) := by
  exact rule7770 (meaning t m 3324) (meaning t m 4196) (meaning t m 4769) (meaning t m 4770) (meaning t m 4771)

theorem rule7771 (p3324 p4196 p4769 p4770 p4771 : Prop) : (p3324) ∨ (¬ (p4196 ∧ p4769 ∧ p3324 ∧ p4770 ∧ p4771)) := by
  classical
  tauto

theorem initial7771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3324) ∨ (¬ (meaning t m 4768)) := by
  exact rule7771 (meaning t m 3324) (meaning t m 4196) (meaning t m 4769) (meaning t m 4770) (meaning t m 4771)

theorem rule7773 (p3324 p4196 p4769 p4770 p4771 : Prop) : (¬ (p4196 ∧ p4769 ∧ p3324 ∧ p4770 ∧ p4771)) ∨ (p4771) := by
  classical
  tauto

theorem initial7773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4768)) ∨ (meaning t m 4771) := by
  exact rule7773 (meaning t m 3324) (meaning t m 4196) (meaning t m 4769) (meaning t m 4770) (meaning t m 4771)

theorem rule7775 (p2668 p4341 p4417 p4773 p4774 : Prop) : (p4417) ∨ (¬ (p4417 ∧ p4341 ∧ p2668 ∧ p4773 ∧ p4774)) := by
  classical
  tauto

theorem initial7775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4417) ∨ (¬ (meaning t m 4772)) := by
  exact rule7775 (meaning t m 2668) (meaning t m 4341) (meaning t m 4417) (meaning t m 4773) (meaning t m 4774)

theorem rule7776 (p2668 p4341 p4417 p4773 p4774 : Prop) : (p4341) ∨ (¬ (p4417 ∧ p4341 ∧ p2668 ∧ p4773 ∧ p4774)) := by
  classical
  tauto

theorem initial7776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4341) ∨ (¬ (meaning t m 4772)) := by
  exact rule7776 (meaning t m 2668) (meaning t m 4341) (meaning t m 4417) (meaning t m 4773) (meaning t m 4774)

theorem rule7777 (p2668 p4341 p4417 p4773 p4774 : Prop) : (p2668) ∨ (¬ (p4417 ∧ p4341 ∧ p2668 ∧ p4773 ∧ p4774)) := by
  classical
  tauto

theorem initial7777 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2668) ∨ (¬ (meaning t m 4772)) := by
  exact rule7777 (meaning t m 2668) (meaning t m 4341) (meaning t m 4417) (meaning t m 4773) (meaning t m 4774)

theorem rule7779 (p2668 p4341 p4417 p4773 p4774 : Prop) : (¬ (p4417 ∧ p4341 ∧ p2668 ∧ p4773 ∧ p4774)) ∨ (p4774) := by
  classical
  tauto

theorem initial7779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4772)) ∨ (meaning t m 4774) := by
  exact rule7779 (meaning t m 2668) (meaning t m 4341) (meaning t m 4417) (meaning t m 4773) (meaning t m 4774)

theorem rule7783 (p4768 p4772 : Prop) : (¬ (p4768 ∨ p4772)) ∨ (p4768) ∨ (p4772) := by
  classical
  tauto

theorem initial7783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4767)) ∨ (meaning t m 4768) ∨ (meaning t m 4772) := by
  exact rule7783 (meaning t m 4768) (meaning t m 4772)

theorem rule7784 (p2670 p4767 : Prop) (h : (p2670 ↔ p4767)) : (¬ p2670) ∨ (p4767) := by
  classical
  tauto

theorem initial7784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2670)) ∨ (meaning t m 4767) := by
  have source := ElevenTheory.theory1159 t (m.theta 3 6) (m.theta 3 8) (m.theta 6 8)
  exact rule7784 (meaning t m 2670) (meaning t m 4767) source

theorem rule7786 (p3572 p4357 p4777 p4778 p4779 : Prop) : (p4357) ∨ (¬ (p4357 ∧ p4777 ∧ p3572 ∧ p4778 ∧ p4779)) := by
  classical
  tauto

theorem initial7786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4357) ∨ (¬ (meaning t m 4776)) := by
  exact rule7786 (meaning t m 3572) (meaning t m 4357) (meaning t m 4777) (meaning t m 4778) (meaning t m 4779)

theorem rule7787 (p3572 p4357 p4777 p4778 p4779 : Prop) : (¬ (p4357 ∧ p4777 ∧ p3572 ∧ p4778 ∧ p4779)) ∨ (p4777) := by
  classical
  tauto

theorem initial7787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4776)) ∨ (meaning t m 4777) := by
  exact rule7787 (meaning t m 3572) (meaning t m 4357) (meaning t m 4777) (meaning t m 4778) (meaning t m 4779)

theorem rule7788 (p3572 p4357 p4777 p4778 p4779 : Prop) : (p3572) ∨ (¬ (p4357 ∧ p4777 ∧ p3572 ∧ p4778 ∧ p4779)) := by
  classical
  tauto

theorem initial7788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3572) ∨ (¬ (meaning t m 4776)) := by
  exact rule7788 (meaning t m 3572) (meaning t m 4357) (meaning t m 4777) (meaning t m 4778) (meaning t m 4779)

theorem rule7789 (p3572 p4357 p4777 p4778 p4779 : Prop) : (¬ (p4357 ∧ p4777 ∧ p3572 ∧ p4778 ∧ p4779)) ∨ (p4778) := by
  classical
  tauto

theorem initial7789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4776)) ∨ (meaning t m 4778) := by
  exact rule7789 (meaning t m 3572) (meaning t m 4357) (meaning t m 4777) (meaning t m 4778) (meaning t m 4779)

theorem rule7790 (p3572 p4357 p4777 p4778 p4779 : Prop) : (¬ (p4357 ∧ p4777 ∧ p3572 ∧ p4778 ∧ p4779)) ∨ (p4779) := by
  classical
  tauto

theorem initial7790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4776)) ∨ (meaning t m 4779) := by
  exact rule7790 (meaning t m 3572) (meaning t m 4357) (meaning t m 4777) (meaning t m 4778) (meaning t m 4779)

theorem rule7792 (p2685 p4325 p4781 p4782 p4783 : Prop) : (p4325) ∨ (¬ (p4325 ∧ p4781 ∧ p2685 ∧ p4782 ∧ p4783)) := by
  classical
  tauto

theorem initial7792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4325) ∨ (¬ (meaning t m 4780)) := by
  exact rule7792 (meaning t m 2685) (meaning t m 4325) (meaning t m 4781) (meaning t m 4782) (meaning t m 4783)

theorem rule7793 (p2685 p4325 p4781 p4782 p4783 : Prop) : (¬ (p4325 ∧ p4781 ∧ p2685 ∧ p4782 ∧ p4783)) ∨ (p4781) := by
  classical
  tauto

theorem initial7793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4780)) ∨ (meaning t m 4781) := by
  exact rule7793 (meaning t m 2685) (meaning t m 4325) (meaning t m 4781) (meaning t m 4782) (meaning t m 4783)

theorem rule7794 (p2685 p4325 p4781 p4782 p4783 : Prop) : (p2685) ∨ (¬ (p4325 ∧ p4781 ∧ p2685 ∧ p4782 ∧ p4783)) := by
  classical
  tauto

theorem initial7794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2685) ∨ (¬ (meaning t m 4780)) := by
  exact rule7794 (meaning t m 2685) (meaning t m 4325) (meaning t m 4781) (meaning t m 4782) (meaning t m 4783)

theorem rule7795 (p2685 p4325 p4781 p4782 p4783 : Prop) : (¬ (p4325 ∧ p4781 ∧ p2685 ∧ p4782 ∧ p4783)) ∨ (p4782) := by
  classical
  tauto

theorem initial7795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4780)) ∨ (meaning t m 4782) := by
  exact rule7795 (meaning t m 2685) (meaning t m 4325) (meaning t m 4781) (meaning t m 4782) (meaning t m 4783)

theorem rule7796 (p2685 p4325 p4781 p4782 p4783 : Prop) : (¬ (p4325 ∧ p4781 ∧ p2685 ∧ p4782 ∧ p4783)) ∨ (p4783) := by
  classical
  tauto

theorem initial7796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4780)) ∨ (meaning t m 4783) := by
  exact rule7796 (meaning t m 2685) (meaning t m 4325) (meaning t m 4781) (meaning t m 4782) (meaning t m 4783)

theorem rule7800 (p4776 p4780 : Prop) : (¬ (p4776 ∨ p4780)) ∨ (p4776) ∨ (p4780) := by
  classical
  tauto

theorem initial7800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4775)) ∨ (meaning t m 4776) ∨ (meaning t m 4780) := by
  exact rule7800 (meaning t m 4776) (meaning t m 4780)

theorem rule7801 (p2679 p4775 : Prop) (h : (p2679 ↔ p4775)) : (¬ p2679) ∨ (p4775) := by
  classical
  tauto

theorem initial7801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2679)) ∨ (meaning t m 4775) := by
  have source := ElevenTheory.theory1160 t (m.theta 2 3) (m.theta 2 7) (m.theta 3 7)
  exact rule7801 (meaning t m 2679) (meaning t m 4775) source

theorem rule7803 (p2811 p3365 p4236 p4786 p4787 : Prop) : (p4236) ∨ (¬ (p4236 ∧ p2811 ∧ p3365 ∧ p4786 ∧ p4787)) := by
  classical
  tauto

theorem initial7803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4236) ∨ (¬ (meaning t m 4785)) := by
  exact rule7803 (meaning t m 2811) (meaning t m 3365) (meaning t m 4236) (meaning t m 4786) (meaning t m 4787)

theorem rule7804 (p2811 p3365 p4236 p4786 p4787 : Prop) : (p2811) ∨ (¬ (p4236 ∧ p2811 ∧ p3365 ∧ p4786 ∧ p4787)) := by
  classical
  tauto

theorem initial7804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2811) ∨ (¬ (meaning t m 4785)) := by
  exact rule7804 (meaning t m 2811) (meaning t m 3365) (meaning t m 4236) (meaning t m 4786) (meaning t m 4787)

theorem rule7805 (p2811 p3365 p4236 p4786 p4787 : Prop) : (p3365) ∨ (¬ (p4236 ∧ p2811 ∧ p3365 ∧ p4786 ∧ p4787)) := by
  classical
  tauto

theorem initial7805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3365) ∨ (¬ (meaning t m 4785)) := by
  exact rule7805 (meaning t m 2811) (meaning t m 3365) (meaning t m 4236) (meaning t m 4786) (meaning t m 4787)

theorem rule7806 (p2811 p3365 p4236 p4786 p4787 : Prop) : (¬ (p4236 ∧ p2811 ∧ p3365 ∧ p4786 ∧ p4787)) ∨ (p4786) := by
  classical
  tauto

theorem initial7806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4785)) ∨ (meaning t m 4786) := by
  exact rule7806 (meaning t m 2811) (meaning t m 3365) (meaning t m 4236) (meaning t m 4786) (meaning t m 4787)

theorem rule7807 (p2811 p3365 p4236 p4786 p4787 : Prop) : (¬ (p4236 ∧ p2811 ∧ p3365 ∧ p4786 ∧ p4787)) ∨ (p4787) := by
  classical
  tauto

theorem initial7807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4785)) ∨ (meaning t m 4787) := by
  exact rule7807 (meaning t m 2811) (meaning t m 3365) (meaning t m 4236) (meaning t m 4786) (meaning t m 4787)

theorem rule7809 (p2696 p3361 p4117 p4789 p4790 : Prop) : (p3361) ∨ (¬ (p3361 ∧ p4117 ∧ p2696 ∧ p4789 ∧ p4790)) := by
  classical
  tauto

theorem initial7809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3361) ∨ (¬ (meaning t m 4788)) := by
  exact rule7809 (meaning t m 2696) (meaning t m 3361) (meaning t m 4117) (meaning t m 4789) (meaning t m 4790)

theorem rule7810 (p2696 p3361 p4117 p4789 p4790 : Prop) : (p4117) ∨ (¬ (p3361 ∧ p4117 ∧ p2696 ∧ p4789 ∧ p4790)) := by
  classical
  tauto

theorem initial7810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4117) ∨ (¬ (meaning t m 4788)) := by
  exact rule7810 (meaning t m 2696) (meaning t m 3361) (meaning t m 4117) (meaning t m 4789) (meaning t m 4790)

theorem rule7811 (p2696 p3361 p4117 p4789 p4790 : Prop) : (p2696) ∨ (¬ (p3361 ∧ p4117 ∧ p2696 ∧ p4789 ∧ p4790)) := by
  classical
  tauto

theorem initial7811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2696) ∨ (¬ (meaning t m 4788)) := by
  exact rule7811 (meaning t m 2696) (meaning t m 3361) (meaning t m 4117) (meaning t m 4789) (meaning t m 4790)

theorem rule7812 (p2696 p3361 p4117 p4789 p4790 : Prop) : (¬ (p3361 ∧ p4117 ∧ p2696 ∧ p4789 ∧ p4790)) ∨ (p4789) := by
  classical
  tauto

theorem initial7812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4788)) ∨ (meaning t m 4789) := by
  exact rule7812 (meaning t m 2696) (meaning t m 3361) (meaning t m 4117) (meaning t m 4789) (meaning t m 4790)

theorem rule7813 (p2696 p3361 p4117 p4789 p4790 : Prop) : (¬ (p3361 ∧ p4117 ∧ p2696 ∧ p4789 ∧ p4790)) ∨ (p4790) := by
  classical
  tauto

theorem initial7813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4788)) ∨ (meaning t m 4790) := by
  exact rule7813 (meaning t m 2696) (meaning t m 3361) (meaning t m 4117) (meaning t m 4789) (meaning t m 4790)

theorem rule7817 (p4785 p4788 : Prop) : (¬ (p4785 ∨ p4788)) ∨ (p4785) ∨ (p4788) := by
  classical
  tauto

theorem initial7817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4784)) ∨ (meaning t m 4785) ∨ (meaning t m 4788) := by
  exact rule7817 (meaning t m 4785) (meaning t m 4788)

theorem rule7818 (p2690 p4784 : Prop) (h : (p2690 ↔ p4784)) : (¬ p2690) ∨ (p4784) := by
  classical
  tauto

theorem initial7818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2690)) ∨ (meaning t m 4784) := by
  have source := ElevenTheory.theory1161 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3)
  exact rule7818 (meaning t m 2690) (meaning t m 4784) source

theorem rule7820 (p2737 p3588 p4781 : Prop) (h : (¬ p3588) ∨ (¬ p2737) ∨ (¬ p4781)) : (¬ p2737) ∨ (¬ p3588) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial7820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory1162 (m.theta 1 2) (m.theta 2 3) (m.theta 2 7)
  exact rule7820 (meaning t m 2737) (meaning t m 3588) (meaning t m 4781) source

theorem rule7821 (p3588 p4400 p4424 p4793 p4794 : Prop) : (p4400) ∨ (¬ (p4400 ∧ p4424 ∧ p3588 ∧ p4793 ∧ p4794)) := by
  classical
  tauto

theorem initial7821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4400) ∨ (¬ (meaning t m 4792)) := by
  exact rule7821 (meaning t m 3588) (meaning t m 4400) (meaning t m 4424) (meaning t m 4793) (meaning t m 4794)

theorem rule7822 (p3588 p4400 p4424 p4793 p4794 : Prop) : (p4424) ∨ (¬ (p4400 ∧ p4424 ∧ p3588 ∧ p4793 ∧ p4794)) := by
  classical
  tauto

theorem initial7822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4424) ∨ (¬ (meaning t m 4792)) := by
  exact rule7822 (meaning t m 3588) (meaning t m 4400) (meaning t m 4424) (meaning t m 4793) (meaning t m 4794)

theorem rule7823 (p3588 p4400 p4424 p4793 p4794 : Prop) : (p3588) ∨ (¬ (p4400 ∧ p4424 ∧ p3588 ∧ p4793 ∧ p4794)) := by
  classical
  tauto

theorem initial7823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3588) ∨ (¬ (meaning t m 4792)) := by
  exact rule7823 (meaning t m 3588) (meaning t m 4400) (meaning t m 4424) (meaning t m 4793) (meaning t m 4794)

theorem rule7824 (p3588 p4400 p4424 p4793 p4794 : Prop) : (¬ (p4400 ∧ p4424 ∧ p3588 ∧ p4793 ∧ p4794)) ∨ (p4793) := by
  classical
  tauto

theorem initial7824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4792)) ∨ (meaning t m 4793) := by
  exact rule7824 (meaning t m 3588) (meaning t m 4400) (meaning t m 4424) (meaning t m 4793) (meaning t m 4794)

theorem rule7825 (p3588 p4400 p4424 p4793 p4794 : Prop) : (¬ (p4400 ∧ p4424 ∧ p3588 ∧ p4793 ∧ p4794)) ∨ (p4794) := by
  classical
  tauto

theorem initial7825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4792)) ∨ (meaning t m 4794) := by
  exact rule7825 (meaning t m 3588) (meaning t m 4400) (meaning t m 4424) (meaning t m 4793) (meaning t m 4794)

theorem rule7827 (p2707 p3576 p3687 p4796 p4797 : Prop) : (p3576) ∨ (¬ (p3576 ∧ p3687 ∧ p2707 ∧ p4796 ∧ p4797)) := by
  classical
  tauto

theorem initial7827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3576) ∨ (¬ (meaning t m 4795)) := by
  exact rule7827 (meaning t m 2707) (meaning t m 3576) (meaning t m 3687) (meaning t m 4796) (meaning t m 4797)

theorem rule7828 (p2707 p3576 p3687 p4796 p4797 : Prop) : (p3687) ∨ (¬ (p3576 ∧ p3687 ∧ p2707 ∧ p4796 ∧ p4797)) := by
  classical
  tauto

theorem initial7828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3687) ∨ (¬ (meaning t m 4795)) := by
  exact rule7828 (meaning t m 2707) (meaning t m 3576) (meaning t m 3687) (meaning t m 4796) (meaning t m 4797)

theorem rule7829 (p2707 p3576 p3687 p4796 p4797 : Prop) : (p2707) ∨ (¬ (p3576 ∧ p3687 ∧ p2707 ∧ p4796 ∧ p4797)) := by
  classical
  tauto

theorem initial7829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2707) ∨ (¬ (meaning t m 4795)) := by
  exact rule7829 (meaning t m 2707) (meaning t m 3576) (meaning t m 3687) (meaning t m 4796) (meaning t m 4797)

theorem rule7830 (p2707 p3576 p3687 p4796 p4797 : Prop) : (¬ (p3576 ∧ p3687 ∧ p2707 ∧ p4796 ∧ p4797)) ∨ (p4796) := by
  classical
  tauto

theorem initial7830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4795)) ∨ (meaning t m 4796) := by
  exact rule7830 (meaning t m 2707) (meaning t m 3576) (meaning t m 3687) (meaning t m 4796) (meaning t m 4797)

theorem rule7831 (p2707 p3576 p3687 p4796 p4797 : Prop) : (¬ (p3576 ∧ p3687 ∧ p2707 ∧ p4796 ∧ p4797)) ∨ (p4797) := by
  classical
  tauto

theorem initial7831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4795)) ∨ (meaning t m 4797) := by
  exact rule7831 (meaning t m 2707) (meaning t m 3576) (meaning t m 3687) (meaning t m 4796) (meaning t m 4797)

theorem rule7835 (p4792 p4795 : Prop) : (¬ (p4792 ∨ p4795)) ∨ (p4792) ∨ (p4795) := by
  classical
  tauto

theorem initial7835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4791)) ∨ (meaning t m 4792) ∨ (meaning t m 4795) := by
  exact rule7835 (meaning t m 4792) (meaning t m 4795)

theorem rule7836 (p2701 p4791 : Prop) (h : (p2701 ↔ p4791)) : (¬ p2701) ∨ (p4791) := by
  classical
  tauto

theorem initial7836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2701)) ∨ (meaning t m 4791) := by
  have source := ElevenTheory.theory1163 t (m.theta 1 2) (m.theta 1 7) (m.theta 2 7)
  exact rule7836 (meaning t m 2701) (meaning t m 4791) source

theorem rule7838 (p3659 p3685 p4800 p4801 p4802 : Prop) : (p3685) ∨ (¬ (p3685 ∧ p4800 ∧ p3659 ∧ p4801 ∧ p4802)) := by
  classical
  tauto

theorem initial7838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3685) ∨ (¬ (meaning t m 4799)) := by
  exact rule7838 (meaning t m 3659) (meaning t m 3685) (meaning t m 4800) (meaning t m 4801) (meaning t m 4802)

theorem rule7839 (p3659 p3685 p4800 p4801 p4802 : Prop) : (¬ (p3685 ∧ p4800 ∧ p3659 ∧ p4801 ∧ p4802)) ∨ (p4800) := by
  classical
  tauto

theorem initial7839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4799)) ∨ (meaning t m 4800) := by
  exact rule7839 (meaning t m 3659) (meaning t m 3685) (meaning t m 4800) (meaning t m 4801) (meaning t m 4802)

theorem rule7840 (p3659 p3685 p4800 p4801 p4802 : Prop) : (p3659) ∨ (¬ (p3685 ∧ p4800 ∧ p3659 ∧ p4801 ∧ p4802)) := by
  classical
  tauto

theorem initial7840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3659) ∨ (¬ (meaning t m 4799)) := by
  exact rule7840 (meaning t m 3659) (meaning t m 3685) (meaning t m 4800) (meaning t m 4801) (meaning t m 4802)

theorem rule7842 (p3659 p3685 p4800 p4801 p4802 : Prop) : (¬ (p3685 ∧ p4800 ∧ p3659 ∧ p4801 ∧ p4802)) ∨ (p4802) := by
  classical
  tauto

theorem initial7842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4799)) ∨ (meaning t m 4802) := by
  exact rule7842 (meaning t m 3659) (meaning t m 3685) (meaning t m 4800) (meaning t m 4801) (meaning t m 4802)

theorem rule7844 (p2717 p4804 p4805 p4806 p4807 : Prop) : (¬ (p4804 ∧ p4805 ∧ p2717 ∧ p4806 ∧ p4807)) ∨ (p4804) := by
  classical
  tauto

theorem initial7844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4803)) ∨ (meaning t m 4804) := by
  exact rule7844 (meaning t m 2717) (meaning t m 4804) (meaning t m 4805) (meaning t m 4806) (meaning t m 4807)

theorem rule7845 (p2717 p4804 p4805 p4806 p4807 : Prop) : (¬ (p4804 ∧ p4805 ∧ p2717 ∧ p4806 ∧ p4807)) ∨ (p4805) := by
  classical
  tauto

theorem initial7845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4803)) ∨ (meaning t m 4805) := by
  exact rule7845 (meaning t m 2717) (meaning t m 4804) (meaning t m 4805) (meaning t m 4806) (meaning t m 4807)

theorem rule7846 (p2717 p4804 p4805 p4806 p4807 : Prop) : (p2717) ∨ (¬ (p4804 ∧ p4805 ∧ p2717 ∧ p4806 ∧ p4807)) := by
  classical
  tauto

theorem initial7846 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2717) ∨ (¬ (meaning t m 4803)) := by
  exact rule7846 (meaning t m 2717) (meaning t m 4804) (meaning t m 4805) (meaning t m 4806) (meaning t m 4807)

theorem rule7848 (p2717 p4804 p4805 p4806 p4807 : Prop) : (¬ (p4804 ∧ p4805 ∧ p2717 ∧ p4806 ∧ p4807)) ∨ (p4807) := by
  classical
  tauto

theorem initial7848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4803)) ∨ (meaning t m 4807) := by
  exact rule7848 (meaning t m 2717) (meaning t m 4804) (meaning t m 4805) (meaning t m 4806) (meaning t m 4807)

theorem rule7852 (p4799 p4803 : Prop) : (¬ (p4799 ∨ p4803)) ∨ (p4799) ∨ (p4803) := by
  classical
  tauto

theorem initial7852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4798)) ∨ (meaning t m 4799) ∨ (meaning t m 4803) := by
  exact rule7852 (meaning t m 4799) (meaning t m 4803)

theorem rule7853 (p2711 p4798 : Prop) (h : (p2711 ↔ p4798)) : (¬ p2711) ∨ (p4798) := by
  classical
  tauto

theorem initial7853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2711)) ∨ (meaning t m 4798) := by
  have source := ElevenTheory.theory1164 t (m.theta 2 7) (m.theta 2 8) (m.theta 7 8)
  exact rule7853 (meaning t m 2711) (meaning t m 4798) source

theorem rule7855 (p3402 p4111 p4116 p4810 p4811 : Prop) : (p3402) ∨ (¬ (p3402 ∧ p4116 ∧ p4111 ∧ p4810 ∧ p4811)) := by
  classical
  tauto

theorem initial7855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3402) ∨ (¬ (meaning t m 4809)) := by
  exact rule7855 (meaning t m 3402) (meaning t m 4111) (meaning t m 4116) (meaning t m 4810) (meaning t m 4811)

theorem rule7856 (p3402 p4111 p4116 p4810 p4811 : Prop) : (p4116) ∨ (¬ (p3402 ∧ p4116 ∧ p4111 ∧ p4810 ∧ p4811)) := by
  classical
  tauto

theorem initial7856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4116) ∨ (¬ (meaning t m 4809)) := by
  exact rule7856 (meaning t m 3402) (meaning t m 4111) (meaning t m 4116) (meaning t m 4810) (meaning t m 4811)

theorem rule7857 (p3402 p4111 p4116 p4810 p4811 : Prop) : (p4111) ∨ (¬ (p3402 ∧ p4116 ∧ p4111 ∧ p4810 ∧ p4811)) := by
  classical
  tauto

theorem initial7857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4111) ∨ (¬ (meaning t m 4809)) := by
  exact rule7857 (meaning t m 3402) (meaning t m 4111) (meaning t m 4116) (meaning t m 4810) (meaning t m 4811)

theorem rule7859 (p3402 p4111 p4116 p4810 p4811 : Prop) : (¬ (p3402 ∧ p4116 ∧ p4111 ∧ p4810 ∧ p4811)) ∨ (p4811) := by
  classical
  tauto

theorem initial7859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4809)) ∨ (meaning t m 4811) := by
  exact rule7859 (meaning t m 3402) (meaning t m 4111) (meaning t m 4116) (meaning t m 4810) (meaning t m 4811)

theorem rule7861 (p2727 p3487 p4281 p4813 p4814 : Prop) : (p3487) ∨ (¬ (p3487 ∧ p4281 ∧ p2727 ∧ p4813 ∧ p4814)) := by
  classical
  tauto

theorem initial7861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3487) ∨ (¬ (meaning t m 4812)) := by
  exact rule7861 (meaning t m 2727) (meaning t m 3487) (meaning t m 4281) (meaning t m 4813) (meaning t m 4814)

theorem rule7862 (p2727 p3487 p4281 p4813 p4814 : Prop) : (p4281) ∨ (¬ (p3487 ∧ p4281 ∧ p2727 ∧ p4813 ∧ p4814)) := by
  classical
  tauto

theorem initial7862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4281) ∨ (¬ (meaning t m 4812)) := by
  exact rule7862 (meaning t m 2727) (meaning t m 3487) (meaning t m 4281) (meaning t m 4813) (meaning t m 4814)

theorem rule7863 (p2727 p3487 p4281 p4813 p4814 : Prop) : (p2727) ∨ (¬ (p3487 ∧ p4281 ∧ p2727 ∧ p4813 ∧ p4814)) := by
  classical
  tauto

theorem initial7863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2727) ∨ (¬ (meaning t m 4812)) := by
  exact rule7863 (meaning t m 2727) (meaning t m 3487) (meaning t m 4281) (meaning t m 4813) (meaning t m 4814)

theorem rule7864 (p2727 p3487 p4281 p4813 p4814 : Prop) : (¬ (p3487 ∧ p4281 ∧ p2727 ∧ p4813 ∧ p4814)) ∨ (p4813) := by
  classical
  tauto

theorem initial7864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4812)) ∨ (meaning t m 4813) := by
  exact rule7864 (meaning t m 2727) (meaning t m 3487) (meaning t m 4281) (meaning t m 4813) (meaning t m 4814)

theorem rule7865 (p2727 p3487 p4281 p4813 p4814 : Prop) : (¬ (p3487 ∧ p4281 ∧ p2727 ∧ p4813 ∧ p4814)) ∨ (p4814) := by
  classical
  tauto

theorem initial7865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4812)) ∨ (meaning t m 4814) := by
  exact rule7865 (meaning t m 2727) (meaning t m 3487) (meaning t m 4281) (meaning t m 4813) (meaning t m 4814)

theorem rule7869 (p4809 p4812 : Prop) : (¬ (p4809 ∨ p4812)) ∨ (p4809) ∨ (p4812) := by
  classical
  tauto

theorem initial7869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4808)) ∨ (meaning t m 4809) ∨ (meaning t m 4812) := by
  exact rule7869 (meaning t m 4809) (meaning t m 4812)

theorem rule7870 (p2721 p4808 : Prop) (h : (p2721 ↔ p4808)) : (¬ p2721) ∨ (p4808) := by
  classical
  tauto

theorem initial7870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2721)) ∨ (meaning t m 4808) := by
  have source := ElevenTheory.theory1165 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 4)
  exact rule7870 (meaning t m 2721) (meaning t m 4808) source

theorem rule7872 (p2727 p4111 : Prop) (h : (¬ p4111) ∨ (¬ p2727)) : (¬ p2727) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial7872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory1166 (m.theta 1 3) (m.theta 3 4)
  exact rule7872 (meaning t m 2727) (meaning t m 4111) source

theorem rule7875 (p2740 p2747 : Prop) : (p2740) ∨ (p2747) ∨ (¬ (p2740 ∨ p2747)) := by
  classical
  tauto

theorem initial7875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2740) ∨ (meaning t m 2747) ∨ (¬ (meaning t m 4815)) := by
  exact rule7875 (meaning t m 2740) (meaning t m 2747)

theorem rule7876 (p2731 p4815 : Prop) (h : (p2731 ↔ p4815)) : (¬ p2731) ∨ (p4815) := by
  classical
  tauto

theorem initial7876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2731)) ∨ (meaning t m 4815) := by
  have source := ElevenTheory.theory1167 t (m.theta 1 2) (m.theta 1 3) (m.theta 2 3)
  exact rule7876 (meaning t m 2731) (meaning t m 4815) source

theorem rule7899 (p2027 p2685 p2696 p2741 p2996 p4737 : Prop) (h : (¬ p4737) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2685) ∨ (¬ p2741) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2741) ∨ (¬ p2996) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial7899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory1170 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 7)
  exact rule7899 (meaning t m 2027) (meaning t m 2685) (meaning t m 2696) (meaning t m 2741) (meaning t m 2996) (meaning t m 4737) source

theorem rule7900 (p4381 p4823 p4824 p4825 p4826 : Prop) : (¬ (p4823 ∧ p4824 ∧ p4381 ∧ p4825 ∧ p4826)) ∨ (p4823) := by
  classical
  tauto

theorem initial7900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4822)) ∨ (meaning t m 4823) := by
  exact rule7900 (meaning t m 4381) (meaning t m 4823) (meaning t m 4824) (meaning t m 4825) (meaning t m 4826)

theorem rule7902 (p4381 p4823 p4824 p4825 p4826 : Prop) : (p4381) ∨ (¬ (p4823 ∧ p4824 ∧ p4381 ∧ p4825 ∧ p4826)) := by
  classical
  tauto

theorem initial7902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4381) ∨ (¬ (meaning t m 4822)) := by
  exact rule7902 (meaning t m 4381) (meaning t m 4823) (meaning t m 4824) (meaning t m 4825) (meaning t m 4826)

theorem rule7904 (p4381 p4823 p4824 p4825 p4826 : Prop) : (¬ (p4823 ∧ p4824 ∧ p4381 ∧ p4825 ∧ p4826)) ∨ (p4826) := by
  classical
  tauto

theorem initial7904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4822)) ∨ (meaning t m 4826) := by
  exact rule7904 (meaning t m 4381) (meaning t m 4823) (meaning t m 4824) (meaning t m 4825) (meaning t m 4826)

theorem rule7907 (p2761 p4828 p4829 p4830 p4831 : Prop) : (¬ (p4828 ∧ p4829 ∧ p2761 ∧ p4830 ∧ p4831)) ∨ (p4829) := by
  classical
  tauto

theorem initial7907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4827)) ∨ (meaning t m 4829) := by
  exact rule7907 (meaning t m 2761) (meaning t m 4828) (meaning t m 4829) (meaning t m 4830) (meaning t m 4831)

theorem rule7908 (p2761 p4828 p4829 p4830 p4831 : Prop) : (p2761) ∨ (¬ (p4828 ∧ p4829 ∧ p2761 ∧ p4830 ∧ p4831)) := by
  classical
  tauto

theorem initial7908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2761) ∨ (¬ (meaning t m 4827)) := by
  exact rule7908 (meaning t m 2761) (meaning t m 4828) (meaning t m 4829) (meaning t m 4830) (meaning t m 4831)

theorem rule7909 (p2761 p4828 p4829 p4830 p4831 : Prop) : (¬ (p4828 ∧ p4829 ∧ p2761 ∧ p4830 ∧ p4831)) ∨ (p4830) := by
  classical
  tauto

theorem initial7909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4827)) ∨ (meaning t m 4830) := by
  exact rule7909 (meaning t m 2761) (meaning t m 4828) (meaning t m 4829) (meaning t m 4830) (meaning t m 4831)

theorem rule7910 (p2761 p4828 p4829 p4830 p4831 : Prop) : (¬ (p4828 ∧ p4829 ∧ p2761 ∧ p4830 ∧ p4831)) ∨ (p4831) := by
  classical
  tauto

theorem initial7910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4827)) ∨ (meaning t m 4831) := by
  exact rule7910 (meaning t m 2761) (meaning t m 4828) (meaning t m 4829) (meaning t m 4830) (meaning t m 4831)

theorem rule7914 (p4822 p4827 : Prop) : (¬ (p4822 ∨ p4827)) ∨ (p4822) ∨ (p4827) := by
  classical
  tauto

theorem initial7914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4821)) ∨ (meaning t m 4822) ∨ (meaning t m 4827) := by
  exact rule7914 (meaning t m 4822) (meaning t m 4827)

theorem rule7915 (p2755 p4821 : Prop) (h : (p2755 ↔ p4821)) : (¬ p2755) ∨ (p4821) := by
  classical
  tauto

theorem initial7915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2755)) ∨ (meaning t m 4821) := by
  have source := ElevenTheory.theory1171 t (m.theta 7 10) (m.theta 7 9) (m.theta 9 10)
  exact rule7915 (meaning t m 2755) (meaning t m 4821) source

theorem rule7917 (p2027 p2299 p2396 p4261 p4443 p4832 : Prop) (h : (¬ p4832) ∨ (¬ p4261) ∨ p2027 ∨ (¬ p4443) ∨ (¬ p2299) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p4261) ∨ (¬ p4443) ∨ (¬ p4832) := by
  classical
  tauto

theorem initial7917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 4832)) := by
  have source := ElevenTheory.theory1172 t (m.theta 1 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule7917 (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 4261) (meaning t m 4443) (meaning t m 4832) source

theorem rule7920 (p2777 p2784 : Prop) : (p2777) ∨ (p2784) ∨ (¬ (p2777 ∨ p2784)) := by
  classical
  tauto

theorem initial7920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2777) ∨ (meaning t m 2784) ∨ (¬ (meaning t m 4833)) := by
  exact rule7920 (meaning t m 2777) (meaning t m 2784)

theorem rule7921 (p2768 p4833 : Prop) (h : (p2768 ↔ p4833)) : (¬ p2768) ∨ (p4833) := by
  classical
  tauto

theorem initial7921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2768)) ∨ (meaning t m 4833) := by
  have source := ElevenTheory.theory1173 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 6)
  exact rule7921 (meaning t m 2768) (meaning t m 4833) source

theorem rule7944 (p2027 p2745 p2774 p3365 p4154 p4328 : Prop) (h : (¬ p2745) ∨ (¬ p4154) ∨ (¬ p3365) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p4328)) : (p2027) ∨ (¬ p2745) ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p4154) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial7944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory1176 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6)
  exact rule7944 (meaning t m 2027) (meaning t m 2745) (meaning t m 2774) (meaning t m 3365) (meaning t m 4154) (meaning t m 4328) source

theorem rule7945 (p4195 p4337 p4841 p4842 p4843 : Prop) : (¬ (p4841 ∧ p4337 ∧ p4195 ∧ p4842 ∧ p4843)) ∨ (p4841) := by
  classical
  tauto

theorem initial7945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4840)) ∨ (meaning t m 4841) := by
  exact rule7945 (meaning t m 4195) (meaning t m 4337) (meaning t m 4841) (meaning t m 4842) (meaning t m 4843)

theorem rule7946 (p4195 p4337 p4841 p4842 p4843 : Prop) : (p4337) ∨ (¬ (p4841 ∧ p4337 ∧ p4195 ∧ p4842 ∧ p4843)) := by
  classical
  tauto

theorem initial7946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4337) ∨ (¬ (meaning t m 4840)) := by
  exact rule7946 (meaning t m 4195) (meaning t m 4337) (meaning t m 4841) (meaning t m 4842) (meaning t m 4843)

theorem rule7947 (p4195 p4337 p4841 p4842 p4843 : Prop) : (p4195) ∨ (¬ (p4841 ∧ p4337 ∧ p4195 ∧ p4842 ∧ p4843)) := by
  classical
  tauto

theorem initial7947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4195) ∨ (¬ (meaning t m 4840)) := by
  exact rule7947 (meaning t m 4195) (meaning t m 4337) (meaning t m 4841) (meaning t m 4842) (meaning t m 4843)

theorem rule7948 (p4195 p4337 p4841 p4842 p4843 : Prop) : (¬ (p4841 ∧ p4337 ∧ p4195 ∧ p4842 ∧ p4843)) ∨ (p4842) := by
  classical
  tauto

theorem initial7948 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4840)) ∨ (meaning t m 4842) := by
  exact rule7948 (meaning t m 4195) (meaning t m 4337) (meaning t m 4841) (meaning t m 4842) (meaning t m 4843)

theorem rule7949 (p4195 p4337 p4841 p4842 p4843 : Prop) : (¬ (p4841 ∧ p4337 ∧ p4195 ∧ p4842 ∧ p4843)) ∨ (p4843) := by
  classical
  tauto

theorem initial7949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4840)) ∨ (meaning t m 4843) := by
  exact rule7949 (meaning t m 4195) (meaning t m 4337) (meaning t m 4841) (meaning t m 4842) (meaning t m 4843)

theorem rule7951 (p2797 p4328 p4426 p4845 p4846 : Prop) : (p4328) ∨ (¬ (p4328 ∧ p4426 ∧ p2797 ∧ p4845 ∧ p4846)) := by
  classical
  tauto

theorem initial7951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4328) ∨ (¬ (meaning t m 4844)) := by
  exact rule7951 (meaning t m 2797) (meaning t m 4328) (meaning t m 4426) (meaning t m 4845) (meaning t m 4846)

theorem rule7952 (p2797 p4328 p4426 p4845 p4846 : Prop) : (p4426) ∨ (¬ (p4328 ∧ p4426 ∧ p2797 ∧ p4845 ∧ p4846)) := by
  classical
  tauto

theorem initial7952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4426) ∨ (¬ (meaning t m 4844)) := by
  exact rule7952 (meaning t m 2797) (meaning t m 4328) (meaning t m 4426) (meaning t m 4845) (meaning t m 4846)

theorem rule7953 (p2797 p4328 p4426 p4845 p4846 : Prop) : (p2797) ∨ (¬ (p4328 ∧ p4426 ∧ p2797 ∧ p4845 ∧ p4846)) := by
  classical
  tauto

theorem initial7953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2797) ∨ (¬ (meaning t m 4844)) := by
  exact rule7953 (meaning t m 2797) (meaning t m 4328) (meaning t m 4426) (meaning t m 4845) (meaning t m 4846)

theorem rule7954 (p2797 p4328 p4426 p4845 p4846 : Prop) : (¬ (p4328 ∧ p4426 ∧ p2797 ∧ p4845 ∧ p4846)) ∨ (p4845) := by
  classical
  tauto

theorem initial7954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4844)) ∨ (meaning t m 4845) := by
  exact rule7954 (meaning t m 2797) (meaning t m 4328) (meaning t m 4426) (meaning t m 4845) (meaning t m 4846)

theorem rule7955 (p2797 p4328 p4426 p4845 p4846 : Prop) : (¬ (p4328 ∧ p4426 ∧ p2797 ∧ p4845 ∧ p4846)) ∨ (p4846) := by
  classical
  tauto

theorem initial7955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4844)) ∨ (meaning t m 4846) := by
  exact rule7955 (meaning t m 2797) (meaning t m 4328) (meaning t m 4426) (meaning t m 4845) (meaning t m 4846)

end SunPrize.SMT
