import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory012
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule11941 (p2298 p3568 p4067 p4569 p4570 : Prop) : (p3568) ∨ (((¬ p2298) ∨ (¬ p3568) ∨ (¬ p4067) ∨ (¬ p4569) ∨ (¬ p4570))) := by
  classical
  tauto

theorem initial11941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3568) ∨ (meaning t m 5824) := by
  exact rule11941 (meaning t m 2298) (meaning t m 3568) (meaning t m 4067) (meaning t m 4569) (meaning t m 4570)

theorem rule11942 (p2298 p3568 p4067 p4569 p4570 : Prop) : (p4067) ∨ (((¬ p2298) ∨ (¬ p3568) ∨ (¬ p4067) ∨ (¬ p4569) ∨ (¬ p4570))) := by
  classical
  tauto

theorem initial11942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4067) ∨ (meaning t m 5824) := by
  exact rule11942 (meaning t m 2298) (meaning t m 3568) (meaning t m 4067) (meaning t m 4569) (meaning t m 4570)

theorem rule11943 (p2298 p3568 p4067 p4569 p4570 : Prop) : (p4569) ∨ (((¬ p2298) ∨ (¬ p3568) ∨ (¬ p4067) ∨ (¬ p4569) ∨ (¬ p4570))) := by
  classical
  tauto

theorem initial11943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4569) ∨ (meaning t m 5824) := by
  exact rule11943 (meaning t m 2298) (meaning t m 3568) (meaning t m 4067) (meaning t m 4569) (meaning t m 4570)

theorem rule11944 (p2298 p3568 p4067 p4569 p4570 : Prop) : (p4570) ∨ (((¬ p2298) ∨ (¬ p3568) ∨ (¬ p4067) ∨ (¬ p4569) ∨ (¬ p4570))) := by
  classical
  tauto

theorem initial11944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4570) ∨ (meaning t m 5824) := by
  exact rule11944 (meaning t m 2298) (meaning t m 3568) (meaning t m 4067) (meaning t m 4569) (meaning t m 4570)

theorem rule11946 (p2295 p3552 p4156 p4361 p4572 : Prop) : (p3552) ∨ (((¬ p3552) ∨ (¬ p4156) ∨ (¬ p2295) ∨ (¬ p4572) ∨ (¬ p4361))) := by
  classical
  tauto

theorem initial11946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3552) ∨ (meaning t m 5825) := by
  exact rule11946 (meaning t m 2295) (meaning t m 3552) (meaning t m 4156) (meaning t m 4361) (meaning t m 4572)

theorem rule11947 (p2295 p3552 p4156 p4361 p4572 : Prop) : (p4156) ∨ (((¬ p3552) ∨ (¬ p4156) ∨ (¬ p2295) ∨ (¬ p4572) ∨ (¬ p4361))) := by
  classical
  tauto

theorem initial11947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4156) ∨ (meaning t m 5825) := by
  exact rule11947 (meaning t m 2295) (meaning t m 3552) (meaning t m 4156) (meaning t m 4361) (meaning t m 4572)

theorem rule11948 (p2295 p3552 p4156 p4361 p4572 : Prop) : (p2295) ∨ (((¬ p3552) ∨ (¬ p4156) ∨ (¬ p2295) ∨ (¬ p4572) ∨ (¬ p4361))) := by
  classical
  tauto

theorem initial11948 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2295) ∨ (meaning t m 5825) := by
  exact rule11948 (meaning t m 2295) (meaning t m 3552) (meaning t m 4156) (meaning t m 4361) (meaning t m 4572)

theorem rule11949 (p2295 p3552 p4156 p4361 p4572 : Prop) : (p4572) ∨ (((¬ p3552) ∨ (¬ p4156) ∨ (¬ p2295) ∨ (¬ p4572) ∨ (¬ p4361))) := by
  classical
  tauto

theorem initial11949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4572) ∨ (meaning t m 5825) := by
  exact rule11949 (meaning t m 2295) (meaning t m 3552) (meaning t m 4156) (meaning t m 4361) (meaning t m 4572)

theorem rule11954 (p5824 p5825 : Prop) : (¬ ((¬ p5824) ∨ (¬ p5825))) ∨ (¬ p5824) ∨ (¬ p5825) := by
  classical
  tauto

theorem initial11954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5823)) ∨ (¬ (meaning t m 5824)) ∨ (¬ (meaning t m 5825)) := by
  exact rule11954 (meaning t m 5824) (meaning t m 5825)

theorem rule11955 (p4567 p5823 : Prop) (h : (p4567 ↔ p5823)) : (¬ p4567) ∨ (p5823) := by
  classical
  tauto

theorem initial11955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4567)) ∨ (meaning t m 5823) := by
  have source := ElevenTheory.theory3228 t (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule11955 (meaning t m 4567) (meaning t m 5823) source

theorem rule11957 (p2963 p3567 p3983 p4580 p4581 : Prop) : (p3567) ∨ (((¬ p3567) ∨ (¬ p3983) ∨ (¬ p2963) ∨ (¬ p4580) ∨ (¬ p4581))) := by
  classical
  tauto

theorem initial11957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3567) ∨ (meaning t m 5827) := by
  exact rule11957 (meaning t m 2963) (meaning t m 3567) (meaning t m 3983) (meaning t m 4580) (meaning t m 4581)

theorem rule11958 (p2963 p3567 p3983 p4580 p4581 : Prop) : (p3983) ∨ (((¬ p3567) ∨ (¬ p3983) ∨ (¬ p2963) ∨ (¬ p4580) ∨ (¬ p4581))) := by
  classical
  tauto

theorem initial11958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3983) ∨ (meaning t m 5827) := by
  exact rule11958 (meaning t m 2963) (meaning t m 3567) (meaning t m 3983) (meaning t m 4580) (meaning t m 4581)

theorem rule11959 (p2963 p3567 p3983 p4580 p4581 : Prop) : (p2963) ∨ (((¬ p3567) ∨ (¬ p3983) ∨ (¬ p2963) ∨ (¬ p4580) ∨ (¬ p4581))) := by
  classical
  tauto

theorem initial11959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2963) ∨ (meaning t m 5827) := by
  exact rule11959 (meaning t m 2963) (meaning t m 3567) (meaning t m 3983) (meaning t m 4580) (meaning t m 4581)

theorem rule11960 (p2963 p3567 p3983 p4580 p4581 : Prop) : (p4580) ∨ (((¬ p3567) ∨ (¬ p3983) ∨ (¬ p2963) ∨ (¬ p4580) ∨ (¬ p4581))) := by
  classical
  tauto

theorem initial11960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4580) ∨ (meaning t m 5827) := by
  exact rule11960 (meaning t m 2963) (meaning t m 3567) (meaning t m 3983) (meaning t m 4580) (meaning t m 4581)

theorem rule11963 (p2331 p2667 p3987 p4583 p4584 : Prop) : (p2667) ∨ (((¬ p2667) ∨ (¬ p2331) ∨ (¬ p3987) ∨ (¬ p4583) ∨ (¬ p4584))) := by
  classical
  tauto

theorem initial11963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2667) ∨ (meaning t m 5828) := by
  exact rule11963 (meaning t m 2331) (meaning t m 2667) (meaning t m 3987) (meaning t m 4583) (meaning t m 4584)

theorem rule11964 (p2331 p2667 p3987 p4583 p4584 : Prop) : (p2331) ∨ (((¬ p2667) ∨ (¬ p2331) ∨ (¬ p3987) ∨ (¬ p4583) ∨ (¬ p4584))) := by
  classical
  tauto

theorem initial11964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2331) ∨ (meaning t m 5828) := by
  exact rule11964 (meaning t m 2331) (meaning t m 2667) (meaning t m 3987) (meaning t m 4583) (meaning t m 4584)

theorem rule11965 (p2331 p2667 p3987 p4583 p4584 : Prop) : (p3987) ∨ (((¬ p2667) ∨ (¬ p2331) ∨ (¬ p3987) ∨ (¬ p4583) ∨ (¬ p4584))) := by
  classical
  tauto

theorem initial11965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3987) ∨ (meaning t m 5828) := by
  exact rule11965 (meaning t m 2331) (meaning t m 2667) (meaning t m 3987) (meaning t m 4583) (meaning t m 4584)

theorem rule11966 (p2331 p2667 p3987 p4583 p4584 : Prop) : (p4583) ∨ (((¬ p2667) ∨ (¬ p2331) ∨ (¬ p3987) ∨ (¬ p4583) ∨ (¬ p4584))) := by
  classical
  tauto

theorem initial11966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4583) ∨ (meaning t m 5828) := by
  exact rule11966 (meaning t m 2331) (meaning t m 2667) (meaning t m 3987) (meaning t m 4583) (meaning t m 4584)

theorem rule11971 (p5827 p5828 : Prop) : (¬ ((¬ p5827) ∨ (¬ p5828))) ∨ (¬ p5827) ∨ (¬ p5828) := by
  classical
  tauto

theorem initial11971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5826)) ∨ (¬ (meaning t m 5827)) ∨ (¬ (meaning t m 5828)) := by
  exact rule11971 (meaning t m 5827) (meaning t m 5828)

theorem rule11972 (p4578 p5826 : Prop) (h : (p4578 ↔ p5826)) : (¬ p4578) ∨ (p5826) := by
  classical
  tauto

theorem initial11972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4578)) ∨ (meaning t m 5826) := by
  have source := ElevenTheory.theory3229 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 6)
  exact rule11972 (meaning t m 4578) (meaning t m 5826) source

theorem rule11974 (p3551 p3960 p3961 p4587 p4588 : Prop) : (p3961) ∨ (((¬ p3961) ∨ (¬ p3960) ∨ (¬ p4587) ∨ (¬ p3551) ∨ (¬ p4588))) := by
  classical
  tauto

theorem initial11974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3961) ∨ (meaning t m 5830) := by
  exact rule11974 (meaning t m 3551) (meaning t m 3960) (meaning t m 3961) (meaning t m 4587) (meaning t m 4588)

theorem rule11975 (p3551 p3960 p3961 p4587 p4588 : Prop) : (p3960) ∨ (((¬ p3961) ∨ (¬ p3960) ∨ (¬ p4587) ∨ (¬ p3551) ∨ (¬ p4588))) := by
  classical
  tauto

theorem initial11975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3960) ∨ (meaning t m 5830) := by
  exact rule11975 (meaning t m 3551) (meaning t m 3960) (meaning t m 3961) (meaning t m 4587) (meaning t m 4588)

theorem rule11977 (p3551 p3960 p3961 p4587 p4588 : Prop) : (p3551) ∨ (((¬ p3961) ∨ (¬ p3960) ∨ (¬ p4587) ∨ (¬ p3551) ∨ (¬ p4588))) := by
  classical
  tauto

theorem initial11977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3551) ∨ (meaning t m 5830) := by
  exact rule11977 (meaning t m 3551) (meaning t m 3960) (meaning t m 3961) (meaning t m 4587) (meaning t m 4588)

theorem rule11978 (p3551 p3960 p3961 p4587 p4588 : Prop) : (p4588) ∨ (((¬ p3961) ∨ (¬ p3960) ∨ (¬ p4587) ∨ (¬ p3551) ∨ (¬ p4588))) := by
  classical
  tauto

theorem initial11978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4588) ∨ (meaning t m 5830) := by
  exact rule11978 (meaning t m 3551) (meaning t m 3960) (meaning t m 3961) (meaning t m 4587) (meaning t m 4588)

theorem rule11981 (p2341 p4403 p4590 p4591 p4592 : Prop) : (p4592) ∨ (((¬ p4591) ∨ (¬ p4592) ∨ (¬ p4403) ∨ (¬ p4590) ∨ (¬ p2341))) := by
  classical
  tauto

theorem initial11981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4592) ∨ (meaning t m 5831) := by
  exact rule11981 (meaning t m 2341) (meaning t m 4403) (meaning t m 4590) (meaning t m 4591) (meaning t m 4592)

theorem rule11982 (p2341 p4403 p4590 p4591 p4592 : Prop) : (p4403) ∨ (((¬ p4591) ∨ (¬ p4592) ∨ (¬ p4403) ∨ (¬ p4590) ∨ (¬ p2341))) := by
  classical
  tauto

theorem initial11982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4403) ∨ (meaning t m 5831) := by
  exact rule11982 (meaning t m 2341) (meaning t m 4403) (meaning t m 4590) (meaning t m 4591) (meaning t m 4592)

theorem rule11983 (p2341 p4403 p4590 p4591 p4592 : Prop) : (p4590) ∨ (((¬ p4591) ∨ (¬ p4592) ∨ (¬ p4403) ∨ (¬ p4590) ∨ (¬ p2341))) := by
  classical
  tauto

theorem initial11983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4590) ∨ (meaning t m 5831) := by
  exact rule11983 (meaning t m 2341) (meaning t m 4403) (meaning t m 4590) (meaning t m 4591) (meaning t m 4592)

theorem rule11984 (p2341 p4403 p4590 p4591 p4592 : Prop) : (p2341) ∨ (((¬ p4591) ∨ (¬ p4592) ∨ (¬ p4403) ∨ (¬ p4590) ∨ (¬ p2341))) := by
  classical
  tauto

theorem initial11984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2341) ∨ (meaning t m 5831) := by
  exact rule11984 (meaning t m 2341) (meaning t m 4403) (meaning t m 4590) (meaning t m 4591) (meaning t m 4592)

theorem rule11988 (p5830 p5831 : Prop) : (¬ ((¬ p5830) ∨ (¬ p5831))) ∨ (¬ p5830) ∨ (¬ p5831) := by
  classical
  tauto

theorem initial11988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5829)) ∨ (¬ (meaning t m 5830)) ∨ (¬ (meaning t m 5831)) := by
  exact rule11988 (meaning t m 5830) (meaning t m 5831)

theorem rule11989 (p4585 p5829 : Prop) (h : (p4585 ↔ p5829)) : (¬ p4585) ∨ (p5829) := by
  classical
  tauto

theorem initial11989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4585)) ∨ (meaning t m 5829) := by
  have source := ElevenTheory.theory3230 t (m.theta 0 7) (m.theta 0 8) (m.theta 7 8)
  exact rule11989 (meaning t m 4585) (meaning t m 5829) source

theorem rule11991 (p3573 p3956 p4432 p4595 p4596 : Prop) : (p4432) ∨ (((¬ p4432) ∨ (¬ p3956) ∨ (¬ p3573) ∨ (¬ p4595) ∨ (¬ p4596))) := by
  classical
  tauto

theorem initial11991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4432) ∨ (meaning t m 5833) := by
  exact rule11991 (meaning t m 3573) (meaning t m 3956) (meaning t m 4432) (meaning t m 4595) (meaning t m 4596)

theorem rule11992 (p3573 p3956 p4432 p4595 p4596 : Prop) : (p3956) ∨ (((¬ p4432) ∨ (¬ p3956) ∨ (¬ p3573) ∨ (¬ p4595) ∨ (¬ p4596))) := by
  classical
  tauto

theorem initial11992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3956) ∨ (meaning t m 5833) := by
  exact rule11992 (meaning t m 3573) (meaning t m 3956) (meaning t m 4432) (meaning t m 4595) (meaning t m 4596)

theorem rule11993 (p3573 p3956 p4432 p4595 p4596 : Prop) : (p3573) ∨ (((¬ p4432) ∨ (¬ p3956) ∨ (¬ p3573) ∨ (¬ p4595) ∨ (¬ p4596))) := by
  classical
  tauto

theorem initial11993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3573) ∨ (meaning t m 5833) := by
  exact rule11993 (meaning t m 3573) (meaning t m 3956) (meaning t m 4432) (meaning t m 4595) (meaning t m 4596)

theorem rule11994 (p3573 p3956 p4432 p4595 p4596 : Prop) : (p4595) ∨ (((¬ p4432) ∨ (¬ p3956) ∨ (¬ p3573) ∨ (¬ p4595) ∨ (¬ p4596))) := by
  classical
  tauto

theorem initial11994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4595) ∨ (meaning t m 5833) := by
  exact rule11994 (meaning t m 3573) (meaning t m 3956) (meaning t m 4432) (meaning t m 4595) (meaning t m 4596)

theorem rule11995 (p3573 p3956 p4432 p4595 p4596 : Prop) : (p4596) ∨ (((¬ p4432) ∨ (¬ p3956) ∨ (¬ p3573) ∨ (¬ p4595) ∨ (¬ p4596))) := by
  classical
  tauto

theorem initial11995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4596) ∨ (meaning t m 5833) := by
  exact rule11995 (meaning t m 3573) (meaning t m 3956) (meaning t m 4432) (meaning t m 4595) (meaning t m 4596)

theorem rule11997 (p2352 p2510 p4157 p4384 p4598 : Prop) : (p4157) ∨ (((¬ p4157) ∨ (¬ p2510) ∨ (¬ p2352) ∨ (¬ p4598) ∨ (¬ p4384))) := by
  classical
  tauto

theorem initial11997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4157) ∨ (meaning t m 5834) := by
  exact rule11997 (meaning t m 2352) (meaning t m 2510) (meaning t m 4157) (meaning t m 4384) (meaning t m 4598)

theorem rule11998 (p2352 p2510 p4157 p4384 p4598 : Prop) : (p2510) ∨ (((¬ p4157) ∨ (¬ p2510) ∨ (¬ p2352) ∨ (¬ p4598) ∨ (¬ p4384))) := by
  classical
  tauto

theorem initial11998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2510) ∨ (meaning t m 5834) := by
  exact rule11998 (meaning t m 2352) (meaning t m 2510) (meaning t m 4157) (meaning t m 4384) (meaning t m 4598)

theorem rule11999 (p2352 p2510 p4157 p4384 p4598 : Prop) : (p2352) ∨ (((¬ p4157) ∨ (¬ p2510) ∨ (¬ p2352) ∨ (¬ p4598) ∨ (¬ p4384))) := by
  classical
  tauto

theorem initial11999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2352) ∨ (meaning t m 5834) := by
  exact rule11999 (meaning t m 2352) (meaning t m 2510) (meaning t m 4157) (meaning t m 4384) (meaning t m 4598)

theorem rule12000 (p2352 p2510 p4157 p4384 p4598 : Prop) : (p4598) ∨ (((¬ p4157) ∨ (¬ p2510) ∨ (¬ p2352) ∨ (¬ p4598) ∨ (¬ p4384))) := by
  classical
  tauto

theorem initial12000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4598) ∨ (meaning t m 5834) := by
  exact rule12000 (meaning t m 2352) (meaning t m 2510) (meaning t m 4157) (meaning t m 4384) (meaning t m 4598)

theorem rule12005 (p5833 p5834 : Prop) : (¬ ((¬ p5833) ∨ (¬ p5834))) ∨ (¬ p5833) ∨ (¬ p5834) := by
  classical
  tauto

theorem initial12005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5832)) ∨ (¬ (meaning t m 5833)) ∨ (¬ (meaning t m 5834)) := by
  exact rule12005 (meaning t m 5833) (meaning t m 5834)

theorem rule12006 (p4593 p5832 : Prop) (h : (p4593 ↔ p5832)) : (¬ p4593) ∨ (p5832) := by
  classical
  tauto

theorem initial12006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4593)) ∨ (meaning t m 5832) := by
  have source := ElevenTheory.theory3231 t (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule12006 (meaning t m 4593) (meaning t m 5832) source

theorem rule12008 (p1975 p2027 p2233 p2274 p2352 p2573 p3989 : Prop) (h : (¬ p2573) ∨ (¬ p2274) ∨ p2027 ∨ p2233 ∨ (¬ p3989) ∨ (¬ p1975) ∨ (¬ p2352)) : (¬ p1975) ∨ (p2027) ∨ (p2233) ∨ (¬ p2274) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial12008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory3232 t (m.theta 0 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule12008 (meaning t m 1975) (meaning t m 2027) (meaning t m 2233) (meaning t m 2274) (meaning t m 2352) (meaning t m 2573) (meaning t m 3989) source

theorem rule12009 (p1980 p2355 p3568 p4361 : Prop) (h : (¬ p1980) ∨ p4361 ∨ (¬ p3568) ∨ p2355) : (¬ p1980) ∨ (p2355) ∨ (¬ p3568) ∨ (p4361) := by
  classical
  tauto

theorem initial12009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 3568)) ∨ (meaning t m 4361) := by
  have source := ElevenTheory.theory3233 t (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule12009 (meaning t m 1980) (meaning t m 2355) (meaning t m 3568) (meaning t m 4361) source

theorem rule12010 (p3322 p4171 p4330 p4347 p4601 : Prop) : (p4171) ∨ (((¬ p4171) ∨ (¬ p4347) ∨ (¬ p3322) ∨ (¬ p4601) ∨ (¬ p4330))) := by
  classical
  tauto

theorem initial12010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4171) ∨ (meaning t m 5836) := by
  exact rule12010 (meaning t m 3322) (meaning t m 4171) (meaning t m 4330) (meaning t m 4347) (meaning t m 4601)

theorem rule12011 (p3322 p4171 p4330 p4347 p4601 : Prop) : (p4347) ∨ (((¬ p4171) ∨ (¬ p4347) ∨ (¬ p3322) ∨ (¬ p4601) ∨ (¬ p4330))) := by
  classical
  tauto

theorem initial12011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4347) ∨ (meaning t m 5836) := by
  exact rule12011 (meaning t m 3322) (meaning t m 4171) (meaning t m 4330) (meaning t m 4347) (meaning t m 4601)

theorem rule12012 (p3322 p4171 p4330 p4347 p4601 : Prop) : (p3322) ∨ (((¬ p4171) ∨ (¬ p4347) ∨ (¬ p3322) ∨ (¬ p4601) ∨ (¬ p4330))) := by
  classical
  tauto

theorem initial12012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3322) ∨ (meaning t m 5836) := by
  exact rule12012 (meaning t m 3322) (meaning t m 4171) (meaning t m 4330) (meaning t m 4347) (meaning t m 4601)

theorem rule12016 (p2363 p3990 p4345 p4603 p4604 : Prop) : (p4345) ∨ (((¬ p4345) ∨ (¬ p3990) ∨ (¬ p2363) ∨ (¬ p4603) ∨ (¬ p4604))) := by
  classical
  tauto

theorem initial12016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4345) ∨ (meaning t m 5837) := by
  exact rule12016 (meaning t m 2363) (meaning t m 3990) (meaning t m 4345) (meaning t m 4603) (meaning t m 4604)

theorem rule12017 (p2363 p3990 p4345 p4603 p4604 : Prop) : (p3990) ∨ (((¬ p4345) ∨ (¬ p3990) ∨ (¬ p2363) ∨ (¬ p4603) ∨ (¬ p4604))) := by
  classical
  tauto

theorem initial12017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3990) ∨ (meaning t m 5837) := by
  exact rule12017 (meaning t m 2363) (meaning t m 3990) (meaning t m 4345) (meaning t m 4603) (meaning t m 4604)

theorem rule12018 (p2363 p3990 p4345 p4603 p4604 : Prop) : (p2363) ∨ (((¬ p4345) ∨ (¬ p3990) ∨ (¬ p2363) ∨ (¬ p4603) ∨ (¬ p4604))) := by
  classical
  tauto

theorem initial12018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2363) ∨ (meaning t m 5837) := by
  exact rule12018 (meaning t m 2363) (meaning t m 3990) (meaning t m 4345) (meaning t m 4603) (meaning t m 4604)

theorem rule12019 (p2363 p3990 p4345 p4603 p4604 : Prop) : (p4603) ∨ (((¬ p4345) ∨ (¬ p3990) ∨ (¬ p2363) ∨ (¬ p4603) ∨ (¬ p4604))) := by
  classical
  tauto

theorem initial12019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4603) ∨ (meaning t m 5837) := by
  exact rule12019 (meaning t m 2363) (meaning t m 3990) (meaning t m 4345) (meaning t m 4603) (meaning t m 4604)

theorem rule12024 (p5836 p5837 : Prop) : (¬ ((¬ p5836) ∨ (¬ p5837))) ∨ (¬ p5836) ∨ (¬ p5837) := by
  classical
  tauto

theorem initial12024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5835)) ∨ (¬ (meaning t m 5836)) ∨ (¬ (meaning t m 5837)) := by
  exact rule12024 (meaning t m 5836) (meaning t m 5837)

theorem rule12025 (p4599 p5835 : Prop) (h : (p4599 ↔ p5835)) : (¬ p4599) ∨ (p5835) := by
  classical
  tauto

theorem initial12025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4599)) ∨ (meaning t m 5835) := by
  have source := ElevenTheory.theory3234 t (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule12025 (meaning t m 4599) (meaning t m 5835) source

theorem rule12027 (p1981 p2027 p2230 p2233 p2373 p3146 p4347 : Prop) (h : p2027 ∨ p2233 ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4347) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial12027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3235 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule12027 (meaning t m 1981) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2373) (meaning t m 3146) (meaning t m 4347) source

theorem rule12028 (p1982 p2027 p2187 p2230 p2233 p2363 p2563 : Prop) (h : (¬ p2563) ∨ p2027 ∨ p2233 ∨ (¬ p2230) ∨ (¬ p2363) ∨ (¬ p2187) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2363) ∨ (¬ p2563) := by
  classical
  tauto

theorem initial12028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2563)) := by
  have source := ElevenTheory.theory3236 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule12028 (meaning t m 1982) (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2233) (meaning t m 2363) (meaning t m 2563) source

theorem rule12029 (p3693 p3880 p4158 p4607 p4608 : Prop) : (p3693) ∨ (((¬ p3693) ∨ (¬ p3880) ∨ (¬ p4607) ∨ (¬ p4608) ∨ (¬ p4158))) := by
  classical
  tauto

theorem initial12029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3693) ∨ (meaning t m 5839) := by
  exact rule12029 (meaning t m 3693) (meaning t m 3880) (meaning t m 4158) (meaning t m 4607) (meaning t m 4608)

theorem rule12030 (p3693 p3880 p4158 p4607 p4608 : Prop) : (p3880) ∨ (((¬ p3693) ∨ (¬ p3880) ∨ (¬ p4607) ∨ (¬ p4608) ∨ (¬ p4158))) := by
  classical
  tauto

theorem initial12030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3880) ∨ (meaning t m 5839) := by
  exact rule12030 (meaning t m 3693) (meaning t m 3880) (meaning t m 4158) (meaning t m 4607) (meaning t m 4608)

theorem rule12031 (p3693 p3880 p4158 p4607 p4608 : Prop) : (p4607) ∨ (((¬ p3693) ∨ (¬ p3880) ∨ (¬ p4607) ∨ (¬ p4608) ∨ (¬ p4158))) := by
  classical
  tauto

theorem initial12031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4607) ∨ (meaning t m 5839) := by
  exact rule12031 (meaning t m 3693) (meaning t m 3880) (meaning t m 4158) (meaning t m 4607) (meaning t m 4608)

theorem rule12035 (p2373 p2531 p4355 p4434 p4610 : Prop) : (p2531) ∨ (((¬ p2531) ∨ (¬ p4355) ∨ (¬ p2373) ∨ (¬ p4610) ∨ (¬ p4434))) := by
  classical
  tauto

theorem initial12035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2531) ∨ (meaning t m 5840) := by
  exact rule12035 (meaning t m 2373) (meaning t m 2531) (meaning t m 4355) (meaning t m 4434) (meaning t m 4610)

theorem rule12036 (p2373 p2531 p4355 p4434 p4610 : Prop) : (p4355) ∨ (((¬ p2531) ∨ (¬ p4355) ∨ (¬ p2373) ∨ (¬ p4610) ∨ (¬ p4434))) := by
  classical
  tauto

theorem initial12036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4355) ∨ (meaning t m 5840) := by
  exact rule12036 (meaning t m 2373) (meaning t m 2531) (meaning t m 4355) (meaning t m 4434) (meaning t m 4610)

theorem rule12037 (p2373 p2531 p4355 p4434 p4610 : Prop) : (p2373) ∨ (((¬ p2531) ∨ (¬ p4355) ∨ (¬ p2373) ∨ (¬ p4610) ∨ (¬ p4434))) := by
  classical
  tauto

theorem initial12037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2373) ∨ (meaning t m 5840) := by
  exact rule12037 (meaning t m 2373) (meaning t m 2531) (meaning t m 4355) (meaning t m 4434) (meaning t m 4610)

theorem rule12038 (p2373 p2531 p4355 p4434 p4610 : Prop) : (p4610) ∨ (((¬ p2531) ∨ (¬ p4355) ∨ (¬ p2373) ∨ (¬ p4610) ∨ (¬ p4434))) := by
  classical
  tauto

theorem initial12038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4610) ∨ (meaning t m 5840) := by
  exact rule12038 (meaning t m 2373) (meaning t m 2531) (meaning t m 4355) (meaning t m 4434) (meaning t m 4610)

theorem rule12043 (p5839 p5840 : Prop) : (¬ ((¬ p5839) ∨ (¬ p5840))) ∨ (¬ p5839) ∨ (¬ p5840) := by
  classical
  tauto

theorem initial12043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5838)) ∨ (¬ (meaning t m 5839)) ∨ (¬ (meaning t m 5840)) := by
  exact rule12043 (meaning t m 5839) (meaning t m 5840)

theorem rule12044 (p4605 p5838 : Prop) (h : (p4605 ↔ p5838)) : (¬ p4605) ∨ (p5838) := by
  classical
  tauto

theorem initial12044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4605)) ∨ (meaning t m 5838) := by
  have source := ElevenTheory.theory3237 t (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule12044 (meaning t m 4605) (meaning t m 5838) source

theorem rule12046 (p2387 p4170 p4197 p4613 p4614 : Prop) : (p4170) ∨ (((¬ p4170) ∨ (¬ p2387) ∨ (¬ p4197) ∨ (¬ p4613) ∨ (¬ p4614))) := by
  classical
  tauto

theorem initial12046 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4170) ∨ (meaning t m 5842) := by
  exact rule12046 (meaning t m 2387) (meaning t m 4170) (meaning t m 4197) (meaning t m 4613) (meaning t m 4614)

theorem rule12047 (p2387 p4170 p4197 p4613 p4614 : Prop) : (p2387) ∨ (((¬ p4170) ∨ (¬ p2387) ∨ (¬ p4197) ∨ (¬ p4613) ∨ (¬ p4614))) := by
  classical
  tauto

theorem initial12047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2387) ∨ (meaning t m 5842) := by
  exact rule12047 (meaning t m 2387) (meaning t m 4170) (meaning t m 4197) (meaning t m 4613) (meaning t m 4614)

theorem rule12048 (p2387 p4170 p4197 p4613 p4614 : Prop) : (p4197) ∨ (((¬ p4170) ∨ (¬ p2387) ∨ (¬ p4197) ∨ (¬ p4613) ∨ (¬ p4614))) := by
  classical
  tauto

theorem initial12048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4197) ∨ (meaning t m 5842) := by
  exact rule12048 (meaning t m 2387) (meaning t m 4170) (meaning t m 4197) (meaning t m 4613) (meaning t m 4614)

theorem rule12050 (p2387 p4170 p4197 p4613 p4614 : Prop) : (p4614) ∨ (((¬ p4170) ∨ (¬ p2387) ∨ (¬ p4197) ∨ (¬ p4613) ∨ (¬ p4614))) := by
  classical
  tauto

theorem initial12050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4614) ∨ (meaning t m 5842) := by
  exact rule12050 (meaning t m 2387) (meaning t m 4170) (meaning t m 4197) (meaning t m 4613) (meaning t m 4614)

theorem rule12052 (p2383 p4113 p4114 p4616 p4617 : Prop) : (p4617) ∨ (((¬ p4617) ∨ (¬ p2383) ∨ (¬ p4616) ∨ (¬ p4114) ∨ (¬ p4113))) := by
  classical
  tauto

theorem initial12052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4617) ∨ (meaning t m 5843) := by
  exact rule12052 (meaning t m 2383) (meaning t m 4113) (meaning t m 4114) (meaning t m 4616) (meaning t m 4617)

theorem rule12053 (p2383 p4113 p4114 p4616 p4617 : Prop) : (p2383) ∨ (((¬ p4617) ∨ (¬ p2383) ∨ (¬ p4616) ∨ (¬ p4114) ∨ (¬ p4113))) := by
  classical
  tauto

theorem initial12053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2383) ∨ (meaning t m 5843) := by
  exact rule12053 (meaning t m 2383) (meaning t m 4113) (meaning t m 4114) (meaning t m 4616) (meaning t m 4617)

theorem rule12055 (p2383 p4113 p4114 p4616 p4617 : Prop) : (p4114) ∨ (((¬ p4617) ∨ (¬ p2383) ∨ (¬ p4616) ∨ (¬ p4114) ∨ (¬ p4113))) := by
  classical
  tauto

theorem initial12055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4114) ∨ (meaning t m 5843) := by
  exact rule12055 (meaning t m 2383) (meaning t m 4113) (meaning t m 4114) (meaning t m 4616) (meaning t m 4617)

theorem rule12056 (p2383 p4113 p4114 p4616 p4617 : Prop) : (p4113) ∨ (((¬ p4617) ∨ (¬ p2383) ∨ (¬ p4616) ∨ (¬ p4114) ∨ (¬ p4113))) := by
  classical
  tauto

theorem initial12056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4113) ∨ (meaning t m 5843) := by
  exact rule12056 (meaning t m 2383) (meaning t m 4113) (meaning t m 4114) (meaning t m 4616) (meaning t m 4617)

theorem rule12060 (p5842 p5843 : Prop) : (¬ ((¬ p5842) ∨ (¬ p5843))) ∨ (¬ p5842) ∨ (¬ p5843) := by
  classical
  tauto

theorem initial12060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5841)) ∨ (¬ (meaning t m 5842)) ∨ (¬ (meaning t m 5843)) := by
  exact rule12060 (meaning t m 5842) (meaning t m 5843)

theorem rule12061 (p4611 p5841 : Prop) (h : (p4611 ↔ p5841)) : (¬ p4611) ∨ (p5841) := by
  classical
  tauto

theorem initial12061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4611)) ∨ (meaning t m 5841) := by
  have source := ElevenTheory.theory3238 t (m.theta 0 6) (m.theta 0 8) (m.theta 6 8)
  exact rule12061 (meaning t m 4611) (meaning t m 5841) source

theorem rule12063 (p1975 p2027 p2187 p2284 p2388 p2553 p3956 : Prop) (h : p2027 ∨ p2388 ∨ (¬ p3956) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p1975) ∨ (¬ p2553)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p2553) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial12063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory3239 t (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule12063 (meaning t m 1975) (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 2388) (meaning t m 2553) (meaning t m 3956) source

theorem rule12064 (p4025 p4107 p4396 p4620 p4621 : Prop) : (p4396) ∨ (((¬ p4396) ∨ (¬ p4107) ∨ (¬ p4025) ∨ (¬ p4620) ∨ (¬ p4621))) := by
  classical
  tauto

theorem initial12064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4396) ∨ (meaning t m 5845) := by
  exact rule12064 (meaning t m 4025) (meaning t m 4107) (meaning t m 4396) (meaning t m 4620) (meaning t m 4621)

theorem rule12065 (p4025 p4107 p4396 p4620 p4621 : Prop) : (p4107) ∨ (((¬ p4396) ∨ (¬ p4107) ∨ (¬ p4025) ∨ (¬ p4620) ∨ (¬ p4621))) := by
  classical
  tauto

theorem initial12065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4107) ∨ (meaning t m 5845) := by
  exact rule12065 (meaning t m 4025) (meaning t m 4107) (meaning t m 4396) (meaning t m 4620) (meaning t m 4621)

theorem rule12066 (p4025 p4107 p4396 p4620 p4621 : Prop) : (p4025) ∨ (((¬ p4396) ∨ (¬ p4107) ∨ (¬ p4025) ∨ (¬ p4620) ∨ (¬ p4621))) := by
  classical
  tauto

theorem initial12066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4025) ∨ (meaning t m 5845) := by
  exact rule12066 (meaning t m 4025) (meaning t m 4107) (meaning t m 4396) (meaning t m 4620) (meaning t m 4621)

theorem rule12067 (p4025 p4107 p4396 p4620 p4621 : Prop) : (p4620) ∨ (((¬ p4396) ∨ (¬ p4107) ∨ (¬ p4025) ∨ (¬ p4620) ∨ (¬ p4621))) := by
  classical
  tauto

theorem initial12067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4620) ∨ (meaning t m 5845) := by
  exact rule12067 (meaning t m 4025) (meaning t m 4107) (meaning t m 4396) (meaning t m 4620) (meaning t m 4621)

theorem rule12070 (p2396 p4187 p4623 p4624 p4625 : Prop) : (p4623) ∨ (((¬ p4623) ∨ (¬ p4187) ∨ (¬ p2396) ∨ (¬ p4624) ∨ (¬ p4625))) := by
  classical
  tauto

theorem initial12070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4623) ∨ (meaning t m 5846) := by
  exact rule12070 (meaning t m 2396) (meaning t m 4187) (meaning t m 4623) (meaning t m 4624) (meaning t m 4625)

theorem rule12071 (p2396 p4187 p4623 p4624 p4625 : Prop) : (p4187) ∨ (((¬ p4623) ∨ (¬ p4187) ∨ (¬ p2396) ∨ (¬ p4624) ∨ (¬ p4625))) := by
  classical
  tauto

theorem initial12071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4187) ∨ (meaning t m 5846) := by
  exact rule12071 (meaning t m 2396) (meaning t m 4187) (meaning t m 4623) (meaning t m 4624) (meaning t m 4625)

theorem rule12072 (p2396 p4187 p4623 p4624 p4625 : Prop) : (p2396) ∨ (((¬ p4623) ∨ (¬ p4187) ∨ (¬ p2396) ∨ (¬ p4624) ∨ (¬ p4625))) := by
  classical
  tauto

theorem initial12072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2396) ∨ (meaning t m 5846) := by
  exact rule12072 (meaning t m 2396) (meaning t m 4187) (meaning t m 4623) (meaning t m 4624) (meaning t m 4625)

theorem rule12078 (p5845 p5846 : Prop) : (¬ ((¬ p5845) ∨ (¬ p5846))) ∨ (¬ p5845) ∨ (¬ p5846) := by
  classical
  tauto

theorem initial12078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5844)) ∨ (¬ (meaning t m 5845)) ∨ (¬ (meaning t m 5846)) := by
  exact rule12078 (meaning t m 5845) (meaning t m 5846)

theorem rule12079 (p4618 p5844 : Prop) (h : (p4618 ↔ p5844)) : (¬ p4618) ∨ (p5844) := by
  classical
  tauto

theorem initial12079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4618)) ∨ (meaning t m 5844) := by
  have source := ElevenTheory.theory3240 t (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule12079 (meaning t m 4618) (meaning t m 5844) source

theorem rule12081 (p1983 p2027 p2202 p2396 p2553 p2573 p3238 p3519 : Prop) (h : (¬ p1983) ∨ p2202 ∨ (¬ p3238) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p3519) ∨ (¬ p2553) ∨ (¬ p2396)) : (¬ p1983) ∨ (p2027) ∨ (p2202) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3238) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial12081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory3241 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule12081 (meaning t m 1983) (meaning t m 2027) (meaning t m 2202) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 3238) (meaning t m 3519) source

theorem rule12082 (p3238 p4034 p4202 p4628 p4629 : Prop) : (p4202) ∨ (((¬ p4202) ∨ (¬ p4034) ∨ (¬ p3238) ∨ (¬ p4629) ∨ (¬ p4628))) := by
  classical
  tauto

theorem initial12082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4202) ∨ (meaning t m 5848) := by
  exact rule12082 (meaning t m 3238) (meaning t m 4034) (meaning t m 4202) (meaning t m 4628) (meaning t m 4629)

theorem rule12083 (p3238 p4034 p4202 p4628 p4629 : Prop) : (p4034) ∨ (((¬ p4202) ∨ (¬ p4034) ∨ (¬ p3238) ∨ (¬ p4629) ∨ (¬ p4628))) := by
  classical
  tauto

theorem initial12083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4034) ∨ (meaning t m 5848) := by
  exact rule12083 (meaning t m 3238) (meaning t m 4034) (meaning t m 4202) (meaning t m 4628) (meaning t m 4629)

theorem rule12084 (p3238 p4034 p4202 p4628 p4629 : Prop) : (p3238) ∨ (((¬ p4202) ∨ (¬ p4034) ∨ (¬ p3238) ∨ (¬ p4629) ∨ (¬ p4628))) := by
  classical
  tauto

theorem initial12084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3238) ∨ (meaning t m 5848) := by
  exact rule12084 (meaning t m 3238) (meaning t m 4034) (meaning t m 4202) (meaning t m 4628) (meaning t m 4629)

theorem rule12085 (p3238 p4034 p4202 p4628 p4629 : Prop) : (p4629) ∨ (((¬ p4202) ∨ (¬ p4034) ∨ (¬ p3238) ∨ (¬ p4629) ∨ (¬ p4628))) := by
  classical
  tauto

theorem initial12085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4629) ∨ (meaning t m 5848) := by
  exact rule12085 (meaning t m 3238) (meaning t m 4034) (meaning t m 4202) (meaning t m 4628) (meaning t m 4629)

theorem rule12088 (p2406 p3948 p4210 p4631 p4632 : Prop) : (p4210) ∨ (((¬ p4210) ∨ (¬ p3948) ∨ (¬ p4632) ∨ (¬ p2406) ∨ (¬ p4631))) := by
  classical
  tauto

theorem initial12088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4210) ∨ (meaning t m 5849) := by
  exact rule12088 (meaning t m 2406) (meaning t m 3948) (meaning t m 4210) (meaning t m 4631) (meaning t m 4632)

theorem rule12089 (p2406 p3948 p4210 p4631 p4632 : Prop) : (p3948) ∨ (((¬ p4210) ∨ (¬ p3948) ∨ (¬ p4632) ∨ (¬ p2406) ∨ (¬ p4631))) := by
  classical
  tauto

theorem initial12089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3948) ∨ (meaning t m 5849) := by
  exact rule12089 (meaning t m 2406) (meaning t m 3948) (meaning t m 4210) (meaning t m 4631) (meaning t m 4632)

theorem rule12091 (p2406 p3948 p4210 p4631 p4632 : Prop) : (p2406) ∨ (((¬ p4210) ∨ (¬ p3948) ∨ (¬ p4632) ∨ (¬ p2406) ∨ (¬ p4631))) := by
  classical
  tauto

theorem initial12091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2406) ∨ (meaning t m 5849) := by
  exact rule12091 (meaning t m 2406) (meaning t m 3948) (meaning t m 4210) (meaning t m 4631) (meaning t m 4632)

theorem rule12096 (p5848 p5849 : Prop) : (¬ ((¬ p5848) ∨ (¬ p5849))) ∨ (¬ p5848) ∨ (¬ p5849) := by
  classical
  tauto

theorem initial12096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5847)) ∨ (¬ (meaning t m 5848)) ∨ (¬ (meaning t m 5849)) := by
  exact rule12096 (meaning t m 5848) (meaning t m 5849)

theorem rule12097 (p4626 p5847 : Prop) (h : (p4626 ↔ p5847)) : (¬ p4626) ∨ (p5847) := by
  classical
  tauto

theorem initial12097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4626)) ∨ (meaning t m 5847) := by
  have source := ElevenTheory.theory3242 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5)
  exact rule12097 (meaning t m 4626) (meaning t m 5847) source

theorem rule12099 (p1981 p2027 p2187 p2406 p2409 p2573 p2589 p4203 : Prop) (h : (¬ p2187) ∨ p2409 ∨ (¬ p2406) ∨ (¬ p4203) ∨ (¬ p1981) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2573)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial12099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory3243 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule12099 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2406) (meaning t m 2409) (meaning t m 2573) (meaning t m 2589) (meaning t m 4203) source

theorem rule12100 (p4278 p4635 p4636 p4637 p4638 : Prop) : (p4636) ∨ (((¬ p4636) ∨ (¬ p4278) ∨ (¬ p4635) ∨ (¬ p4637) ∨ (¬ p4638))) := by
  classical
  tauto

theorem initial12100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4636) ∨ (meaning t m 5851) := by
  exact rule12100 (meaning t m 4278) (meaning t m 4635) (meaning t m 4636) (meaning t m 4637) (meaning t m 4638)

theorem rule12101 (p4278 p4635 p4636 p4637 p4638 : Prop) : (p4278) ∨ (((¬ p4636) ∨ (¬ p4278) ∨ (¬ p4635) ∨ (¬ p4637) ∨ (¬ p4638))) := by
  classical
  tauto

theorem initial12101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4278) ∨ (meaning t m 5851) := by
  exact rule12101 (meaning t m 4278) (meaning t m 4635) (meaning t m 4636) (meaning t m 4637) (meaning t m 4638)

theorem rule12102 (p4278 p4635 p4636 p4637 p4638 : Prop) : (p4635) ∨ (((¬ p4636) ∨ (¬ p4278) ∨ (¬ p4635) ∨ (¬ p4637) ∨ (¬ p4638))) := by
  classical
  tauto

theorem initial12102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4635) ∨ (meaning t m 5851) := by
  exact rule12102 (meaning t m 4278) (meaning t m 4635) (meaning t m 4636) (meaning t m 4637) (meaning t m 4638)

theorem rule12103 (p4278 p4635 p4636 p4637 p4638 : Prop) : (p4637) ∨ (((¬ p4636) ∨ (¬ p4278) ∨ (¬ p4635) ∨ (¬ p4637) ∨ (¬ p4638))) := by
  classical
  tauto

theorem initial12103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4637) ∨ (meaning t m 5851) := by
  exact rule12103 (meaning t m 4278) (meaning t m 4635) (meaning t m 4636) (meaning t m 4637) (meaning t m 4638)

theorem rule12106 (p2417 p3192 p4451 p4640 p4641 : Prop) : (p4451) ∨ (((¬ p4451) ∨ (¬ p3192) ∨ (¬ p2417) ∨ (¬ p4640) ∨ (¬ p4641))) := by
  classical
  tauto

theorem initial12106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4451) ∨ (meaning t m 5852) := by
  exact rule12106 (meaning t m 2417) (meaning t m 3192) (meaning t m 4451) (meaning t m 4640) (meaning t m 4641)

theorem rule12107 (p2417 p3192 p4451 p4640 p4641 : Prop) : (p3192) ∨ (((¬ p4451) ∨ (¬ p3192) ∨ (¬ p2417) ∨ (¬ p4640) ∨ (¬ p4641))) := by
  classical
  tauto

theorem initial12107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3192) ∨ (meaning t m 5852) := by
  exact rule12107 (meaning t m 2417) (meaning t m 3192) (meaning t m 4451) (meaning t m 4640) (meaning t m 4641)

theorem rule12108 (p2417 p3192 p4451 p4640 p4641 : Prop) : (p2417) ∨ (((¬ p4451) ∨ (¬ p3192) ∨ (¬ p2417) ∨ (¬ p4640) ∨ (¬ p4641))) := by
  classical
  tauto

theorem initial12108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2417) ∨ (meaning t m 5852) := by
  exact rule12108 (meaning t m 2417) (meaning t m 3192) (meaning t m 4451) (meaning t m 4640) (meaning t m 4641)

theorem rule12110 (p2417 p3192 p4451 p4640 p4641 : Prop) : (p4641) ∨ (((¬ p4451) ∨ (¬ p3192) ∨ (¬ p2417) ∨ (¬ p4640) ∨ (¬ p4641))) := by
  classical
  tauto

theorem initial12110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4641) ∨ (meaning t m 5852) := by
  exact rule12110 (meaning t m 2417) (meaning t m 3192) (meaning t m 4451) (meaning t m 4640) (meaning t m 4641)

theorem rule12114 (p5851 p5852 : Prop) : (¬ ((¬ p5851) ∨ (¬ p5852))) ∨ (¬ p5851) ∨ (¬ p5852) := by
  classical
  tauto

theorem initial12114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5850)) ∨ (¬ (meaning t m 5851)) ∨ (¬ (meaning t m 5852)) := by
  exact rule12114 (meaning t m 5851) (meaning t m 5852)

theorem rule12115 (p4633 p5850 : Prop) (h : (p4633 ↔ p5850)) : (¬ p4633) ∨ (p5850) := by
  classical
  tauto

theorem initial12115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4633)) ∨ (meaning t m 5850) := by
  have source := ElevenTheory.theory3244 t (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule12115 (meaning t m 4633) (meaning t m 5850) source

theorem rule12117 (p2441 p4001 p4235 p4277 p4644 : Prop) : (p4001) ∨ (((¬ p4001) ∨ (¬ p4235) ∨ (¬ p2441) ∨ (¬ p4644) ∨ (¬ p4277))) := by
  classical
  tauto

theorem initial12117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4001) ∨ (meaning t m 5854) := by
  exact rule12117 (meaning t m 2441) (meaning t m 4001) (meaning t m 4235) (meaning t m 4277) (meaning t m 4644)

theorem rule12118 (p2441 p4001 p4235 p4277 p4644 : Prop) : (p4235) ∨ (((¬ p4001) ∨ (¬ p4235) ∨ (¬ p2441) ∨ (¬ p4644) ∨ (¬ p4277))) := by
  classical
  tauto

theorem initial12118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4235) ∨ (meaning t m 5854) := by
  exact rule12118 (meaning t m 2441) (meaning t m 4001) (meaning t m 4235) (meaning t m 4277) (meaning t m 4644)

theorem rule12119 (p2441 p4001 p4235 p4277 p4644 : Prop) : (p2441) ∨ (((¬ p4001) ∨ (¬ p4235) ∨ (¬ p2441) ∨ (¬ p4644) ∨ (¬ p4277))) := by
  classical
  tauto

theorem initial12119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2441) ∨ (meaning t m 5854) := by
  exact rule12119 (meaning t m 2441) (meaning t m 4001) (meaning t m 4235) (meaning t m 4277) (meaning t m 4644)

theorem rule12123 (p2427 p3569 p3741 p4646 p4647 : Prop) : (p3569) ∨ (((¬ p3569) ∨ (¬ p3741) ∨ (¬ p2427) ∨ (¬ p4646) ∨ (¬ p4647))) := by
  classical
  tauto

theorem initial12123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3569) ∨ (meaning t m 5855) := by
  exact rule12123 (meaning t m 2427) (meaning t m 3569) (meaning t m 3741) (meaning t m 4646) (meaning t m 4647)

theorem rule12124 (p2427 p3569 p3741 p4646 p4647 : Prop) : (p3741) ∨ (((¬ p3569) ∨ (¬ p3741) ∨ (¬ p2427) ∨ (¬ p4646) ∨ (¬ p4647))) := by
  classical
  tauto

theorem initial12124 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3741) ∨ (meaning t m 5855) := by
  exact rule12124 (meaning t m 2427) (meaning t m 3569) (meaning t m 3741) (meaning t m 4646) (meaning t m 4647)

theorem rule12125 (p2427 p3569 p3741 p4646 p4647 : Prop) : (p2427) ∨ (((¬ p3569) ∨ (¬ p3741) ∨ (¬ p2427) ∨ (¬ p4646) ∨ (¬ p4647))) := by
  classical
  tauto

theorem initial12125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2427) ∨ (meaning t m 5855) := by
  exact rule12125 (meaning t m 2427) (meaning t m 3569) (meaning t m 3741) (meaning t m 4646) (meaning t m 4647)

theorem rule12126 (p2427 p3569 p3741 p4646 p4647 : Prop) : (p4646) ∨ (((¬ p3569) ∨ (¬ p3741) ∨ (¬ p2427) ∨ (¬ p4646) ∨ (¬ p4647))) := by
  classical
  tauto

theorem initial12126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4646) ∨ (meaning t m 5855) := by
  exact rule12126 (meaning t m 2427) (meaning t m 3569) (meaning t m 3741) (meaning t m 4646) (meaning t m 4647)

theorem rule12131 (p5854 p5855 : Prop) : (¬ ((¬ p5854) ∨ (¬ p5855))) ∨ (¬ p5854) ∨ (¬ p5855) := by
  classical
  tauto

theorem initial12131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5853)) ∨ (¬ (meaning t m 5854)) ∨ (¬ (meaning t m 5855)) := by
  exact rule12131 (meaning t m 5854) (meaning t m 5855)

theorem rule12132 (p4642 p5853 : Prop) (h : (p4642 ↔ p5853)) : (¬ p4642) ∨ (p5853) := by
  classical
  tauto

theorem initial12132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4642)) ∨ (meaning t m 5853) := by
  have source := ElevenTheory.theory3245 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule12132 (meaning t m 4642) (meaning t m 5853) source

theorem rule12134 (p3740 p3742 p4112 p4327 p4650 : Prop) : (p3740) ∨ (((¬ p3740) ∨ (¬ p3742) ∨ (¬ p4112) ∨ (¬ p4650) ∨ (¬ p4327))) := by
  classical
  tauto

theorem initial12134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3740) ∨ (meaning t m 5857) := by
  exact rule12134 (meaning t m 3740) (meaning t m 3742) (meaning t m 4112) (meaning t m 4327) (meaning t m 4650)

theorem rule12135 (p3740 p3742 p4112 p4327 p4650 : Prop) : (p3742) ∨ (((¬ p3740) ∨ (¬ p3742) ∨ (¬ p4112) ∨ (¬ p4650) ∨ (¬ p4327))) := by
  classical
  tauto

theorem initial12135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3742) ∨ (meaning t m 5857) := by
  exact rule12135 (meaning t m 3740) (meaning t m 3742) (meaning t m 4112) (meaning t m 4327) (meaning t m 4650)

theorem rule12136 (p3740 p3742 p4112 p4327 p4650 : Prop) : (p4112) ∨ (((¬ p3740) ∨ (¬ p3742) ∨ (¬ p4112) ∨ (¬ p4650) ∨ (¬ p4327))) := by
  classical
  tauto

theorem initial12136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4112) ∨ (meaning t m 5857) := by
  exact rule12136 (meaning t m 3740) (meaning t m 3742) (meaning t m 4112) (meaning t m 4327) (meaning t m 4650)

theorem rule12137 (p3740 p3742 p4112 p4327 p4650 : Prop) : (p4650) ∨ (((¬ p3740) ∨ (¬ p3742) ∨ (¬ p4112) ∨ (¬ p4650) ∨ (¬ p4327))) := by
  classical
  tauto

theorem initial12137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4650) ∨ (meaning t m 5857) := by
  exact rule12137 (meaning t m 3740) (meaning t m 3742) (meaning t m 4112) (meaning t m 4327) (meaning t m 4650)

theorem rule12140 (p2437 p3579 p3580 p4652 p4653 : Prop) : (p3579) ∨ (((¬ p3579) ∨ (¬ p3580) ∨ (¬ p2437) ∨ (¬ p4652) ∨ (¬ p4653))) := by
  classical
  tauto

theorem initial12140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3579) ∨ (meaning t m 5858) := by
  exact rule12140 (meaning t m 2437) (meaning t m 3579) (meaning t m 3580) (meaning t m 4652) (meaning t m 4653)

theorem rule12141 (p2437 p3579 p3580 p4652 p4653 : Prop) : (p3580) ∨ (((¬ p3579) ∨ (¬ p3580) ∨ (¬ p2437) ∨ (¬ p4652) ∨ (¬ p4653))) := by
  classical
  tauto

theorem initial12141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3580) ∨ (meaning t m 5858) := by
  exact rule12141 (meaning t m 2437) (meaning t m 3579) (meaning t m 3580) (meaning t m 4652) (meaning t m 4653)

theorem rule12142 (p2437 p3579 p3580 p4652 p4653 : Prop) : (p2437) ∨ (((¬ p3579) ∨ (¬ p3580) ∨ (¬ p2437) ∨ (¬ p4652) ∨ (¬ p4653))) := by
  classical
  tauto

theorem initial12142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2437) ∨ (meaning t m 5858) := by
  exact rule12142 (meaning t m 2437) (meaning t m 3579) (meaning t m 3580) (meaning t m 4652) (meaning t m 4653)

theorem rule12144 (p2437 p3579 p3580 p4652 p4653 : Prop) : (p4653) ∨ (((¬ p3579) ∨ (¬ p3580) ∨ (¬ p2437) ∨ (¬ p4652) ∨ (¬ p4653))) := by
  classical
  tauto

theorem initial12144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4653) ∨ (meaning t m 5858) := by
  exact rule12144 (meaning t m 2437) (meaning t m 3579) (meaning t m 3580) (meaning t m 4652) (meaning t m 4653)

theorem rule12148 (p5857 p5858 : Prop) : (¬ ((¬ p5857) ∨ (¬ p5858))) ∨ (¬ p5857) ∨ (¬ p5858) := by
  classical
  tauto

theorem initial12148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5856)) ∨ (¬ (meaning t m 5857)) ∨ (¬ (meaning t m 5858)) := by
  exact rule12148 (meaning t m 5857) (meaning t m 5858)

theorem rule12149 (p4648 p5856 : Prop) (h : (p4648 ↔ p5856)) : (¬ p4648) ∨ (p5856) := by
  classical
  tauto

theorem initial12149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4648)) ∨ (meaning t m 5856) := by
  have source := ElevenTheory.theory3246 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule12149 (meaning t m 4648) (meaning t m 5856) source

theorem rule12151 (p3947 p4429 p4656 p4657 p4658 : Prop) : (p4656) ∨ (((¬ p4656) ∨ (¬ p3947) ∨ (¬ p4429) ∨ (¬ p4657) ∨ (¬ p4658))) := by
  classical
  tauto

theorem initial12151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4656) ∨ (meaning t m 5860) := by
  exact rule12151 (meaning t m 3947) (meaning t m 4429) (meaning t m 4656) (meaning t m 4657) (meaning t m 4658)

theorem rule12152 (p3947 p4429 p4656 p4657 p4658 : Prop) : (p3947) ∨ (((¬ p4656) ∨ (¬ p3947) ∨ (¬ p4429) ∨ (¬ p4657) ∨ (¬ p4658))) := by
  classical
  tauto

theorem initial12152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3947) ∨ (meaning t m 5860) := by
  exact rule12152 (meaning t m 3947) (meaning t m 4429) (meaning t m 4656) (meaning t m 4657) (meaning t m 4658)

theorem rule12153 (p3947 p4429 p4656 p4657 p4658 : Prop) : (p4429) ∨ (((¬ p4656) ∨ (¬ p3947) ∨ (¬ p4429) ∨ (¬ p4657) ∨ (¬ p4658))) := by
  classical
  tauto

theorem initial12153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4429) ∨ (meaning t m 5860) := by
  exact rule12153 (meaning t m 3947) (meaning t m 4429) (meaning t m 4656) (meaning t m 4657) (meaning t m 4658)

theorem rule12155 (p3947 p4429 p4656 p4657 p4658 : Prop) : (p4658) ∨ (((¬ p4656) ∨ (¬ p3947) ∨ (¬ p4429) ∨ (¬ p4657) ∨ (¬ p4658))) := by
  classical
  tauto

theorem initial12155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4658) ∨ (meaning t m 5860) := by
  exact rule12155 (meaning t m 3947) (meaning t m 4429) (meaning t m 4656) (meaning t m 4657) (meaning t m 4658)

theorem rule12157 (p2449 p4660 p4661 p4662 p4663 : Prop) : (p4660) ∨ (((¬ p4660) ∨ (¬ p4661) ∨ (¬ p2449) ∨ (¬ p4662) ∨ (¬ p4663))) := by
  classical
  tauto

theorem initial12157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4660) ∨ (meaning t m 5861) := by
  exact rule12157 (meaning t m 2449) (meaning t m 4660) (meaning t m 4661) (meaning t m 4662) (meaning t m 4663)

theorem rule12158 (p2449 p4660 p4661 p4662 p4663 : Prop) : (p4661) ∨ (((¬ p4660) ∨ (¬ p4661) ∨ (¬ p2449) ∨ (¬ p4662) ∨ (¬ p4663))) := by
  classical
  tauto

theorem initial12158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4661) ∨ (meaning t m 5861) := by
  exact rule12158 (meaning t m 2449) (meaning t m 4660) (meaning t m 4661) (meaning t m 4662) (meaning t m 4663)

theorem rule12159 (p2449 p4660 p4661 p4662 p4663 : Prop) : (p2449) ∨ (((¬ p4660) ∨ (¬ p4661) ∨ (¬ p2449) ∨ (¬ p4662) ∨ (¬ p4663))) := by
  classical
  tauto

theorem initial12159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2449) ∨ (meaning t m 5861) := by
  exact rule12159 (meaning t m 2449) (meaning t m 4660) (meaning t m 4661) (meaning t m 4662) (meaning t m 4663)

theorem rule12161 (p2449 p4660 p4661 p4662 p4663 : Prop) : (p4663) ∨ (((¬ p4660) ∨ (¬ p4661) ∨ (¬ p2449) ∨ (¬ p4662) ∨ (¬ p4663))) := by
  classical
  tauto

theorem initial12161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4663) ∨ (meaning t m 5861) := by
  exact rule12161 (meaning t m 2449) (meaning t m 4660) (meaning t m 4661) (meaning t m 4662) (meaning t m 4663)

theorem rule12165 (p5860 p5861 : Prop) : (¬ ((¬ p5860) ∨ (¬ p5861))) ∨ (¬ p5860) ∨ (¬ p5861) := by
  classical
  tauto

theorem initial12165 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5859)) ∨ (¬ (meaning t m 5860)) ∨ (¬ (meaning t m 5861)) := by
  exact rule12165 (meaning t m 5860) (meaning t m 5861)

theorem rule12166 (p4654 p5859 : Prop) (h : (p4654 ↔ p5859)) : (¬ p4654) ∨ (p5859) := by
  classical
  tauto

theorem initial12166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4654)) ∨ (meaning t m 5859) := by
  have source := ElevenTheory.theory3247 t (m.theta 3 7) (m.theta 3 9) (m.theta 7 9)
  exact rule12166 (meaning t m 4654) (meaning t m 5859) source

theorem rule12168 (p3657 p3950 p4348 p4445 p4666 : Prop) : (p4445) ∨ (((¬ p4445) ∨ (¬ p4348) ∨ (¬ p3657) ∨ (¬ p4666) ∨ (¬ p3950))) := by
  classical
  tauto

theorem initial12168 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4445) ∨ (meaning t m 5863) := by
  exact rule12168 (meaning t m 3657) (meaning t m 3950) (meaning t m 4348) (meaning t m 4445) (meaning t m 4666)

theorem rule12169 (p3657 p3950 p4348 p4445 p4666 : Prop) : (p4348) ∨ (((¬ p4445) ∨ (¬ p4348) ∨ (¬ p3657) ∨ (¬ p4666) ∨ (¬ p3950))) := by
  classical
  tauto

theorem initial12169 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4348) ∨ (meaning t m 5863) := by
  exact rule12169 (meaning t m 3657) (meaning t m 3950) (meaning t m 4348) (meaning t m 4445) (meaning t m 4666)

theorem rule12170 (p3657 p3950 p4348 p4445 p4666 : Prop) : (p3657) ∨ (((¬ p4445) ∨ (¬ p4348) ∨ (¬ p3657) ∨ (¬ p4666) ∨ (¬ p3950))) := by
  classical
  tauto

theorem initial12170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3657) ∨ (meaning t m 5863) := by
  exact rule12170 (meaning t m 3657) (meaning t m 3950) (meaning t m 4348) (meaning t m 4445) (meaning t m 4666)

theorem rule12172 (p3657 p3950 p4348 p4445 p4666 : Prop) : (p3950) ∨ (((¬ p4445) ∨ (¬ p4348) ∨ (¬ p3657) ∨ (¬ p4666) ∨ (¬ p3950))) := by
  classical
  tauto

theorem initial12172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3950) ∨ (meaning t m 5863) := by
  exact rule12172 (meaning t m 3657) (meaning t m 3950) (meaning t m 4348) (meaning t m 4445) (meaning t m 4666)

theorem rule12174 (p2459 p3945 p4443 p4668 p4669 : Prop) : (p4443) ∨ (((¬ p4443) ∨ (¬ p3945) ∨ (¬ p2459) ∨ (¬ p4668) ∨ (¬ p4669))) := by
  classical
  tauto

theorem initial12174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4443) ∨ (meaning t m 5864) := by
  exact rule12174 (meaning t m 2459) (meaning t m 3945) (meaning t m 4443) (meaning t m 4668) (meaning t m 4669)

theorem rule12175 (p2459 p3945 p4443 p4668 p4669 : Prop) : (p3945) ∨ (((¬ p4443) ∨ (¬ p3945) ∨ (¬ p2459) ∨ (¬ p4668) ∨ (¬ p4669))) := by
  classical
  tauto

theorem initial12175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3945) ∨ (meaning t m 5864) := by
  exact rule12175 (meaning t m 2459) (meaning t m 3945) (meaning t m 4443) (meaning t m 4668) (meaning t m 4669)

theorem rule12176 (p2459 p3945 p4443 p4668 p4669 : Prop) : (p2459) ∨ (((¬ p4443) ∨ (¬ p3945) ∨ (¬ p2459) ∨ (¬ p4668) ∨ (¬ p4669))) := by
  classical
  tauto

theorem initial12176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2459) ∨ (meaning t m 5864) := by
  exact rule12176 (meaning t m 2459) (meaning t m 3945) (meaning t m 4443) (meaning t m 4668) (meaning t m 4669)

theorem rule12182 (p5863 p5864 : Prop) : (¬ ((¬ p5863) ∨ (¬ p5864))) ∨ (¬ p5863) ∨ (¬ p5864) := by
  classical
  tauto

theorem initial12182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5862)) ∨ (¬ (meaning t m 5863)) ∨ (¬ (meaning t m 5864)) := by
  exact rule12182 (meaning t m 5863) (meaning t m 5864)

theorem rule12183 (p4664 p5862 : Prop) (h : (p4664 ↔ p5862)) : (¬ p4664) ∨ (p5862) := by
  classical
  tauto

theorem initial12183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4664)) ∨ (meaning t m 5862) := by
  have source := ElevenTheory.theory3248 t (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule12183 (meaning t m 4664) (meaning t m 5862) source

theorem rule12185 (p1981 p2027 p2202 p2470 p2528 p2589 p4347 : Prop) (h : (¬ p2470) ∨ (¬ p1981) ∨ p2202 ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2528) ∨ (¬ p4347)) : (¬ p1981) ∨ (p2027) ∨ (p2202) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2589) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial12185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3249 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule12185 (meaning t m 1981) (meaning t m 2027) (meaning t m 2202) (meaning t m 2470) (meaning t m 2528) (meaning t m 2589) (meaning t m 4347) source

theorem rule12186 (p2497 p2498 p2573 p3519 : Prop) (h : (¬ p3519) ∨ (¬ p2497) ∨ (¬ p2498) ∨ (¬ p2573)) : (¬ p2497) ∨ (¬ p2498) ∨ (¬ p2573) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial12186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory3250 (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6)
  exact rule12186 (meaning t m 2497) (meaning t m 2498) (meaning t m 2573) (meaning t m 3519) source

theorem rule12187 (p2509 p3453 p4370 p4684 p4685 : Prop) : (p3453) ∨ (((¬ p3453) ∨ (¬ p4684) ∨ (¬ p4685) ∨ (¬ p2509) ∨ (¬ p4370))) := by
  classical
  tauto

theorem initial12187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3453) ∨ (meaning t m 5866) := by
  exact rule12187 (meaning t m 2509) (meaning t m 3453) (meaning t m 4370) (meaning t m 4684) (meaning t m 4685)

theorem rule12188 (p2509 p3453 p4370 p4684 p4685 : Prop) : (p4684) ∨ (((¬ p3453) ∨ (¬ p4684) ∨ (¬ p4685) ∨ (¬ p2509) ∨ (¬ p4370))) := by
  classical
  tauto

theorem initial12188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4684) ∨ (meaning t m 5866) := by
  exact rule12188 (meaning t m 2509) (meaning t m 3453) (meaning t m 4370) (meaning t m 4684) (meaning t m 4685)

theorem rule12189 (p2509 p3453 p4370 p4684 p4685 : Prop) : (p4685) ∨ (((¬ p3453) ∨ (¬ p4684) ∨ (¬ p4685) ∨ (¬ p2509) ∨ (¬ p4370))) := by
  classical
  tauto

theorem initial12189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4685) ∨ (meaning t m 5866) := by
  exact rule12189 (meaning t m 2509) (meaning t m 3453) (meaning t m 4370) (meaning t m 4684) (meaning t m 4685)

theorem rule12190 (p2509 p3453 p4370 p4684 p4685 : Prop) : (p2509) ∨ (((¬ p3453) ∨ (¬ p4684) ∨ (¬ p4685) ∨ (¬ p2509) ∨ (¬ p4370))) := by
  classical
  tauto

theorem initial12190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2509) ∨ (meaning t m 5866) := by
  exact rule12190 (meaning t m 2509) (meaning t m 3453) (meaning t m 4370) (meaning t m 4684) (meaning t m 4685)

theorem rule12191 (p2509 p3453 p4370 p4684 p4685 : Prop) : (p4370) ∨ (((¬ p3453) ∨ (¬ p4684) ∨ (¬ p4685) ∨ (¬ p2509) ∨ (¬ p4370))) := by
  classical
  tauto

theorem initial12191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4370) ∨ (meaning t m 5866) := by
  exact rule12191 (meaning t m 2509) (meaning t m 3453) (meaning t m 4370) (meaning t m 4684) (meaning t m 4685)

theorem rule12192 (p2509 p3453 p4370 p4684 p4685 : Prop) : (¬ p2509) ∨ (¬ p3453) ∨ (¬ p4370) ∨ (¬ p4684) ∨ (¬ p4685) ∨ (¬ ((¬ p3453) ∨ (¬ p4684) ∨ (¬ p4685) ∨ (¬ p2509) ∨ (¬ p4370))) := by
  classical
  tauto

theorem initial12192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3453)) ∨ (¬ (meaning t m 4370)) ∨ (¬ (meaning t m 4684)) ∨ (¬ (meaning t m 4685)) ∨ (¬ (meaning t m 5866)) := by
  exact rule12192 (meaning t m 2509) (meaning t m 3453) (meaning t m 4370) (meaning t m 4684) (meaning t m 4685)

theorem rule12193 (p2518 p4687 p4688 p4689 p4690 : Prop) : (p4688) ∨ (((¬ p4688) ∨ (¬ p4687) ∨ (¬ p4690) ∨ (¬ p2518) ∨ (¬ p4689))) := by
  classical
  tauto

theorem initial12193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4688) ∨ (meaning t m 5867) := by
  exact rule12193 (meaning t m 2518) (meaning t m 4687) (meaning t m 4688) (meaning t m 4689) (meaning t m 4690)

theorem rule12201 (p5866 p5867 : Prop) : (¬ ((¬ p5866) ∨ (¬ p5867))) ∨ (¬ p5866) ∨ (¬ p5867) := by
  classical
  tauto

theorem initial12201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5865)) ∨ (¬ (meaning t m 5866)) ∨ (¬ (meaning t m 5867)) := by
  exact rule12201 (meaning t m 5866) (meaning t m 5867)

theorem rule12202 (p4682 p5865 : Prop) (h : (p4682 ↔ p5865)) : (¬ p4682) ∨ (p5865) := by
  classical
  tauto

theorem initial12202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4682)) ∨ (meaning t m 5865) := by
  have source := ElevenTheory.theory3251 t (m.theta 1 4) (m.theta 1 8) (m.theta 4 8)
  exact rule12202 (meaning t m 4682) (meaning t m 5865) source

theorem rule12204 (p1975 p2027 p2409 p2476 p2518 p2553 p2573 : Prop) (h : p2027 ∨ p2409 ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p1975) ∨ (¬ p2518) ∨ (¬ p2476)) : (¬ p1975) ∨ (p2027) ∨ (p2409) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2553) ∨ (¬ p2573) := by
  classical
  tauto

theorem initial12204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) := by
  have source := ElevenTheory.theory3252 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule12204 (meaning t m 1975) (meaning t m 2027) (meaning t m 2409) (meaning t m 2476) (meaning t m 2518) (meaning t m 2553) (meaning t m 2573) source

theorem rule12205 (p2534 p4045 p4332 p4440 p4693 : Prop) : (p4440) ∨ (((¬ p4440) ∨ (¬ p2534) ∨ (¬ p4045) ∨ (¬ p4693) ∨ (¬ p4332))) := by
  classical
  tauto

theorem initial12205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4440) ∨ (meaning t m 5869) := by
  exact rule12205 (meaning t m 2534) (meaning t m 4045) (meaning t m 4332) (meaning t m 4440) (meaning t m 4693)

theorem rule12206 (p2534 p4045 p4332 p4440 p4693 : Prop) : (p2534) ∨ (((¬ p4440) ∨ (¬ p2534) ∨ (¬ p4045) ∨ (¬ p4693) ∨ (¬ p4332))) := by
  classical
  tauto

theorem initial12206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2534) ∨ (meaning t m 5869) := by
  exact rule12206 (meaning t m 2534) (meaning t m 4045) (meaning t m 4332) (meaning t m 4440) (meaning t m 4693)

theorem rule12207 (p2534 p4045 p4332 p4440 p4693 : Prop) : (p4045) ∨ (((¬ p4440) ∨ (¬ p2534) ∨ (¬ p4045) ∨ (¬ p4693) ∨ (¬ p4332))) := by
  classical
  tauto

theorem initial12207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4045) ∨ (meaning t m 5869) := by
  exact rule12207 (meaning t m 2534) (meaning t m 4045) (meaning t m 4332) (meaning t m 4440) (meaning t m 4693)

theorem rule12209 (p2534 p4045 p4332 p4440 p4693 : Prop) : (p4332) ∨ (((¬ p4440) ∨ (¬ p2534) ∨ (¬ p4045) ∨ (¬ p4693) ∨ (¬ p4332))) := by
  classical
  tauto

theorem initial12209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4332) ∨ (meaning t m 5869) := by
  exact rule12209 (meaning t m 2534) (meaning t m 4045) (meaning t m 4332) (meaning t m 4440) (meaning t m 4693)

theorem rule12211 (p2528 p3358 p4695 p4696 p4697 : Prop) : (p4695) ∨ (((¬ p4695) ∨ (¬ p3358) ∨ (¬ p2528) ∨ (¬ p4696) ∨ (¬ p4697))) := by
  classical
  tauto

theorem initial12211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4695) ∨ (meaning t m 5870) := by
  exact rule12211 (meaning t m 2528) (meaning t m 3358) (meaning t m 4695) (meaning t m 4696) (meaning t m 4697)

theorem rule12212 (p2528 p3358 p4695 p4696 p4697 : Prop) : (p3358) ∨ (((¬ p4695) ∨ (¬ p3358) ∨ (¬ p2528) ∨ (¬ p4696) ∨ (¬ p4697))) := by
  classical
  tauto

theorem initial12212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3358) ∨ (meaning t m 5870) := by
  exact rule12212 (meaning t m 2528) (meaning t m 3358) (meaning t m 4695) (meaning t m 4696) (meaning t m 4697)

theorem rule12213 (p2528 p3358 p4695 p4696 p4697 : Prop) : (p2528) ∨ (((¬ p4695) ∨ (¬ p3358) ∨ (¬ p2528) ∨ (¬ p4696) ∨ (¬ p4697))) := by
  classical
  tauto

theorem initial12213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2528) ∨ (meaning t m 5870) := by
  exact rule12213 (meaning t m 2528) (meaning t m 3358) (meaning t m 4695) (meaning t m 4696) (meaning t m 4697)

theorem rule12215 (p2528 p3358 p4695 p4696 p4697 : Prop) : (p4697) ∨ (((¬ p4695) ∨ (¬ p3358) ∨ (¬ p2528) ∨ (¬ p4696) ∨ (¬ p4697))) := by
  classical
  tauto

theorem initial12215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4697) ∨ (meaning t m 5870) := by
  exact rule12215 (meaning t m 2528) (meaning t m 3358) (meaning t m 4695) (meaning t m 4696) (meaning t m 4697)

theorem rule12219 (p5869 p5870 : Prop) : (¬ ((¬ p5869) ∨ (¬ p5870))) ∨ (¬ p5869) ∨ (¬ p5870) := by
  classical
  tauto

theorem initial12219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5868)) ∨ (¬ (meaning t m 5869)) ∨ (¬ (meaning t m 5870)) := by
  exact rule12219 (meaning t m 5869) (meaning t m 5870)

theorem rule12220 (p4691 p5868 : Prop) (h : (p4691 ↔ p5868)) : (¬ p4691) ∨ (p5868) := by
  classical
  tauto

theorem initial12220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4691)) ∨ (meaning t m 5868) := by
  have source := ElevenTheory.theory3253 t (m.theta 4 8) (m.theta 4 9) (m.theta 8 9)
  exact rule12220 (meaning t m 4691) (meaning t m 5868) source

theorem rule12222 (p2440 p3879 p4700 p4701 p4702 : Prop) : (p3879) ∨ (((¬ p3879) ∨ (¬ p2440) ∨ (¬ p4700) ∨ (¬ p4701) ∨ (¬ p4702))) := by
  classical
  tauto

theorem initial12222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3879) ∨ (meaning t m 5872) := by
  exact rule12222 (meaning t m 2440) (meaning t m 3879) (meaning t m 4700) (meaning t m 4701) (meaning t m 4702)

theorem rule12223 (p2440 p3879 p4700 p4701 p4702 : Prop) : (p2440) ∨ (((¬ p3879) ∨ (¬ p2440) ∨ (¬ p4700) ∨ (¬ p4701) ∨ (¬ p4702))) := by
  classical
  tauto

theorem initial12223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2440) ∨ (meaning t m 5872) := by
  exact rule12223 (meaning t m 2440) (meaning t m 3879) (meaning t m 4700) (meaning t m 4701) (meaning t m 4702)

theorem rule12224 (p2440 p3879 p4700 p4701 p4702 : Prop) : (p4700) ∨ (((¬ p3879) ∨ (¬ p2440) ∨ (¬ p4700) ∨ (¬ p4701) ∨ (¬ p4702))) := by
  classical
  tauto

theorem initial12224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4700) ∨ (meaning t m 5872) := by
  exact rule12224 (meaning t m 2440) (meaning t m 3879) (meaning t m 4700) (meaning t m 4701) (meaning t m 4702)

theorem rule12225 (p2440 p3879 p4700 p4701 p4702 : Prop) : (p4701) ∨ (((¬ p3879) ∨ (¬ p2440) ∨ (¬ p4700) ∨ (¬ p4701) ∨ (¬ p4702))) := by
  classical
  tauto

theorem initial12225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4701) ∨ (meaning t m 5872) := by
  exact rule12225 (meaning t m 2440) (meaning t m 3879) (meaning t m 4700) (meaning t m 4701) (meaning t m 4702)

theorem rule12226 (p2440 p3879 p4700 p4701 p4702 : Prop) : (p4702) ∨ (((¬ p3879) ∨ (¬ p2440) ∨ (¬ p4700) ∨ (¬ p4701) ∨ (¬ p4702))) := by
  classical
  tauto

theorem initial12226 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4702) ∨ (meaning t m 5872) := by
  exact rule12226 (meaning t m 2440) (meaning t m 3879) (meaning t m 4700) (meaning t m 4701) (meaning t m 4702)

theorem rule12228 (p2542 p3413 p4241 p4704 p4705 : Prop) : (p4241) ∨ (((¬ p4241) ∨ (¬ p3413) ∨ (¬ p2542) ∨ (¬ p4704) ∨ (¬ p4705))) := by
  classical
  tauto

theorem initial12228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4241) ∨ (meaning t m 5873) := by
  exact rule12228 (meaning t m 2542) (meaning t m 3413) (meaning t m 4241) (meaning t m 4704) (meaning t m 4705)

theorem rule12229 (p2542 p3413 p4241 p4704 p4705 : Prop) : (p3413) ∨ (((¬ p4241) ∨ (¬ p3413) ∨ (¬ p2542) ∨ (¬ p4704) ∨ (¬ p4705))) := by
  classical
  tauto

theorem initial12229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3413) ∨ (meaning t m 5873) := by
  exact rule12229 (meaning t m 2542) (meaning t m 3413) (meaning t m 4241) (meaning t m 4704) (meaning t m 4705)

theorem rule12230 (p2542 p3413 p4241 p4704 p4705 : Prop) : (p2542) ∨ (((¬ p4241) ∨ (¬ p3413) ∨ (¬ p2542) ∨ (¬ p4704) ∨ (¬ p4705))) := by
  classical
  tauto

theorem initial12230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2542) ∨ (meaning t m 5873) := by
  exact rule12230 (meaning t m 2542) (meaning t m 3413) (meaning t m 4241) (meaning t m 4704) (meaning t m 4705)

theorem rule12231 (p2542 p3413 p4241 p4704 p4705 : Prop) : (p4704) ∨ (((¬ p4241) ∨ (¬ p3413) ∨ (¬ p2542) ∨ (¬ p4704) ∨ (¬ p4705))) := by
  classical
  tauto

theorem initial12231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4704) ∨ (meaning t m 5873) := by
  exact rule12231 (meaning t m 2542) (meaning t m 3413) (meaning t m 4241) (meaning t m 4704) (meaning t m 4705)

theorem rule12232 (p2542 p3413 p4241 p4704 p4705 : Prop) : (p4705) ∨ (((¬ p4241) ∨ (¬ p3413) ∨ (¬ p2542) ∨ (¬ p4704) ∨ (¬ p4705))) := by
  classical
  tauto

theorem initial12232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4705) ∨ (meaning t m 5873) := by
  exact rule12232 (meaning t m 2542) (meaning t m 3413) (meaning t m 4241) (meaning t m 4704) (meaning t m 4705)

theorem rule12236 (p5872 p5873 : Prop) : (¬ ((¬ p5872) ∨ (¬ p5873))) ∨ (¬ p5872) ∨ (¬ p5873) := by
  classical
  tauto

theorem initial12236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5871)) ∨ (¬ (meaning t m 5872)) ∨ (¬ (meaning t m 5873)) := by
  exact rule12236 (meaning t m 5872) (meaning t m 5873)

theorem rule12237 (p4698 p5871 : Prop) (h : (p4698 ↔ p5871)) : (¬ p4698) ∨ (p5871) := by
  classical
  tauto

theorem initial12237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4698)) ∨ (meaning t m 5871) := by
  have source := ElevenTheory.theory3254 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule12237 (meaning t m 4698) (meaning t m 5871) source

theorem rule12239 (p1975 p2027 p2542 p2545 p2553 p2573 p2589 : Prop) (h : p2545 ∨ p2027 ∨ (¬ p2542) ∨ (¬ p2553) ∨ (¬ p2589) ∨ (¬ p1975) ∨ (¬ p2573)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2589) := by
  classical
  tauto

theorem initial12239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) := by
  have source := ElevenTheory.theory3255 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule12239 (meaning t m 1975) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2553) (meaning t m 2573) (meaning t m 2589) source

theorem rule12240 (p2588 p3581 p3921 p4276 p4708 : Prop) : (p3921) ∨ (((¬ p3921) ∨ (¬ p2588) ∨ (¬ p3581) ∨ (¬ p4708) ∨ (¬ p4276))) := by
  classical
  tauto

theorem initial12240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3921) ∨ (meaning t m 5875) := by
  exact rule12240 (meaning t m 2588) (meaning t m 3581) (meaning t m 3921) (meaning t m 4276) (meaning t m 4708)

theorem rule12241 (p2588 p3581 p3921 p4276 p4708 : Prop) : (p2588) ∨ (((¬ p3921) ∨ (¬ p2588) ∨ (¬ p3581) ∨ (¬ p4708) ∨ (¬ p4276))) := by
  classical
  tauto

theorem initial12241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2588) ∨ (meaning t m 5875) := by
  exact rule12241 (meaning t m 2588) (meaning t m 3581) (meaning t m 3921) (meaning t m 4276) (meaning t m 4708)

theorem rule12242 (p2588 p3581 p3921 p4276 p4708 : Prop) : (p3581) ∨ (((¬ p3921) ∨ (¬ p2588) ∨ (¬ p3581) ∨ (¬ p4708) ∨ (¬ p4276))) := by
  classical
  tauto

theorem initial12242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3581) ∨ (meaning t m 5875) := by
  exact rule12242 (meaning t m 2588) (meaning t m 3581) (meaning t m 3921) (meaning t m 4276) (meaning t m 4708)

theorem rule12243 (p2588 p3581 p3921 p4276 p4708 : Prop) : (p4708) ∨ (((¬ p3921) ∨ (¬ p2588) ∨ (¬ p3581) ∨ (¬ p4708) ∨ (¬ p4276))) := by
  classical
  tauto

theorem initial12243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4708) ∨ (meaning t m 5875) := by
  exact rule12243 (meaning t m 2588) (meaning t m 3581) (meaning t m 3921) (meaning t m 4276) (meaning t m 4708)

theorem rule12246 (p2553 p3920 p4710 p4711 p4712 : Prop) : (p4710) ∨ (((¬ p4710) ∨ (¬ p3920) ∨ (¬ p2553) ∨ (¬ p4711) ∨ (¬ p4712))) := by
  classical
  tauto

theorem initial12246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4710) ∨ (meaning t m 5876) := by
  exact rule12246 (meaning t m 2553) (meaning t m 3920) (meaning t m 4710) (meaning t m 4711) (meaning t m 4712)

theorem rule12247 (p2553 p3920 p4710 p4711 p4712 : Prop) : (p3920) ∨ (((¬ p4710) ∨ (¬ p3920) ∨ (¬ p2553) ∨ (¬ p4711) ∨ (¬ p4712))) := by
  classical
  tauto

theorem initial12247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3920) ∨ (meaning t m 5876) := by
  exact rule12247 (meaning t m 2553) (meaning t m 3920) (meaning t m 4710) (meaning t m 4711) (meaning t m 4712)

theorem rule12248 (p2553 p3920 p4710 p4711 p4712 : Prop) : (p2553) ∨ (((¬ p4710) ∨ (¬ p3920) ∨ (¬ p2553) ∨ (¬ p4711) ∨ (¬ p4712))) := by
  classical
  tauto

theorem initial12248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2553) ∨ (meaning t m 5876) := by
  exact rule12248 (meaning t m 2553) (meaning t m 3920) (meaning t m 4710) (meaning t m 4711) (meaning t m 4712)

theorem rule12254 (p5875 p5876 : Prop) : (¬ ((¬ p5875) ∨ (¬ p5876))) ∨ (¬ p5875) ∨ (¬ p5876) := by
  classical
  tauto

theorem initial12254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5874)) ∨ (¬ (meaning t m 5875)) ∨ (¬ (meaning t m 5876)) := by
  exact rule12254 (meaning t m 5875) (meaning t m 5876)

theorem rule12255 (p4706 p5874 : Prop) (h : (p4706 ↔ p5874)) : (¬ p4706) ∨ (p5874) := by
  classical
  tauto

theorem initial12255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4706)) ∨ (meaning t m 5874) := by
  have source := ElevenTheory.theory3256 t (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule12255 (meaning t m 4706) (meaning t m 5874) source

theorem rule12257 (p2590 p3096 p3958 p4110 p4715 : Prop) : (p3096) ∨ (((¬ p3096) ∨ (¬ p4110) ∨ (¬ p2590) ∨ (¬ p4715) ∨ (¬ p3958))) := by
  classical
  tauto

theorem initial12257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3096) ∨ (meaning t m 5878) := by
  exact rule12257 (meaning t m 2590) (meaning t m 3096) (meaning t m 3958) (meaning t m 4110) (meaning t m 4715)

theorem rule12258 (p2590 p3096 p3958 p4110 p4715 : Prop) : (p4110) ∨ (((¬ p3096) ∨ (¬ p4110) ∨ (¬ p2590) ∨ (¬ p4715) ∨ (¬ p3958))) := by
  classical
  tauto

theorem initial12258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4110) ∨ (meaning t m 5878) := by
  exact rule12258 (meaning t m 2590) (meaning t m 3096) (meaning t m 3958) (meaning t m 4110) (meaning t m 4715)

theorem rule12259 (p2590 p3096 p3958 p4110 p4715 : Prop) : (p2590) ∨ (((¬ p3096) ∨ (¬ p4110) ∨ (¬ p2590) ∨ (¬ p4715) ∨ (¬ p3958))) := by
  classical
  tauto

theorem initial12259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2590) ∨ (meaning t m 5878) := by
  exact rule12259 (meaning t m 2590) (meaning t m 3096) (meaning t m 3958) (meaning t m 4110) (meaning t m 4715)

theorem rule12263 (p2563 p3660 p4203 p4717 p4718 : Prop) : (p4203) ∨ (((¬ p4203) ∨ (¬ p3660) ∨ (¬ p2563) ∨ (¬ p4717) ∨ (¬ p4718))) := by
  classical
  tauto

theorem initial12263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4203) ∨ (meaning t m 5879) := by
  exact rule12263 (meaning t m 2563) (meaning t m 3660) (meaning t m 4203) (meaning t m 4717) (meaning t m 4718)

theorem rule12264 (p2563 p3660 p4203 p4717 p4718 : Prop) : (p3660) ∨ (((¬ p4203) ∨ (¬ p3660) ∨ (¬ p2563) ∨ (¬ p4717) ∨ (¬ p4718))) := by
  classical
  tauto

theorem initial12264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3660) ∨ (meaning t m 5879) := by
  exact rule12264 (meaning t m 2563) (meaning t m 3660) (meaning t m 4203) (meaning t m 4717) (meaning t m 4718)

theorem rule12265 (p2563 p3660 p4203 p4717 p4718 : Prop) : (p2563) ∨ (((¬ p4203) ∨ (¬ p3660) ∨ (¬ p2563) ∨ (¬ p4717) ∨ (¬ p4718))) := by
  classical
  tauto

theorem initial12265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2563) ∨ (meaning t m 5879) := by
  exact rule12265 (meaning t m 2563) (meaning t m 3660) (meaning t m 4203) (meaning t m 4717) (meaning t m 4718)

theorem rule12271 (p5878 p5879 : Prop) : (¬ ((¬ p5878) ∨ (¬ p5879))) ∨ (¬ p5878) ∨ (¬ p5879) := by
  classical
  tauto

theorem initial12271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5877)) ∨ (¬ (meaning t m 5878)) ∨ (¬ (meaning t m 5879)) := by
  exact rule12271 (meaning t m 5878) (meaning t m 5879)

theorem rule12272 (p4713 p5877 : Prop) (h : (p4713 ↔ p5877)) : (¬ p4713) ∨ (p5877) := by
  classical
  tauto

theorem initial12272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4713)) ∨ (meaning t m 5877) := by
  have source := ElevenTheory.theory3257 t (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule12272 (meaning t m 4713) (meaning t m 5877) source

theorem rule12274 (p3055 p3759 p3905 p4419 p4727 : Prop) : (p3905) ∨ (((¬ p3905) ∨ (¬ p4419) ∨ (¬ p3055) ∨ (¬ p4727) ∨ (¬ p3759))) := by
  classical
  tauto

theorem initial12274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3905) ∨ (meaning t m 5881) := by
  exact rule12274 (meaning t m 3055) (meaning t m 3759) (meaning t m 3905) (meaning t m 4419) (meaning t m 4727)

theorem rule12275 (p3055 p3759 p3905 p4419 p4727 : Prop) : (p4419) ∨ (((¬ p3905) ∨ (¬ p4419) ∨ (¬ p3055) ∨ (¬ p4727) ∨ (¬ p3759))) := by
  classical
  tauto

theorem initial12275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4419) ∨ (meaning t m 5881) := by
  exact rule12275 (meaning t m 3055) (meaning t m 3759) (meaning t m 3905) (meaning t m 4419) (meaning t m 4727)

theorem rule12276 (p3055 p3759 p3905 p4419 p4727 : Prop) : (p3055) ∨ (((¬ p3905) ∨ (¬ p4419) ∨ (¬ p3055) ∨ (¬ p4727) ∨ (¬ p3759))) := by
  classical
  tauto

theorem initial12276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3055) ∨ (meaning t m 5881) := by
  exact rule12276 (meaning t m 3055) (meaning t m 3759) (meaning t m 3905) (meaning t m 4419) (meaning t m 4727)

theorem rule12277 (p3055 p3759 p3905 p4419 p4727 : Prop) : (p4727) ∨ (((¬ p3905) ∨ (¬ p4419) ∨ (¬ p3055) ∨ (¬ p4727) ∨ (¬ p3759))) := by
  classical
  tauto

theorem initial12277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4727) ∨ (meaning t m 5881) := by
  exact rule12277 (meaning t m 3055) (meaning t m 3759) (meaning t m 3905) (meaning t m 4419) (meaning t m 4727)

theorem rule12278 (p3055 p3759 p3905 p4419 p4727 : Prop) : (p3759) ∨ (((¬ p3905) ∨ (¬ p4419) ∨ (¬ p3055) ∨ (¬ p4727) ∨ (¬ p3759))) := by
  classical
  tauto

theorem initial12278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3759) ∨ (meaning t m 5881) := by
  exact rule12278 (meaning t m 3055) (meaning t m 3759) (meaning t m 3905) (meaning t m 4419) (meaning t m 4727)

theorem rule12280 (p2598 p3362 p3363 p4729 p4730 : Prop) : (p2598) ∨ (((¬ p2598) ∨ (¬ p4729) ∨ (¬ p3363) ∨ (¬ p3362) ∨ (¬ p4730))) := by
  classical
  tauto

theorem initial12280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2598) ∨ (meaning t m 5882) := by
  exact rule12280 (meaning t m 2598) (meaning t m 3362) (meaning t m 3363) (meaning t m 4729) (meaning t m 4730)

end SunPrize.SMT
