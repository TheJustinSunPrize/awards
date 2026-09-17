import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory045
import SunPrize.Certificate.Theory046
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule26307 (p2027 p2406 p2563 p2928 p4001 p4555 : Prop) (h : (¬ p4001) ∨ (¬ p2406) ∨ (¬ p2928) ∨ p2027 ∨ (¬ p4555) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2563) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial26307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory15563 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule26307 (meaning t m 2027) (meaning t m 2406) (meaning t m 2563) (meaning t m 2928) (meaning t m 4001) (meaning t m 4555) source

theorem rule26308 (p2027 p2246 p2579 p2749 p2807 p3347 p3572 p3755 p3956 p4347 p5109 p5216 : Prop) (h : (¬ p5109) ∨ (¬ p3755) ∨ (¬ p3347) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p2749) ∨ (¬ p2807) ∨ (¬ p5216) ∨ (¬ p2246) ∨ (¬ p3572)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2579) ∨ (¬ p2749) ∨ (¬ p2807) ∨ (¬ p3347) ∨ (¬ p3572) ∨ (¬ p3755) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p5109) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial26308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5109)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory15564 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule26308 (meaning t m 2027) (meaning t m 2246) (meaning t m 2579) (meaning t m 2749) (meaning t m 2807) (meaning t m 3347) (meaning t m 3572) (meaning t m 3755) (meaning t m 3956) (meaning t m 4347) (meaning t m 5109) (meaning t m 5216) source

theorem rule26309 (p2027 p2387 p2577 p2662 p3063 p3662 p4701 p4759 : Prop) (h : (¬ p3662) ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p4759) ∨ (¬ p4701) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2577)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p3662) ∨ (¬ p4701) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial26309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4701)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory15565 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 5) (m.theta 6 8)
  exact rule26309 (meaning t m 2027) (meaning t m 2387) (meaning t m 2577) (meaning t m 2662) (meaning t m 3063) (meaning t m 3662) (meaning t m 4701) (meaning t m 4759) source

theorem rule26310 (p2737 p3688 p4426 : Prop) (h : (¬ p2737) ∨ (¬ p4426) ∨ (¬ p3688)) : (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial26310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory15566 (m.theta 1 2) (m.theta 2 3) (m.theta 2 6)
  exact rule26310 (meaning t m 2737) (meaning t m 3688) (meaning t m 4426) source

theorem rule26311 (p2027 p2493 p3238 p3952 p4203 p4702 : Prop) (h : (¬ p2493) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p4203) ∨ (¬ p4702) ∨ (¬ p3952)) : (p2027) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3952) ∨ (¬ p4203) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial26311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory15567 t (m.theta 1 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule26311 (meaning t m 2027) (meaning t m 2493) (meaning t m 3238) (meaning t m 3952) (meaning t m 4203) (meaning t m 4702) source

theorem rule26312 (p2027 p2498 p2588 p3591 p3830 p4624 p5152 : Prop) (h : p2027 ∨ (¬ p4624) ∨ (¬ p2588) ∨ (¬ p5152) ∨ (¬ p2498) ∨ (¬ p3591) ∨ (¬ p3830)) : (p2027) ∨ (¬ p2498) ∨ (¬ p2588) ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p4624) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial26312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4624)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory15568 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule26312 (meaning t m 2027) (meaning t m 2498) (meaning t m 2588) (meaning t m 3591) (meaning t m 3830) (meaning t m 4624) (meaning t m 5152) source

theorem rule26314 (p2027 p2246 p2449 p2579 p2744 p2761 p2807 p3347 p3956 p4257 p5123 p5580 : Prop) (h : p2027 ∨ (¬ p5123) ∨ (¬ p2449) ∨ (¬ p3956) ∨ (¬ p5580) ∨ (¬ p2246) ∨ (¬ p2807) ∨ (¬ p2744) ∨ (¬ p4257) ∨ (¬ p3347) ∨ (¬ p2579) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2449) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3347) ∨ (¬ p3956) ∨ (¬ p4257) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial26314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory15570 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule26314 (meaning t m 2027) (meaning t m 2246) (meaning t m 2449) (meaning t m 2579) (meaning t m 2744) (meaning t m 2761) (meaning t m 2807) (meaning t m 3347) (meaning t m 3956) (meaning t m 4257) (meaning t m 5123) (meaning t m 5580) source

theorem rule26317 (p2027 p2246 p2744 p2901 p2946 p3055 p3246 p3366 p3584 p4137 p4625 : Prop) (h : p2027 ∨ (¬ p4625) ∨ (¬ p3246) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p2246) ∨ (¬ p3584) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial26317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory15573 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule26317 (meaning t m 2027) (meaning t m 2246) (meaning t m 2744) (meaning t m 2901) (meaning t m 2946) (meaning t m 3055) (meaning t m 3246) (meaning t m 3366) (meaning t m 3584) (meaning t m 4137) (meaning t m 4625) source

theorem rule26321 (p1998 p2027 p2210 p2247 p2688 p2881 p2891 : Prop) (h : p2027 ∨ (¬ p1998) ∨ (¬ p2881) ∨ (¬ p2247) ∨ p2688 ∨ (¬ p2891) ∨ (¬ p2210)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p2881) ∨ (¬ p2891) := by
  classical
  tauto

theorem initial26321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) := by
  have source := ElevenTheory.theory15577 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 5 7) (m.theta 7 8)
  exact rule26321 (meaning t m 1998) (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2688) (meaning t m 2881) (meaning t m 2891) source

theorem rule26335 (p2386 p3096 p4356 : Prop) (h : (¬ p4356) ∨ (¬ p3096) ∨ p2386) : (p2386) ∨ (¬ p3096) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial26335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2386) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory15591 (m.theta 0 6) (m.theta 4 6) (m.theta 5 6)
  exact rule26335 (meaning t m 2386) (meaning t m 3096) (meaning t m 4356) source

theorem rule26345 (p1994 p2027 p2578 p2667 p2727 p2764 p4137 p4154 p4191 : Prop) (h : (¬ p4154) ∨ (¬ p2667) ∨ p2027 ∨ p2764 ∨ (¬ p2578) ∨ (¬ p4191) ∨ (¬ p4137) ∨ (¬ p2727) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2578) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (p2764) ∨ (¬ p4137) ∨ (¬ p4154) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial26345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory15601 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule26345 (meaning t m 1994) (meaning t m 2027) (meaning t m 2578) (meaning t m 2667) (meaning t m 2727) (meaning t m 2764) (meaning t m 4137) (meaning t m 4154) (meaning t m 4191) source

theorem rule26348 (p2027 p2972 p3486 p3570 p4135 p4668 : Prop) (h : (¬ p2972) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p4135) ∨ (¬ p3570)) : (p2027) ∨ (¬ p2972) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4135) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial26348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory15604 t (m.theta 1 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8) (m.theta 7 9)
  exact rule26348 (meaning t m 2027) (meaning t m 2972) (meaning t m 3486) (meaning t m 3570) (meaning t m 4135) (meaning t m 4668) source

theorem rule26352 (p1982 p2027 p2363 p2622 p2774 p2819 p3365 : Prop) (h : p2622 ∨ (¬ p3365) ∨ p2027 ∨ (¬ p2819) ∨ (¬ p2363) ∨ (¬ p1982) ∨ (¬ p2774)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (p2622) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial26352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory15608 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule26352 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2622) (meaning t m 2774) (meaning t m 2819) (meaning t m 3365) source

theorem rule26355 (p2027 p2136 p2246 p2363 p2663 p2744 p3083 p3366 p3389 p3646 p3692 p3742 p3988 p4596 : Prop) (h : (¬ p3366) ∨ (¬ p2136) ∨ (¬ p3692) ∨ (¬ p2363) ∨ (¬ p3646) ∨ (¬ p3988) ∨ (¬ p2663) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p4596) ∨ (¬ p3389) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3389) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p3742) ∨ (¬ p3988) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial26355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory15611 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule26355 (meaning t m 2027) (meaning t m 2136) (meaning t m 2246) (meaning t m 2363) (meaning t m 2663) (meaning t m 2744) (meaning t m 3083) (meaning t m 3366) (meaning t m 3389) (meaning t m 3646) (meaning t m 3692) (meaning t m 3742) (meaning t m 3988) (meaning t m 4596) source

theorem rule26357 (p2027 p2138 p2247 p2744 p3366 p3399 p3527 p3690 p4244 p4666 : Prop) (h : (¬ p3527) ∨ (¬ p4244) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p3399) ∨ (¬ p3690) ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p3366)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial26357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory15613 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule26357 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3399) (meaning t m 3527) (meaning t m 3690) (meaning t m 4244) (meaning t m 4666) source

theorem rule26358 (p2027 p2427 p3246 p3947 p4386 p4702 : Prop) (h : (¬ p4702) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p4386) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial26358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory15614 t (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule26358 (meaning t m 2027) (meaning t m 2427) (meaning t m 3246) (meaning t m 3947) (meaning t m 4386) (meaning t m 4702) source

theorem rule26359 (p2027 p2427 p3516 p3691 p3947 p4386 p4702 : Prop) (h : (¬ p2427) ∨ (¬ p4702) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p4386) ∨ (¬ p3691) ∨ (¬ p3516)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial26359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory15615 t (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule26359 (meaning t m 2027) (meaning t m 2427) (meaning t m 3516) (meaning t m 3691) (meaning t m 3947) (meaning t m 4386) (meaning t m 4702) source

theorem rule26360 (p2027 p2210 p2247 p2744 p2972 p3366 p3425 p3659 p4348 p4450 : Prop) (h : (¬ p3425) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p4348) ∨ (¬ p3659) ∨ (¬ p4450) ∨ (¬ p2972) ∨ (¬ p3366) ∨ (¬ p2744) ∨ p2027) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2972) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial26360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory15616 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule26360 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2744) (meaning t m 2972) (meaning t m 3366) (meaning t m 3425) (meaning t m 3659) (meaning t m 4348) (meaning t m 4450) source

theorem rule26361 (p2027 p2579 p2588 p3449 p3707 p4107 p4351 p4444 p4669 p5193 : Prop) (h : (¬ p4107) ∨ (¬ p4669) ∨ (¬ p2588) ∨ (¬ p4351) ∨ (¬ p3707) ∨ (¬ p4444) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p5193)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3449) ∨ (¬ p3707) ∨ (¬ p4107) ∨ (¬ p4351) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial26361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4351)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory15617 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 8) (m.theta 1 9) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26361 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 3449) (meaning t m 3707) (meaning t m 4107) (meaning t m 4351) (meaning t m 4444) (meaning t m 4669) (meaning t m 5193) source

theorem rule26363 (p2027 p2246 p2449 p2608 p2744 p2761 p2807 p3860 p4353 p5123 p5612 : Prop) (h : (¬ p2744) ∨ (¬ p4353) ∨ (¬ p2761) ∨ (¬ p2449) ∨ (¬ p2246) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p5612) ∨ (¬ p5123) ∨ (¬ p3860)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2449) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3860) ∨ (¬ p4353) ∨ (¬ p5123) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial26363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4353)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory15619 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 8) (m.theta 3 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule26363 (meaning t m 2027) (meaning t m 2246) (meaning t m 2449) (meaning t m 2608) (meaning t m 2744) (meaning t m 2761) (meaning t m 2807) (meaning t m 3860) (meaning t m 4353) (meaning t m 5123) (meaning t m 5612) source

theorem rule26364 (p2027 p2246 p2264 p2608 p2744 p2807 p3860 p3941 p4261 p5122 : Prop) (h : (¬ p2807) ∨ (¬ p2264) ∨ (¬ p2246) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p5122) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3941) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3860) ∨ (¬ p3941) ∨ (¬ p4261) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial26364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory15620 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule26364 (meaning t m 2027) (meaning t m 2246) (meaning t m 2264) (meaning t m 2608) (meaning t m 2744) (meaning t m 2807) (meaning t m 3860) (meaning t m 3941) (meaning t m 4261) (meaning t m 5122) source

theorem rule26366 (p2027 p2246 p2542 p2651 p2744 p2982 p3366 p3425 p3659 p4348 p4450 : Prop) (h : p2027 ∨ (¬ p4450) ∨ (¬ p3659) ∨ (¬ p2542) ∨ (¬ p4348) ∨ (¬ p3425) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2651) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2982) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial26366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory15622 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule26366 (meaning t m 2027) (meaning t m 2246) (meaning t m 2542) (meaning t m 2651) (meaning t m 2744) (meaning t m 2982) (meaning t m 3366) (meaning t m 3425) (meaning t m 3659) (meaning t m 4348) (meaning t m 4450) source

theorem rule26368 (p2027 p2247 p2744 p3366 p3425 p3449 p3659 p3969 p4348 p4446 p5122 : Prop) (h : (¬ p3425) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3449) ∨ (¬ p3969) ∨ (¬ p5122) ∨ (¬ p4446) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p3659) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3449) ∨ (¬ p3659) ∨ (¬ p3969) ∨ (¬ p4348) ∨ (¬ p4446) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial26368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory15624 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule26368 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3425) (meaning t m 3449) (meaning t m 3659) (meaning t m 3969) (meaning t m 4348) (meaning t m 4446) (meaning t m 5122) source

theorem rule26372 (p2027 p2246 p2608 p2744 p2881 p2901 p2946 p3817 p4366 p4666 : Prop) (h : (¬ p4666) ∨ p2027 ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p2608) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial26372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory15628 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule26372 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 2881) (meaning t m 2901) (meaning t m 2946) (meaning t m 3817) (meaning t m 4366) (meaning t m 4666) source

theorem rule26373 (p2027 p2247 p2744 p2780 p3366 p3399 p3527 p3822 p4107 p4666 : Prop) (h : (¬ p4107) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p2780) ∨ (¬ p3527) ∨ (¬ p3366) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3399)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial26373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory15629 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule26373 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 2780) (meaning t m 3366) (meaning t m 3399) (meaning t m 3527) (meaning t m 3822) (meaning t m 4107) (meaning t m 4666) source

theorem rule26374 (p1995 p2027 p2764 p3238 p3556 p3690 p4031 p4381 : Prop) (h : (¬ p1995) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p3238) ∨ (¬ p4381) ∨ p2764 ∨ p2027 ∨ (¬ p4031)) : (¬ p1995) ∨ (p2027) ∨ (p2764) ∨ (¬ p3238) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p4031) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial26374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory15630 t (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule26374 (meaning t m 1995) (meaning t m 2027) (meaning t m 2764) (meaning t m 3238) (meaning t m 3556) (meaning t m 3690) (meaning t m 4031) (meaning t m 4381) source

theorem rule26375 (p2027 p2307 p2630 p3567 p3822 p4841 p4972 : Prop) (h : (¬ p3822) ∨ (¬ p4841) ∨ (¬ p2630) ∨ (¬ p4972) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p3567)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2630) ∨ (¬ p3567) ∨ (¬ p3822) ∨ (¬ p4841) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial26375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4841)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory15631 t (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule26375 (meaning t m 2027) (meaning t m 2307) (meaning t m 2630) (meaning t m 3567) (meaning t m 3822) (meaning t m 4841) (meaning t m 4972) source

theorem rule26376 (p3461 p3680 p5045 : Prop) (h : (¬ p5045) ∨ (¬ p3461) ∨ p3680) : (¬ p3461) ∨ (p3680) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial26376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3461)) ∨ (meaning t m 3680) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory15632 (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule26376 (meaning t m 3461) (meaning t m 3680) (meaning t m 5045) source

theorem rule26377 (p2027 p2651 p2952 p2992 p4154 p4972 : Prop) (h : (¬ p4154) ∨ (¬ p2952) ∨ (¬ p4972) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p2992)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4154) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial26377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory15633 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule26377 (meaning t m 2027) (meaning t m 2651) (meaning t m 2952) (meaning t m 2992) (meaning t m 4154) (meaning t m 4972) source

theorem rule26378 (p2027 p2247 p2744 p3093 p3323 p3366 p3425 p3659 p3922 p4330 p4348 : Prop) (h : (¬ p4330) ∨ (¬ p2744) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p3425) ∨ (¬ p2247) ∨ (¬ p3659) ∨ (¬ p3922) ∨ (¬ p4348) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3093) ∨ (¬ p3323) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3922) ∨ (¬ p4330) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial26378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory15634 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 7) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule26378 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3093) (meaning t m 3323) (meaning t m 3366) (meaning t m 3425) (meaning t m 3659) (meaning t m 3922) (meaning t m 4330) (meaning t m 4348) source

theorem rule26392 (p2027 p2246 p2363 p2383 p2744 p3055 p3366 p3684 p3880 p3987 p4348 p4905 : Prop) (h : (¬ p3880) ∨ (¬ p3055) ∨ (¬ p3987) ∨ (¬ p2246) ∨ (¬ p2383) ∨ (¬ p2363) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p4348) ∨ (¬ p4905) ∨ p2027 ∨ (¬ p3684)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p3987) ∨ (¬ p4348) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial26392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory15648 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26392 (meaning t m 2027) (meaning t m 2246) (meaning t m 2363) (meaning t m 2383) (meaning t m 2744) (meaning t m 3055) (meaning t m 3366) (meaning t m 3684) (meaning t m 3880) (meaning t m 3987) (meaning t m 4348) (meaning t m 4905) source

theorem rule26393 (p2027 p2247 p2476 p2534 p2744 p3063 p3093 p3146 p3366 p3905 p4134 : Prop) (h : (¬ p2476) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3146) ∨ (¬ p2534) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p3366) ∨ (¬ p3093) ∨ (¬ p4134)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p4134) := by
  classical
  tauto

theorem initial26393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4134)) := by
  have source := ElevenTheory.theory15649 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule26393 (meaning t m 2027) (meaning t m 2247) (meaning t m 2476) (meaning t m 2534) (meaning t m 2744) (meaning t m 3063) (meaning t m 3093) (meaning t m 3146) (meaning t m 3366) (meaning t m 3905) (meaning t m 4134) source

theorem rule26396 (p2027 p2630 p2807 p3292 p3572 p5172 : Prop) (h : (¬ p3572) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p5172) ∨ (¬ p3292)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2807) ∨ (¬ p3292) ∨ (¬ p3572) ∨ (¬ p5172) := by
  classical
  tauto

theorem initial26396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 5172)) := by
  have source := ElevenTheory.theory15652 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 3 9)
  exact rule26396 (meaning t m 2027) (meaning t m 2630) (meaning t m 2807) (meaning t m 3292) (meaning t m 3572) (meaning t m 5172) source

theorem rule26406 (p2027 p2247 p2744 p3471 p3588 p3589 : Prop) (h : (¬ p3588) ∨ (¬ p3589) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p2247) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3471) ∨ (¬ p3588) ∨ (¬ p3589) := by
  classical
  tauto

theorem initial26406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3589)) := by
  have source := ElevenTheory.theory15662 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7)
  exact rule26406 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3471) (meaning t m 3588) (meaning t m 3589) source

theorem rule26407 (p2027 p2248 p2651 p3016 p3548 p3564 p4330 p4348 p4366 : Prop) (h : p2027 ∨ (¬ p3548) ∨ (¬ p4330) ∨ (¬ p3564) ∨ (¬ p2248) ∨ (¬ p4366) ∨ (¬ p3016) ∨ (¬ p4348) ∨ (¬ p2651)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3548) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial26407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory15663 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule26407 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 3016) (meaning t m 3548) (meaning t m 3564) (meaning t m 4330) (meaning t m 4348) (meaning t m 4366) source

theorem rule26409 (p2027 p2475 p2499 p2518 p3324 p4113 p4973 : Prop) (h : (¬ p4973) ∨ (¬ p3324) ∨ (¬ p2475) ∨ (¬ p2499) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p4113)) : (p2027) ∨ (¬ p2475) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p3324) ∨ (¬ p4113) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial26409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory15665 t (m.theta 0 8) (m.theta 1 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule26409 (meaning t m 2027) (meaning t m 2475) (meaning t m 2499) (meaning t m 2518) (meaning t m 3324) (meaning t m 4113) (meaning t m 4973) source

theorem rule26410 (p1998 p2027 p2177 p2295 p2622 p2743 p2829 p4328 : Prop) (h : (¬ p4328) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2743) ∨ (¬ p2177) ∨ p2622 ∨ (¬ p2829)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial26410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory15666 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule26410 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 2622) (meaning t m 2743) (meaning t m 2829) (meaning t m 4328) source

theorem rule26411 (p1998 p2027 p2177 p2295 p2622 p2743 p2753 p2774 p4328 : Prop) (h : (¬ p4328) ∨ (¬ p2295) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2753) ∨ p2622 ∨ (¬ p2743) ∨ (¬ p2774)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial26411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory15667 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule26411 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 2622) (meaning t m 2743) (meaning t m 2753) (meaning t m 2774) (meaning t m 4328) source

theorem rule26413 (p1981 p2027 p2122 p2611 p2668 p2774 p3568 : Prop) (h : p2027 ∨ (¬ p2122) ∨ p2611 ∨ (¬ p2668) ∨ (¬ p2774) ∨ (¬ p3568) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2122) ∨ (p2611) ∨ (¬ p2668) ∨ (¬ p2774) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial26413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory15669 t (m.theta 0 2) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule26413 (meaning t m 1981) (meaning t m 2027) (meaning t m 2122) (meaning t m 2611) (meaning t m 2668) (meaning t m 2774) (meaning t m 3568) source

theorem rule26416 (p2027 p2192 p2241 p2750 p3369 p3371 p3646 : Prop) (h : (¬ p2241) ∨ (¬ p3646) ∨ (¬ p3369) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p3371) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3369) ∨ (¬ p3371) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial26416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory15672 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 5 6)
  exact rule26416 (meaning t m 2027) (meaning t m 2192) (meaning t m 2241) (meaning t m 2750) (meaning t m 3369) (meaning t m 3371) (meaning t m 3646) source

theorem rule26419 (p2027 p2437 p2911 p3359 p4636 p4666 : Prop) (h : (¬ p4666) ∨ (¬ p3359) ∨ (¬ p2437) ∨ (¬ p4636) ∨ p2027 ∨ (¬ p2911)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2911) ∨ (¬ p3359) ∨ (¬ p4636) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial26419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4636)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory15675 t (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 8) (m.theta 7 9)
  exact rule26419 (meaning t m 2027) (meaning t m 2437) (meaning t m 2911) (meaning t m 3359) (meaning t m 4636) (meaning t m 4666) source

theorem rule26420 (p4118 p4261 p4288 : Prop) (h : (¬ p4288) ∨ (¬ p4261) ∨ p4118) : (p4118) ∨ (¬ p4261) ∨ (¬ p4288) := by
  classical
  tauto

theorem initial26420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4118) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4288)) := by
  have source := ElevenTheory.theory15676 (m.theta 1 8) (m.theta 3 8) (m.theta 8 9)
  exact rule26420 (meaning t m 4118) (meaning t m 4261) (meaning t m 4288) source

theorem rule26424 (p2005 p2027 p2766 p3266 p3422 p4425 p5160 : Prop) (h : (¬ p2005) ∨ p2766 ∨ p2027 ∨ (¬ p5160) ∨ (¬ p3266) ∨ (¬ p3422) ∨ (¬ p4425)) : (¬ p2005) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3422) ∨ (¬ p4425) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial26424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory15680 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26424 (meaning t m 2005) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3422) (meaning t m 4425) (meaning t m 5160) source

theorem rule26427 (p2027 p2313 p3309 p3361 p3585 p3983 p4749 p4869 : Prop) (h : (¬ p3983) ∨ (¬ p4869) ∨ (¬ p2313) ∨ (¬ p3309) ∨ (¬ p3361) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p4749)) : (p2027) ∨ (¬ p2313) ∨ (¬ p3309) ∨ (¬ p3361) ∨ (¬ p3585) ∨ (¬ p3983) ∨ (¬ p4749) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial26427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory15683 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 6 7)
  exact rule26427 (meaning t m 2027) (meaning t m 2313) (meaning t m 3309) (meaning t m 3361) (meaning t m 3585) (meaning t m 3983) (meaning t m 4749) (meaning t m 4869) source

theorem rule26431 (p2027 p2737 p2807 p3588 p4777 p4790 : Prop) (h : (¬ p3588) ∨ (¬ p4790) ∨ (¬ p2737) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p4777)) : (p2027) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p3588) ∨ (¬ p4777) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4777)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15687 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7)
  exact rule26431 (meaning t m 2027) (meaning t m 2737) (meaning t m 2807) (meaning t m 3588) (meaning t m 4777) (meaning t m 4790) source

theorem rule26433 (p2027 p2177 p2528 p4107 p4438 p4445 : Prop) (h : (¬ p4445) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p4438) ∨ (¬ p2177) ∨ (¬ p4107)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2528) ∨ (¬ p4107) ∨ (¬ p4438) ∨ (¬ p4445) := by
  classical
  tauto

theorem initial26433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4445)) := by
  have source := ElevenTheory.theory15689 t (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule26433 (meaning t m 2027) (meaning t m 2177) (meaning t m 2528) (meaning t m 4107) (meaning t m 4438) (meaning t m 4445) source

theorem rule26434 (p2027 p2341 p2963 p3553 p4104 p4572 : Prop) (h : (¬ p4104) ∨ (¬ p3553) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p4572) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2963) ∨ (¬ p3553) ∨ (¬ p4104) ∨ (¬ p4572) := by
  classical
  tauto

theorem initial26434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4572)) := by
  have source := ElevenTheory.theory15690 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8)
  exact rule26434 (meaning t m 2027) (meaning t m 2341) (meaning t m 2963) (meaning t m 3553) (meaning t m 4104) (meaning t m 4572) source

theorem rule26435 (p2027 p2299 p2470 p3540 p4370 p4712 p5307 : Prop) (h : (¬ p4370) ∨ (¬ p3540) ∨ (¬ p2299) ∨ (¬ p4712) ∨ p2027 ∨ (¬ p5307) ∨ (¬ p2470)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2470) ∨ (¬ p3540) ∨ (¬ p4370) ∨ (¬ p4712) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial26435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4370)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory15691 t (m.theta 0 4) (m.theta 1 8) (m.theta 4 7) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule26435 (meaning t m 2027) (meaning t m 2299) (meaning t m 2470) (meaning t m 3540) (meaning t m 4370) (meaning t m 4712) (meaning t m 5307) source

theorem rule26437 (p2027 p2341 p3055 p3548 p3576 p3819 p5086 : Prop) (h : (¬ p3548) ∨ (¬ p3576) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p5086) ∨ (¬ p3055) ∨ (¬ p3819)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3055) ∨ (¬ p3548) ∨ (¬ p3576) ∨ (¬ p3819) ∨ (¬ p5086) := by
  classical
  tauto

theorem initial26437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 5086)) := by
  have source := ElevenTheory.theory15693 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7) (m.theta 7 8)
  exact rule26437 (meaning t m 2027) (meaning t m 2341) (meaning t m 3055) (meaning t m 3548) (meaning t m 3576) (meaning t m 3819) (meaning t m 5086) source

theorem rule26441 (p2027 p2946 p3115 p4385 p4392 p4790 : Prop) (h : p2027 ∨ (¬ p2946) ∨ (¬ p4392) ∨ (¬ p4790) ∨ (¬ p3115) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p4385) ∨ (¬ p4392) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15697 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 9)
  exact rule26441 (meaning t m 2027) (meaning t m 2946) (meaning t m 3115) (meaning t m 4385) (meaning t m 4392) (meaning t m 4790) source

theorem rule26442 (p1978 p3043 p4032 p4138 p4503 : Prop) (h : (¬ p4032) ∨ (¬ p1978) ∨ p3043 ∨ p4503 ∨ (¬ p4138)) : (¬ p1978) ∨ (p3043) ∨ (¬ p4032) ∨ (¬ p4138) ∨ (p4503) := by
  classical
  tauto

theorem initial26442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4138)) ∨ (meaning t m 4503) := by
  have source := ElevenTheory.theory15698 t (m.theta 0 5) (m.theta 5 9) (m.theta 6 8) (m.theta 7 8)
  exact rule26442 (meaning t m 1978) (meaning t m 3043) (meaning t m 4032) (meaning t m 4138) (meaning t m 4503) source

theorem rule26444 (p2027 p2274 p2312 p2341 p3548 p4024 p4105 p4889 : Prop) (h : (¬ p4024) ∨ (¬ p4889) ∨ (¬ p4105) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p2341) ∨ (¬ p2312)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3548) ∨ (¬ p4024) ∨ (¬ p4105) ∨ (¬ p4889) := by
  classical
  tauto

theorem initial26444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 4889)) := by
  have source := ElevenTheory.theory15700 t (m.theta 0 7) (m.theta 1 6) (m.theta 1 7) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule26444 (meaning t m 2027) (meaning t m 2274) (meaning t m 2312) (meaning t m 2341) (meaning t m 3548) (meaning t m 4024) (meaning t m 4105) (meaning t m 4889) source

theorem rule26445 (p2027 p2319 p2387 p3516 p4107 p4501 : Prop) (h : p2027 ∨ (¬ p3516) ∨ (¬ p2319) ∨ (¬ p4107) ∨ (¬ p4501) ∨ (¬ p2387)) : (p2027) ∨ (¬ p2319) ∨ (¬ p2387) ∨ (¬ p3516) ∨ (¬ p4107) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial26445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory15701 t (m.theta 0 6) (m.theta 0 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule26445 (meaning t m 2027) (meaning t m 2319) (meaning t m 2387) (meaning t m 3516) (meaning t m 4107) (meaning t m 4501) source

theorem rule26446 (p2027 p2589 p2608 p2839 p3695 p5193 : Prop) (h : (¬ p2608) ∨ p2027 ∨ (¬ p5193) ∨ (¬ p3695) ∨ (¬ p2589) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3695) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial26446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory15702 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 4 5)
  exact rule26446 (meaning t m 2027) (meaning t m 2589) (meaning t m 2608) (meaning t m 2839) (meaning t m 3695) (meaning t m 5193) source

theorem rule26449 (p2011 p2027 p2598 p2622 p2850 p2982 p3365 : Prop) (h : (¬ p3365) ∨ (¬ p2850) ∨ p2027 ∨ p2622 ∨ (¬ p2982) ∨ (¬ p2011) ∨ (¬ p2598)) : (¬ p2011) ∨ (p2027) ∨ (¬ p2598) ∨ (p2622) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial26449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory15705 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9)
  exact rule26449 (meaning t m 2011) (meaning t m 2027) (meaning t m 2598) (meaning t m 2622) (meaning t m 2850) (meaning t m 2982) (meaning t m 3365) source

theorem rule26451 (p2027 p3178 p3767 p4035 p4461 p4790 p5284 : Prop) (h : (¬ p4461) ∨ (¬ p3178) ∨ (¬ p4035) ∨ (¬ p4790) ∨ p2027 ∨ (¬ p5284) ∨ (¬ p3767)) : (p2027) ∨ (¬ p3178) ∨ (¬ p3767) ∨ (¬ p4035) ∨ (¬ p4461) ∨ (¬ p4790) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial26451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3178)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4461)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory15707 t (m.theta 0 3) (m.theta 0 8) (m.theta 0 9) (m.theta 2 3) (m.theta 3 9) (m.theta 9 10)
  exact rule26451 (meaning t m 2027) (meaning t m 3178) (meaning t m 3767) (meaning t m 4035) (meaning t m 4461) (meaning t m 4790) (meaning t m 5284) source

theorem rule26453 (p2901 p3568 p4140 p4153 : Prop) (h : (¬ p3568) ∨ (¬ p4140) ∨ (¬ p2901) ∨ (¬ p4153)) : (¬ p2901) ∨ (¬ p3568) ∨ (¬ p4140) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial26453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory15709 (m.theta 3 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7)
  exact rule26453 (meaning t m 2901) (meaning t m 3568) (meaning t m 4140) (meaning t m 4153) source

theorem rule26454 (p2027 p2104 p2132 p2860 p4312 p4507 p4963 : Prop) (h : (¬ p4963) ∨ (¬ p2132) ∨ (¬ p4312) ∨ (¬ p4507) ∨ (¬ p2104) ∨ p2027 ∨ (¬ p2860)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p4312) ∨ (¬ p4507) ∨ (¬ p4963) := by
  classical
  tauto

theorem initial26454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 4963)) := by
  have source := ElevenTheory.theory15710 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 8) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8)
  exact rule26454 (meaning t m 2027) (meaning t m 2104) (meaning t m 2132) (meaning t m 2860) (meaning t m 4312) (meaning t m 4507) (meaning t m 4963) source

theorem rule26458 (p2027 p2156 p2958 p3952 p4315 p4790 : Prop) (h : (¬ p2156) ∨ (¬ p2958) ∨ (¬ p3952) ∨ (¬ p4790) ∨ p2027 ∨ (¬ p4315)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2958) ∨ (¬ p3952) ∨ (¬ p4315) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15714 t (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6)
  exact rule26458 (meaning t m 2027) (meaning t m 2156) (meaning t m 2958) (meaning t m 3952) (meaning t m 4315) (meaning t m 4790) source

theorem rule26459 (p2027 p2331 p2737 p3688 p4337 p4790 : Prop) (h : (¬ p3688) ∨ (¬ p4790) ∨ (¬ p2737) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4337)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4337) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15715 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6)
  exact rule26459 (meaning t m 2027) (meaning t m 2331) (meaning t m 2737) (meaning t m 3688) (meaning t m 4337) (meaning t m 4790) source

theorem rule26460 (p1975 p2027 p2114 p2137 p2156 p2299 p2839 p2881 p3872 : Prop) (h : p2114 ∨ (¬ p3872) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2299) ∨ (¬ p2156) ∨ (¬ p2881) ∨ (¬ p2839) ∨ (¬ p2137)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2299) ∨ (¬ p2839) ∨ (¬ p2881) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial26460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory15716 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule26460 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2156) (meaning t m 2299) (meaning t m 2839) (meaning t m 2881) (meaning t m 3872) source

theorem rule26461 (p2027 p2437 p2651 p2952 p3879 p4646 : Prop) (h : (¬ p3879) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p4646) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial26461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory15717 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7)
  exact rule26461 (meaning t m 2027) (meaning t m 2437) (meaning t m 2651) (meaning t m 2952) (meaning t m 3879) (meaning t m 4646) source

theorem rule26465 (p2027 p2138 p2241 p3027 p3931 p4322 p4385 p4736 p4826 : Prop) (h : (¬ p2138) ∨ (¬ p3931) ∨ (¬ p4736) ∨ (¬ p2241) ∨ (¬ p3027) ∨ (¬ p4826) ∨ p2027 ∨ (¬ p4385) ∨ (¬ p4322)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4736) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial26465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory15721 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule26465 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 3027) (meaning t m 3931) (meaning t m 4322) (meaning t m 4385) (meaning t m 4736) (meaning t m 4826) source

theorem rule26466 (p2027 p2241 p2264 p3027 p4416 p4592 : Prop) (h : (¬ p2241) ∨ (¬ p4592) ∨ (¬ p3027) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p4416)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p4416) ∨ (¬ p4592) := by
  classical
  tauto

theorem initial26466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4416)) ∨ (¬ (meaning t m 4592)) := by
  have source := ElevenTheory.theory15722 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 3) (m.theta 3 7) (m.theta 7 8)
  exact rule26466 (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 3027) (meaning t m 4416) (meaning t m 4592) source

theorem rule26467 (p2027 p2807 p3032 p3527 p3659 p4357 p4790 : Prop) (h : (¬ p4357) ∨ (¬ p4790) ∨ p2027 ∨ (¬ p3032) ∨ (¬ p3527) ∨ (¬ p2807) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2807) ∨ (¬ p3032) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p4357) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4357)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15723 t (m.theta 0 3) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule26467 (meaning t m 2027) (meaning t m 2807) (meaning t m 3032) (meaning t m 3527) (meaning t m 3659) (meaning t m 4357) (meaning t m 4790) source

theorem rule26472 (p3548 p3570 p4909 : Prop) (h : (¬ p3570) ∨ (¬ p4909) ∨ p3548) : (p3548) ∨ (¬ p3570) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial26472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3548) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory15728 (m.theta 1 7) (m.theta 5 7) (m.theta 7 8)
  exact rule26472 (meaning t m 3548) (meaning t m 3570) (meaning t m 4909) source

theorem rule26477 (p2027 p2383 p2810 p3324 p3987 p4194 p4790 : Prop) (h : (¬ p4790) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p3324) ∨ (¬ p4194) ∨ (¬ p2383) ∨ (¬ p3987)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2810) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4194) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15733 t (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule26477 (meaning t m 2027) (meaning t m 2383) (meaning t m 2810) (meaning t m 3324) (meaning t m 3987) (meaning t m 4194) (meaning t m 4790) source

theorem rule26479 (p1975 p2027 p2230 p2233 p2274 p2440 p3016 p4203 : Prop) (h : (¬ p3016) ∨ p2233 ∨ (¬ p2274) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2440) ∨ (¬ p4203) ∨ (¬ p2230)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2274) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial26479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory15735 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule26479 (meaning t m 1975) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2274) (meaning t m 2440) (meaning t m 3016) (meaning t m 4203) source

theorem rule26480 (p2027 p2383 p3324 p3987 p4195 p4790 : Prop) (h : p2027 ∨ (¬ p3987) ∨ (¬ p4790) ∨ (¬ p3324) ∨ (¬ p2383) ∨ (¬ p4195)) : (p2027) ∨ (¬ p2383) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4195) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15736 t (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8)
  exact rule26480 (meaning t m 2027) (meaning t m 2383) (meaning t m 3324) (meaning t m 3987) (meaning t m 4195) (meaning t m 4790) source

theorem rule26481 (p2417 p3434 p3658 : Prop) (h : (¬ p2417) ∨ (¬ p3658) ∨ p3434) : (¬ p2417) ∨ (p3434) ∨ (¬ p3658) := by
  classical
  tauto

theorem initial26481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2417)) ∨ (meaning t m 3434) ∨ (¬ (meaning t m 3658)) := by
  have source := ElevenTheory.theory15737 (m.theta 2 7) (m.theta 4 7) (m.theta 7 9)
  exact rule26481 (meaning t m 2417) (meaning t m 3434) (meaning t m 3658) source

theorem rule26486 (p2027 p2588 p3051 p3646 p3958 p4140 : Prop) (h : (¬ p4140) ∨ (¬ p2588) ∨ (¬ p3958) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p3051)) : (p2027) ∨ (¬ p2588) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3958) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial26486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory15742 t (m.theta 0 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule26486 (meaning t m 2027) (meaning t m 2588) (meaning t m 3051) (meaning t m 3646) (meaning t m 3958) (meaning t m 4140) source

theorem rule26489 (p3483 p4024 p4026 : Prop) (h : (¬ p4026) ∨ (¬ p4024) ∨ (¬ p3483)) : (¬ p3483) ∨ (¬ p4024) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial26489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory15745 (m.theta 1 6) (m.theta 2 6) (m.theta 6 9)
  exact rule26489 (meaning t m 3483) (meaning t m 4024) (meaning t m 4026) source

theorem rule26499 (p2138 p3366 p3583 : Prop) (h : (¬ p2138) ∨ (¬ p3366) ∨ p3583) : (¬ p2138) ∨ (¬ p3366) ∨ (p3583) := by
  classical
  tauto

theorem initial26499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3366)) ∨ (meaning t m 3583) := by
  have source := ElevenTheory.theory15755 (m.theta 0 2) (m.theta 1 2) (m.theta 2 5)
  exact rule26499 (meaning t m 2138) (meaning t m 3366) (meaning t m 3583) source

theorem rule26500 (p2027 p2241 p2449 p2780 p3027 p3950 p4347 p4358 p4736 : Prop) (h : (¬ p4358) ∨ (¬ p2780) ∨ (¬ p2241) ∨ (¬ p3950) ∨ (¬ p2449) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2780) ∨ (¬ p3027) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial26500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory15756 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule26500 (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 2780) (meaning t m 3027) (meaning t m 3950) (meaning t m 4347) (meaning t m 4358) (meaning t m 4736) source

theorem rule26501 (p3744 p4137 p4203 : Prop) (h : (¬ p4203) ∨ (¬ p4137) ∨ p3744) : (p3744) ∨ (¬ p4137) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial26501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3744) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory15757 (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule26501 (meaning t m 3744) (meaning t m 4137) (meaning t m 4203) source

theorem rule26502 (p2027 p3323 p3568 p3690 p4556 p5299 p5379 : Prop) (h : (¬ p3323) ∨ (¬ p4556) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p5299) ∨ (¬ p5379)) : (p2027) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3690) ∨ (¬ p4556) ∨ (¬ p5299) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial26502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 5299)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory15758 t (m.theta 0 9) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule26502 (meaning t m 2027) (meaning t m 3323) (meaning t m 3568) (meaning t m 3690) (meaning t m 4556) (meaning t m 5299) (meaning t m 5379) source

theorem rule26504 (p2641 p3027 p4156 : Prop) (h : (¬ p4156) ∨ (¬ p2641) ∨ p3027) : (¬ p2641) ∨ (p3027) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial26504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (meaning t m 3027) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory15760 (m.theta 1 3) (m.theta 3 6) (m.theta 3 7)
  exact rule26504 (meaning t m 2641) (meaning t m 3027) (meaning t m 4156) source

theorem rule26505 (p2027 p2737 p2946 p3583 p4316 p4790 : Prop) (h : (¬ p2946) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p4790) ∨ (¬ p4316)) : (p2027) ∨ (¬ p2737) ∨ (¬ p2946) ∨ (¬ p3583) ∨ (¬ p4316) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15761 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5)
  exact rule26505 (meaning t m 2027) (meaning t m 2737) (meaning t m 2946) (meaning t m 3583) (meaning t m 4316) (meaning t m 4790) source

theorem rule26506 (p1981 p2027 p2148 p2156 p2819 p3319 p3917 p3957 : Prop) (h : (¬ p2819) ∨ (¬ p3957) ∨ p2148 ∨ p2027 ∨ (¬ p2156) ∨ (¬ p3319) ∨ (¬ p1981) ∨ (¬ p3917)) : (¬ p1981) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2819) ∨ (¬ p3319) ∨ (¬ p3917) ∨ (¬ p3957) := by
  classical
  tauto

theorem initial26506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3957)) := by
  have source := ElevenTheory.theory15762 t (m.theta 0 5) (m.theta 1 6) (m.theta 2 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule26506 (meaning t m 1981) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2819) (meaning t m 3319) (meaning t m 3917) (meaning t m 3957) source

theorem rule26507 (p2027 p2417 p2891 p4363 p4382 p4647 : Prop) (h : p2027 ∨ (¬ p4647) ∨ (¬ p4382) ∨ (¬ p2891) ∨ (¬ p2417) ∨ (¬ p4363)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2891) ∨ (¬ p4363) ∨ (¬ p4382) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial26507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory15763 t (m.theta 1 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule26507 (meaning t m 2027) (meaning t m 2417) (meaning t m 2891) (meaning t m 4363) (meaning t m 4382) (meaning t m 4647) source

theorem rule26508 (p2027 p2187 p2563 p3923 p4512 p4629 : Prop) (h : p2027 ∨ (¬ p4629) ∨ (¬ p4512) ∨ (¬ p2187) ∨ (¬ p3923) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2563) ∨ (¬ p3923) ∨ (¬ p4512) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial26508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory15764 t (m.theta 1 5) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule26508 (meaning t m 2027) (meaning t m 2187) (meaning t m 2563) (meaning t m 3923) (meaning t m 4512) (meaning t m 4629) source

theorem rule26511 (p2027 p2573 p2663 p2810 p3574 p4790 : Prop) (h : (¬ p2573) ∨ (¬ p2663) ∨ (¬ p4790) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p3574)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p3574) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15767 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6)
  exact rule26511 (meaning t m 2027) (meaning t m 2573) (meaning t m 2663) (meaning t m 2810) (meaning t m 3574) (meaning t m 4790) source

theorem rule26519 (p2996 p4111 p4112 : Prop) (h : (¬ p4111) ∨ (¬ p4112) ∨ p2996) : (p2996) ∨ (¬ p4111) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial26519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2996) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory15775 (m.theta 1 3) (m.theta 3 4) (m.theta 3 7)
  exact rule26519 (meaning t m 2996) (meaning t m 4111) (meaning t m 4112) source

theorem rule26522 (p3547 p4477 p4794 : Prop) (h : (¬ p3547) ∨ (¬ p4477) ∨ p4794) : (¬ p3547) ∨ (¬ p4477) ∨ (p4794) := by
  classical
  tauto

theorem initial26522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 4477)) ∨ (meaning t m 4794) := by
  have source := ElevenTheory.theory15778 t (m.theta 1 7) (m.theta 2 7) (m.theta 6 7)
  exact rule26522 (meaning t m 3547) (meaning t m 4477) (meaning t m 4794) source

theorem rule26523 (p3547 p4559 p4911 : Prop) (h : (¬ p4559) ∨ (¬ p3547) ∨ p4911) : (¬ p3547) ∨ (¬ p4559) ∨ (p4911) := by
  classical
  tauto

theorem initial26523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 4559)) ∨ (meaning t m 4911) := by
  have source := ElevenTheory.theory15779 t (m.theta 1 7) (m.theta 5 7) (m.theta 6 7)
  exact rule26523 (meaning t m 3547) (meaning t m 4559) (meaning t m 4911) source

theorem rule26524 (p2027 p2807 p2992 p2996 p4316 p4392 p4790 : Prop) (h : (¬ p2807) ∨ (¬ p2996) ∨ (¬ p2992) ∨ (¬ p4316) ∨ (¬ p4392) ∨ p2027 ∨ (¬ p4790)) : (p2027) ∨ (¬ p2807) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p4316) ∨ (¬ p4392) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15780 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7)
  exact rule26524 (meaning t m 2027) (meaning t m 2807) (meaning t m 2992) (meaning t m 2996) (meaning t m 4316) (meaning t m 4392) (meaning t m 4790) source

theorem rule26527 (p4235 p4241 p4320 : Prop) (h : (¬ p4241) ∨ (¬ p4320) ∨ p4235) : (p4235) ∨ (¬ p4241) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial26527 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4235) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory15783 (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule26527 (meaning t m 4235) (meaning t m 4241) (meaning t m 4320) source

theorem rule26528 (p2027 p2177 p2553 p3659 p3689 p5222 : Prop) (h : (¬ p2177) ∨ (¬ p5222) ∨ p2027 ∨ (¬ p3689) ∨ (¬ p2553) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3659) ∨ (¬ p3689) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial26528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory15784 t (m.theta 2 6) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule26528 (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 3659) (meaning t m 3689) (meaning t m 5222) source

theorem rule26529 (p1978 p2027 p2462 p2860 p3646 p4107 p4244 p4275 : Prop) (h : (¬ p3646) ∨ (¬ p1978) ∨ p2027 ∨ (¬ p4107) ∨ p2462 ∨ (¬ p4275) ∨ (¬ p2860) ∨ (¬ p4244)) : (¬ p1978) ∨ (p2027) ∨ (p2462) ∨ (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4244) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial26529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory15785 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule26529 (meaning t m 1978) (meaning t m 2027) (meaning t m 2462) (meaning t m 2860) (meaning t m 3646) (meaning t m 4107) (meaning t m 4244) (meaning t m 4275) source

theorem rule26530 (p2027 p2651 p2992 p4111 p4315 p4790 : Prop) (h : (¬ p2651) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p4790) ∨ (¬ p4315)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4315) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26530 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15786 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule26530 (meaning t m 2027) (meaning t m 2651) (meaning t m 2992) (meaning t m 4111) (meaning t m 4315) (meaning t m 4790) source

theorem rule26534 (p2027 p2553 p3097 p3646 p3660 p4533 : Prop) (h : p2027 ∨ (¬ p2553) ∨ (¬ p3646) ∨ (¬ p4533) ∨ (¬ p3660) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3660) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial26534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory15790 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule26534 (meaning t m 2027) (meaning t m 2553) (meaning t m 3097) (meaning t m 3646) (meaning t m 3660) (meaning t m 4533) source

theorem rule26536 (p1976 p2027 p2765 p3055 p3367 p3583 p3758 : Prop) (h : p2027 ∨ (¬ p3758) ∨ p2765 ∨ (¬ p1976) ∨ (¬ p3055) ∨ (¬ p3583) ∨ (¬ p3367)) : (¬ p1976) ∨ (p2027) ∨ (p2765) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial26536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory15792 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6)
  exact rule26536 (meaning t m 1976) (meaning t m 2027) (meaning t m 2765) (meaning t m 3055) (meaning t m 3367) (meaning t m 3583) (meaning t m 3758) source

theorem rule26537 (p2000 p2027 p2542 p2589 p2633 p3644 p3742 : Prop) (h : (¬ p3644) ∨ (¬ p3742) ∨ p2027 ∨ p2633 ∨ (¬ p2000) ∨ (¬ p2589) ∨ (¬ p2542)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (p2633) ∨ (¬ p3644) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial26537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory15793 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule26537 (meaning t m 2000) (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 2633) (meaning t m 3644) (meaning t m 3742) source

theorem rule26538 (p2577 p3904 p4198 : Prop) (h : (¬ p4198) ∨ (¬ p3904) ∨ p2577) : (p2577) ∨ (¬ p3904) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial26538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2577) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory15794 (m.theta 0 4) (m.theta 0 5) (m.theta 0 6)
  exact rule26538 (meaning t m 2577) (meaning t m 3904) (meaning t m 4198) source

theorem rule26539 (p2027 p2088 p3178 p3877 p4118 p4790 : Prop) (h : (¬ p4790) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p3178) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3178) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3178)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15795 t (m.theta 0 3) (m.theta 0 8) (m.theta 2 3) (m.theta 3 8) (m.theta 8 9)
  exact rule26539 (meaning t m 2027) (meaning t m 2088) (meaning t m 3178) (meaning t m 3877) (meaning t m 4118) (meaning t m 4790) source

theorem rule26540 (p2027 p2459 p2881 p3857 p3961 p4986 : Prop) (h : (¬ p4986) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p2881) ∨ (¬ p3961) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4986) := by
  classical
  tauto

theorem initial26540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4986)) := by
  have source := ElevenTheory.theory15796 t (m.theta 0 7) (m.theta 0 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule26540 (meaning t m 2027) (meaning t m 2459) (meaning t m 2881) (meaning t m 3857) (meaning t m 3961) (meaning t m 4986) source

theorem rule26541 (p2027 p2192 p2946 p2963 p3745 p4960 : Prop) (h : (¬ p2192) ∨ (¬ p3745) ∨ (¬ p2946) ∨ (¬ p4960) ∨ (¬ p2963) ∨ p2027) : (p2027) ∨ (¬ p2192) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial26541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory15797 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule26541 (meaning t m 2027) (meaning t m 2192) (meaning t m 2946) (meaning t m 2963) (meaning t m 3745) (meaning t m 4960) source

theorem rule26543 (p1984 p2027 p2553 p3549 p3578 p3591 p3660 p3880 : Prop) (h : (¬ p1984) ∨ (¬ p3660) ∨ (¬ p3880) ∨ p3578 ∨ p2027 ∨ (¬ p3549) ∨ (¬ p2553) ∨ (¬ p3591)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p3549) ∨ (p3578) ∨ (¬ p3591) ∨ (¬ p3660) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial26543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3549)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory15799 t (m.theta 0 1) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7)
  exact rule26543 (meaning t m 1984) (meaning t m 2027) (meaning t m 2553) (meaning t m 3549) (meaning t m 3578) (meaning t m 3591) (meaning t m 3660) (meaning t m 3880) source

theorem rule26546 (p3369 p3904 p4108 : Prop) (h : (¬ p3904) ∨ (¬ p4108) ∨ p3369) : (p3369) ∨ (¬ p3904) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial26546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3369) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory15802 (m.theta 0 1) (m.theta 0 4) (m.theta 0 5)
  exact rule26546 (meaning t m 3369) (meaning t m 3904) (meaning t m 4108) source

theorem rule26549 (p2589 p3237 p3346 : Prop) (h : (¬ p3237) ∨ (¬ p2589) ∨ p3346) : (¬ p2589) ∨ (¬ p3237) ∨ (p3346) := by
  classical
  tauto

theorem initial26549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3237)) ∨ (meaning t m 3346) := by
  have source := ElevenTheory.theory15805 (m.theta 0 4) (m.theta 4 5) (m.theta 4 9)
  exact rule26549 (meaning t m 2589) (meaning t m 3237) (meaning t m 3346) source

theorem rule26555 (p2577 p2655 p3983 : Prop) (h : (¬ p2655) ∨ (¬ p2577) ∨ p3983) : (¬ p2577) ∨ (¬ p2655) ∨ (p3983) := by
  classical
  tauto

theorem initial26555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2655)) ∨ (meaning t m 3983) := by
  have source := ElevenTheory.theory15811 (m.theta 0 3) (m.theta 0 4) (m.theta 0 6)
  exact rule26555 (meaning t m 2577) (meaning t m 2655) (meaning t m 3983) source

theorem rule26560 (p1984 p2027 p2169 p3583 p3758 p3954 p3989 : Prop) (h : (¬ p3954) ∨ (¬ p1984) ∨ (¬ p3989) ∨ p2027 ∨ p2169 ∨ (¬ p3583) ∨ (¬ p3758)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p3583) ∨ (¬ p3758) ∨ (¬ p3954) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial26560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory15816 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8)
  exact rule26560 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 3583) (meaning t m 3758) (meaning t m 3954) (meaning t m 3989) source

theorem rule26564 (p2027 p2241 p2295 p2589 p2641 p3989 p4110 p4501 p5193 : Prop) (h : p2027 ∨ (¬ p2241) ∨ (¬ p4501) ∨ (¬ p2295) ∨ (¬ p5193) ∨ (¬ p2641) ∨ (¬ p2589) ∨ (¬ p4110) ∨ (¬ p3989)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2589) ∨ (¬ p2641) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4501) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial26564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory15820 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule26564 (meaning t m 2027) (meaning t m 2241) (meaning t m 2295) (meaning t m 2589) (meaning t m 2641) (meaning t m 3989) (meaning t m 4110) (meaning t m 4501) (meaning t m 5193) source

theorem rule26569 (p2027 p2295 p2331 p3822 p4790 p4841 : Prop) (h : (¬ p4841) ∨ (¬ p2295) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4790) ∨ (¬ p3822)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3822) ∨ (¬ p4790) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial26569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory15825 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule26569 (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 3822) (meaning t m 4790) (meaning t m 4841) source

theorem rule26570 (p2027 p2598 p2753 p2850 p3688 p4342 p4715 : Prop) (h : p2027 ∨ (¬ p2850) ∨ (¬ p4715) ∨ (¬ p2598) ∨ (¬ p4342) ∨ (¬ p3688) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial26570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory15826 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6)
  exact rule26570 (meaning t m 2027) (meaning t m 2598) (meaning t m 2753) (meaning t m 2850) (meaning t m 3688) (meaning t m 4342) (meaning t m 4715) source

theorem rule26575 (p2020 p2027 p2202 p2427 p3156 p3969 p4320 : Prop) (h : p2027 ∨ (¬ p4320) ∨ p2202 ∨ (¬ p2427) ∨ (¬ p2020) ∨ (¬ p3156) ∨ (¬ p3969)) : (¬ p2020) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p3156) ∨ (¬ p3969) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial26575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory15831 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 10)
  exact rule26575 (meaning t m 2020) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 3156) (meaning t m 3969) (meaning t m 4320) source

theorem rule26578 (p3368 p3402 p4202 : Prop) (h : (¬ p4202) ∨ (¬ p3402) ∨ p3368) : (p3368) ∨ (¬ p3402) ∨ (¬ p4202) := by
  classical
  tauto

theorem initial26578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3368) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4202)) := by
  have source := ElevenTheory.theory15834 (m.theta 1 3) (m.theta 1 4) (m.theta 1 5)
  exact rule26578 (meaning t m 3368) (meaning t m 3402) (meaning t m 4202) source

theorem rule26579 (p2027 p2363 p2668 p4037 p4604 : Prop) (h : (¬ p4604) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p2363) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p4037) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial26579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory15835 t (m.theta 3 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule26579 (meaning t m 2027) (meaning t m 2363) (meaning t m 2668) (meaning t m 4037) (meaning t m 4604) source

theorem rule26584 (p2027 p2341 p2922 p3193 p3575 p4636 p4666 : Prop) (h : (¬ p4636) ∨ (¬ p3575) ∨ (¬ p2341) ∨ (¬ p3193) ∨ (¬ p2922) ∨ (¬ p4666) ∨ p2027) : (p2027) ∨ (¬ p2341) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p3575) ∨ (¬ p4636) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial26584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4636)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory15840 t (m.theta 0 7) (m.theta 1 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 8) (m.theta 7 9)
  exact rule26584 (meaning t m 2027) (meaning t m 2341) (meaning t m 2922) (meaning t m 3193) (meaning t m 3575) (meaning t m 4636) (meaning t m 4666) source

theorem rule26585 (p2475 p4286 p5590 : Prop) (h : (¬ p4286) ∨ (¬ p2475) ∨ p5590) : (¬ p2475) ∨ (¬ p4286) ∨ (p5590) := by
  classical
  tauto

theorem initial26585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 4286)) ∨ (meaning t m 5590) := by
  have source := ElevenTheory.theory15841 (m.theta 0 8) (m.theta 4 8) (m.theta 8 10)
  exact rule26585 (meaning t m 2475) (meaning t m 4286) (meaning t m 5590) source

theorem rule26586 (p2027 p2406 p2427 p3556 p3904 p5191 : Prop) (h : p2027 ∨ (¬ p3556) ∨ (¬ p2427) ∨ (¬ p5191) ∨ (¬ p3904) ∨ (¬ p2406)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p5191) := by
  classical
  tauto

theorem initial26586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 5191)) := by
  have source := ElevenTheory.theory15842 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 5 7)
  exact rule26586 (meaning t m 2027) (meaning t m 2406) (meaning t m 2427) (meaning t m 3556) (meaning t m 3904) (meaning t m 5191) source

theorem rule26592 (p3546 p3551 p3631 p3657 : Prop) (h : (¬ p3546) ∨ (¬ p3631) ∨ (¬ p3551) ∨ (¬ p3657)) : (¬ p3546) ∨ (¬ p3551) ∨ (¬ p3631) ∨ (¬ p3657) := by
  classical
  tauto

theorem initial26592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3657)) := by
  have source := ElevenTheory.theory15848 (m.theta 0 7) (m.theta 1 7) (m.theta 7 8) (m.theta 7 9)
  exact rule26592 (meaning t m 3546) (meaning t m 3551) (meaning t m 3631) (meaning t m 3657) source

theorem rule26593 (p4321 p5332 p5387 : Prop) (h : (¬ p4321) ∨ (¬ p5332) ∨ p5387) : (¬ p4321) ∨ (¬ p5332) ∨ (p5387) := by
  classical
  tauto

theorem initial26593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5332)) ∨ (meaning t m 5387) := by
  have source := ElevenTheory.theory15849 (m.theta 1 9) (m.theta 2 9) (m.theta 9 10)
  exact rule26593 (meaning t m 4321) (meaning t m 5332) (meaning t m 5387) source

theorem rule26599 (p2027 p2187 p2387 p3051 p4198 p4558 : Prop) (h : p2027 ∨ (¬ p4198) ∨ (¬ p2187) ∨ (¬ p4558) ∨ (¬ p3051) ∨ (¬ p2387)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p3051) ∨ (¬ p4198) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial26599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory15855 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule26599 (meaning t m 2027) (meaning t m 2187) (meaning t m 2387) (meaning t m 3051) (meaning t m 4198) (meaning t m 4558) source

theorem rule26602 (p2027 p2252 p2750 p2963 p3399 p3954 p4037 p4075 p4191 p4826 : Prop) (h : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p4191) ∨ (¬ p2963) ∨ (¬ p4037) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p4826) ∨ (¬ p3954) ∨ (¬ p4075)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3399) ∨ (¬ p3954) ∨ (¬ p4037) ∨ (¬ p4075) ∨ (¬ p4191) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial26602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory15858 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule26602 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2963) (meaning t m 3399) (meaning t m 3954) (meaning t m 4037) (meaning t m 4075) (meaning t m 4191) (meaning t m 4826) source

theorem rule26603 (p2027 p3093 p3954 p4242 p4243 p4512 p4741 : Prop) (h : (¬ p3093) ∨ (¬ p4512) ∨ (¬ p3954) ∨ (¬ p4243) ∨ (¬ p4741) ∨ p2027 ∨ (¬ p4242)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4243) ∨ (¬ p4512) ∨ (¬ p4741) := by
  classical
  tauto

theorem initial26603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4741)) := by
  have source := ElevenTheory.theory15859 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 5) (m.theta 2 8)
  exact rule26603 (meaning t m 2027) (meaning t m 3093) (meaning t m 3954) (meaning t m 4242) (meaning t m 4243) (meaning t m 4512) (meaning t m 4741) source

theorem rule26605 (p2027 p2749 p2992 p3365 p4315 p4734 : Prop) (h : (¬ p3365) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p2749) ∨ (¬ p4734)) : (p2027) ∨ (¬ p2749) ∨ (¬ p2992) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial26605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory15861 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5)
  exact rule26605 (meaning t m 2027) (meaning t m 2749) (meaning t m 2992) (meaning t m 3365) (meaning t m 4315) (meaning t m 4734) source

theorem rule26606 (p1977 p2027 p2241 p2553 p3008 p3549 p3591 : Prop) (h : p3008 ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p1977)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial26606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory15862 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7)
  exact rule26606 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2553) (meaning t m 3008) (meaning t m 3549) (meaning t m 3591) source

theorem rule26607 (p1988 p2027 p2622 p2761 p2901 p3136 p3246 : Prop) (h : (¬ p1988) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2901) ∨ p2622 ∨ (¬ p2761) ∨ (¬ p3136)) : (¬ p1988) ∨ (p2027) ∨ (p2622) ∨ (¬ p2761) ∨ (¬ p2901) ∨ (¬ p3136) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial26607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory15863 t (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule26607 (meaning t m 1988) (meaning t m 2027) (meaning t m 2622) (meaning t m 2761) (meaning t m 2901) (meaning t m 3136) (meaning t m 3246) source

theorem rule26610 (p2027 p2577 p2659 p3016 p3564 p3946 : Prop) (h : (¬ p3946) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p2577) ∨ (¬ p2659)) : (p2027) ∨ (¬ p2577) ∨ (¬ p2659) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial26610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory15866 t (m.theta 0 4) (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9)
  exact rule26610 (meaning t m 2027) (meaning t m 2577) (meaning t m 2659) (meaning t m 3016) (meaning t m 3564) (meaning t m 3946) source

theorem rule26615 (p1991 p2027 p2459 p2534 p2633 p2657 p3742 p4186 : Prop) (h : (¬ p3742) ∨ (¬ p1991) ∨ (¬ p4186) ∨ p2633 ∨ (¬ p2657) ∨ (¬ p2534) ∨ (¬ p2459) ∨ p2027) : (¬ p1991) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p2657) ∨ (¬ p3742) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial26615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory15871 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26615 (meaning t m 1991) (meaning t m 2027) (meaning t m 2459) (meaning t m 2534) (meaning t m 2633) (meaning t m 2657) (meaning t m 3742) (meaning t m 4186) source

theorem rule26629 (p1990 p2027 p2202 p2352 p2493 p3097 p3238 p3955 : Prop) (h : (¬ p3955) ∨ (¬ p1990) ∨ (¬ p2493) ∨ (¬ p3238) ∨ p2202 ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2352)) : (¬ p1990) ∨ (p2027) ∨ (p2202) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3097) ∨ (¬ p3238) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial26629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory15885 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule26629 (meaning t m 1990) (meaning t m 2027) (meaning t m 2202) (meaning t m 2352) (meaning t m 2493) (meaning t m 3097) (meaning t m 3238) (meaning t m 3955) source

theorem rule26630 (p3097 p3325 p3989 : Prop) (h : (¬ p3325) ∨ (¬ p3989) ∨ p3097) : (p3097) ∨ (¬ p3325) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial26630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3097) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory15886 (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule26630 (meaning t m 3097) (meaning t m 3325) (meaning t m 3989) source

theorem rule26631 (p1976 p2027 p2387 p2764 p2778 p2819 p3917 p4191 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p2778) ∨ (¬ p2387) ∨ (¬ p2819) ∨ p2764 ∨ (¬ p3917) ∨ (¬ p4191)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2387) ∨ (p2764) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p3917) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial26631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory15887 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 6) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule26631 (meaning t m 1976) (meaning t m 2027) (meaning t m 2387) (meaning t m 2764) (meaning t m 2778) (meaning t m 2819) (meaning t m 3917) (meaning t m 4191) source

theorem rule26634 (p2027 p2396 p2761 p4321 p5142 p5357 : Prop) (h : (¬ p5142) ∨ (¬ p4321) ∨ (¬ p2761) ∨ (¬ p2396) ∨ (¬ p5357) ∨ p2027) : (p2027) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p4321) ∨ (¬ p5142) ∨ (¬ p5357) := by
  classical
  tauto

theorem initial26634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5142)) ∨ (¬ (meaning t m 5357)) := by
  have source := ElevenTheory.theory15890 t (m.theta 1 7) (m.theta 1 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule26634 (meaning t m 2027) (meaning t m 2396) (meaning t m 2761) (meaning t m 4321) (meaning t m 5142) (meaning t m 5357) source

theorem rule26637 (p2027 p3097 p3156 p3952 p4405 p4441 : Prop) (h : (¬ p3952) ∨ (¬ p4405) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p3156) ∨ (¬ p4441)) : (p2027) ∨ (¬ p3097) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p4405) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial26637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory15893 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule26637 (meaning t m 2027) (meaning t m 3097) (meaning t m 3156) (meaning t m 3952) (meaning t m 4405) (meaning t m 4441) source

theorem rule26639 (p1997 p2027 p2156 p2191 p2766 p3370 p3692 p4110 : Prop) (h : (¬ p3370) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p2191) ∨ p2766 ∨ (¬ p2156) ∨ (¬ p1997) ∨ (¬ p4110)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2191) ∨ (p2766) ∨ (¬ p3370) ∨ (¬ p3692) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial26639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory15895 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule26639 (meaning t m 1997) (meaning t m 2027) (meaning t m 2156) (meaning t m 2191) (meaning t m 2766) (meaning t m 3370) (meaning t m 3692) (meaning t m 4110) source

theorem rule26642 (p1987 p2027 p2992 p2997 p3097 p3745 p4154 p4315 : Prop) (h : (¬ p3745) ∨ (¬ p1987) ∨ (¬ p4315) ∨ p2027 ∨ p2997 ∨ (¬ p3097) ∨ (¬ p2992) ∨ (¬ p4154)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2992) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3745) ∨ (¬ p4154) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial26642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2992)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory15898 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule26642 (meaning t m 1987) (meaning t m 2027) (meaning t m 2992) (meaning t m 2997) (meaning t m 3097) (meaning t m 3745) (meaning t m 4154) (meaning t m 4315) source

theorem rule26643 (p2027 p2911 p3146 p4278 p4660 p4905 p5107 : Prop) (h : (¬ p4660) ∨ p2027 ∨ (¬ p5107) ∨ (¬ p3146) ∨ (¬ p4278) ∨ (¬ p2911) ∨ (¬ p4905)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3146) ∨ (¬ p4278) ∨ (¬ p4660) ∨ (¬ p4905) ∨ (¬ p5107) := by
  classical
  tauto

theorem initial26643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4660)) ∨ (¬ (meaning t m 4905)) ∨ (¬ (meaning t m 5107)) := by
  have source := ElevenTheory.theory15899 t (m.theta 3 9) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule26643 (meaning t m 2027) (meaning t m 2911) (meaning t m 3146) (meaning t m 4278) (meaning t m 4660) (meaning t m 4905) (meaning t m 5107) source

theorem rule26644 (p2027 p2245 p2352 p2598 p3146 p3172 p3422 p4118 p4134 p4733 : Prop) (h : (¬ p2245) ∨ (¬ p4134) ∨ (¬ p3422) ∨ (¬ p2598) ∨ (¬ p4733) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p4118) ∨ (¬ p3172)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p3146) ∨ (¬ p3172) ∨ (¬ p3422) ∨ (¬ p4118) ∨ (¬ p4134) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial26644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory15900 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule26644 (meaning t m 2027) (meaning t m 2245) (meaning t m 2352) (meaning t m 2598) (meaning t m 3146) (meaning t m 3172) (meaning t m 3422) (meaning t m 4118) (meaning t m 4134) (meaning t m 4733) source

theorem rule26647 (p2299 p3659 p4471 : Prop) (h : (¬ p2299) ∨ (¬ p4471) ∨ p3659) : (¬ p2299) ∨ (p3659) ∨ (¬ p4471) := by
  classical
  tauto

theorem initial26647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2299)) ∨ (meaning t m 3659) ∨ (¬ (meaning t m 4471)) := by
  have source := ElevenTheory.theory15903 (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule26647 (meaning t m 2299) (meaning t m 3659) (meaning t m 4471) source

theorem rule26653 (p3232 p4264 p4374 : Prop) (h : (¬ p4374) ∨ (¬ p3232) ∨ p4264) : (¬ p3232) ∨ (p4264) ∨ (¬ p4374) := by
  classical
  tauto

theorem initial26653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3232)) ∨ (meaning t m 4264) ∨ (¬ (meaning t m 4374)) := by
  have source := ElevenTheory.theory15909 (m.theta 0 9) (m.theta 1 9) (m.theta 4 9)
  exact rule26653 (meaning t m 3232) (meaning t m 4264) (meaning t m 4374) source

theorem rule26654 (p2001 p2027 p2220 p2766 p3646 p3989 p4347 : Prop) (h : p2027 ∨ p2766 ∨ (¬ p2220) ∨ (¬ p2001) ∨ (¬ p4347) ∨ (¬ p3646) ∨ (¬ p3989)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2220) ∨ (p2766) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial26654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory15910 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule26654 (meaning t m 2001) (meaning t m 2027) (meaning t m 2220) (meaning t m 2766) (meaning t m 3646) (meaning t m 3989) (meaning t m 4347) source

theorem rule26656 (p1994 p2997 p3742 p4276 : Prop) (h : p2997 ∨ (¬ p3742) ∨ (¬ p1994) ∨ p4276) : (¬ p1994) ∨ (p2997) ∨ (¬ p3742) ∨ (p4276) := by
  classical
  tauto

theorem initial26656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3742)) ∨ (meaning t m 4276) := by
  have source := ElevenTheory.theory15912 t (m.theta 3 4) (m.theta 4 7) (m.theta 6 7)
  exact rule26656 (meaning t m 1994) (meaning t m 2997) (meaning t m 3742) (meaning t m 4276) source

theorem rule26657 (p2027 p2210 p2563 p3860 p3906 p4210 p4507 : Prop) (h : (¬ p2563) ∨ (¬ p4210) ∨ (¬ p2210) ∨ (¬ p4507) ∨ (¬ p3906) ∨ p2027 ∨ (¬ p3860)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2563) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p4210) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial26657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3906)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory15913 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule26657 (meaning t m 2027) (meaning t m 2210) (meaning t m 2563) (meaning t m 3860) (meaning t m 3906) (meaning t m 4210) (meaning t m 4507) source

theorem rule26659 (p1998 p2027 p2247 p2688 p2881 p2922 p3379 p3569 : Prop) (h : p2688 ∨ (¬ p2881) ∨ (¬ p2247) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p3569) ∨ (¬ p3379)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p2881) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3569) := by
  classical
  tauto

theorem initial26659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3569)) := by
  have source := ElevenTheory.theory15915 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule26659 (meaning t m 1998) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 2881) (meaning t m 2922) (meaning t m 3379) (meaning t m 3569) source

theorem rule26661 (p2027 p2470 p2663 p2810 p4256 p4790 : Prop) (h : (¬ p4256) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p4790) ∨ (¬ p2810) ∨ (¬ p2663)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p4256) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15917 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8)
  exact rule26661 (meaning t m 2027) (meaning t m 2470) (meaning t m 2663) (meaning t m 2810) (meaning t m 4256) (meaning t m 4790) source

theorem rule26662 (p2027 p2248 p2946 p3146 p3156 p3548 p3591 p4105 p5118 p5558 : Prop) (h : p2027 ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p5558) ∨ (¬ p3591) ∨ (¬ p3548) ∨ (¬ p2248) ∨ (¬ p4105) ∨ (¬ p5118)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3548) ∨ (¬ p3591) ∨ (¬ p4105) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial26662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory15918 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 1 7) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule26662 (meaning t m 2027) (meaning t m 2248) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3548) (meaning t m 3591) (meaning t m 4105) (meaning t m 5118) (meaning t m 5558) source

theorem rule26663 (p2027 p3516 p3572 p3947 p4104 p4790 : Prop) (h : (¬ p4104) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4790) ∨ (¬ p3572) ∨ p2027) : (p2027) ∨ (¬ p3516) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4104) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15919 t (m.theta 0 3) (m.theta 0 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 9)
  exact rule26663 (meaning t m 2027) (meaning t m 3516) (meaning t m 3572) (meaning t m 3947) (meaning t m 4104) (meaning t m 4790) source

theorem rule26664 (p2641 p2742 p2797 : Prop) (h : (¬ p2742) ∨ (¬ p2641) ∨ p2797) : (¬ p2641) ∨ (¬ p2742) ∨ (p2797) := by
  classical
  tauto

theorem initial26664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2742)) ∨ (meaning t m 2797) := by
  have source := ElevenTheory.theory15920 (m.theta 1 3) (m.theta 2 3) (m.theta 3 6)
  exact rule26664 (meaning t m 2641) (meaning t m 2742) (meaning t m 2797) source

theorem rule26665 (p2027 p2284 p2553 p2696 p2742 p2992 p3585 p3822 p4718 p4737 p5220 : Prop) (h : (¬ p3822) ∨ p2027 ∨ (¬ p5220) ∨ (¬ p2553) ∨ (¬ p2992) ∨ (¬ p4737) ∨ (¬ p3585) ∨ (¬ p2696) ∨ (¬ p4718) ∨ (¬ p2284) ∨ (¬ p2742)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2553) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2992) ∨ (¬ p3585) ∨ (¬ p3822) ∨ (¬ p4718) ∨ (¬ p4737) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial26665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4718)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory15921 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule26665 (meaning t m 2027) (meaning t m 2284) (meaning t m 2553) (meaning t m 2696) (meaning t m 2742) (meaning t m 2992) (meaning t m 3585) (meaning t m 3822) (meaning t m 4718) (meaning t m 4737) (meaning t m 5220) source

theorem rule26666 (p2696 p2742 p3589 p3591 p4759 : Prop) (h : (¬ p2696) ∨ (¬ p4759) ∨ (¬ p3589) ∨ (¬ p2742) ∨ (¬ p3591)) : (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3589) ∨ (¬ p3591) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial26666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory15922 (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3)
  exact rule26666 (meaning t m 2696) (meaning t m 2742) (meaning t m 3589) (meaning t m 3591) (meaning t m 4759) source

theorem rule26667 (p2010 p2027 p2437 p2459 p2481 p2633 p3857 p4256 : Prop) (h : (¬ p2437) ∨ (¬ p2459) ∨ (¬ p2010) ∨ (¬ p4256) ∨ p2027 ∨ p2633 ∨ (¬ p2481) ∨ (¬ p3857)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2437) ∨ (¬ p2459) ∨ (¬ p2481) ∨ (p2633) ∨ (¬ p3857) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial26667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2481)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory15923 t (m.theta 0 8) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26667 (meaning t m 2010) (meaning t m 2027) (meaning t m 2437) (meaning t m 2459) (meaning t m 2481) (meaning t m 2633) (meaning t m 3857) (meaning t m 4256) source

theorem rule26669 (p2027 p2284 p2590 p2819 p3956 p4428 p4705 : Prop) (h : (¬ p4428) ∨ (¬ p4705) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2590) ∨ (¬ p2284) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2590) ∨ (¬ p2819) ∨ (¬ p3956) ∨ (¬ p4428) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial26669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory15925 t (m.theta 2 6) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule26669 (meaning t m 2027) (meaning t m 2284) (meaning t m 2590) (meaning t m 2819) (meaning t m 3956) (meaning t m 4428) (meaning t m 4705) source

theorem rule26670 (p2000 p2027 p2274 p2542 p2589 p2765 p3742 p3921 : Prop) (h : (¬ p3742) ∨ (¬ p2000) ∨ p2027 ∨ (¬ p2589) ∨ p2765 ∨ (¬ p2542) ∨ (¬ p2274) ∨ (¬ p3921)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (p2765) ∨ (¬ p3742) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial26670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory15926 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7)
  exact rule26670 (meaning t m 2000) (meaning t m 2027) (meaning t m 2274) (meaning t m 2542) (meaning t m 2589) (meaning t m 2765) (meaning t m 3742) (meaning t m 3921) source

theorem rule26675 (p2027 p2230 p2563 p3540 p4001 p4555 : Prop) (h : (¬ p4555) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3540) ∨ (¬ p4001)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3540) ∨ (¬ p4001) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial26675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory15931 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule26675 (meaning t m 2027) (meaning t m 2230) (meaning t m 2563) (meaning t m 3540) (meaning t m 4001) (meaning t m 4555) source

theorem rule26676 (p4032 p4109 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p4109) ∨ p4032) : (p4032) ∨ (¬ p4109) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial26676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4032) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory15932 (m.theta 0 5) (m.theta 4 5) (m.theta 5 9)
  exact rule26676 (meaning t m 4032) (meaning t m 4109) (meaning t m 4948) source

theorem rule26679 (p1991 p2027 p2440 p2657 p2764 p4322 p4948 : Prop) (h : (¬ p1991) ∨ p2764 ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p4322) ∨ (¬ p4948)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (p2764) ∨ (¬ p4322) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial26679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory15935 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule26679 (meaning t m 1991) (meaning t m 2027) (meaning t m 2440) (meaning t m 2657) (meaning t m 2764) (meaning t m 4322) (meaning t m 4948) source

theorem rule26682 (p2027 p2177 p2295 p2331 p2957 p3146 p3697 p3857 p4315 p4790 p4905 : Prop) (h : (¬ p4315) ∨ (¬ p2957) ∨ (¬ p3146) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4790) ∨ (¬ p4905) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2177) ∨ (¬ p2295)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2957) ∨ (¬ p3146) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4315) ∨ (¬ p4790) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial26682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3697)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory15938 t (m.theta 0 3) (m.theta 0 5) (m.theta 0 8) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule26682 (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 2331) (meaning t m 2957) (meaning t m 3146) (meaning t m 3697) (meaning t m 3857) (meaning t m 4315) (meaning t m 4790) (meaning t m 4905) source

theorem rule26683 (p2027 p2449 p2807 p4324 p4357 p4790 : Prop) (h : p2027 ∨ (¬ p4324) ∨ (¬ p2807) ∨ (¬ p4790) ∨ (¬ p2449) ∨ (¬ p4357)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p4324) ∨ (¬ p4357) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4357)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15939 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 9)
  exact rule26683 (meaning t m 2027) (meaning t m 2449) (meaning t m 2807) (meaning t m 4324) (meaning t m 4357) (meaning t m 4790) source

theorem rule26685 (p2579 p3540 p3581 : Prop) (h : (¬ p2579) ∨ (¬ p3581) ∨ p3540) : (¬ p2579) ∨ (p3540) ∨ (¬ p3581) := by
  classical
  tauto

theorem initial26685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2579)) ∨ (meaning t m 3540) ∨ (¬ (meaning t m 3581)) := by
  have source := ElevenTheory.theory15941 (m.theta 0 4) (m.theta 4 6) (m.theta 4 7)
  exact rule26685 (meaning t m 2579) (meaning t m 3540) (meaning t m 3581) source

theorem rule26686 (p2027 p2493 p2579 p2655 p2946 p4116 p4704 : Prop) (h : (¬ p2655) ∨ (¬ p2579) ∨ (¬ p2946) ∨ (¬ p4116) ∨ (¬ p2493) ∨ (¬ p4704) ∨ p2027) : (p2027) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2946) ∨ (¬ p4116) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial26686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory15942 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule26686 (meaning t m 2027) (meaning t m 2493) (meaning t m 2579) (meaning t m 2655) (meaning t m 2946) (meaning t m 4116) (meaning t m 4704) source

theorem rule26689 (p2027 p2331 p2363 p2819 p2957 p4120 p4315 p4337 p4790 p5118 p5568 : Prop) (h : (¬ p4120) ∨ (¬ p2331) ∨ (¬ p2819) ∨ (¬ p5118) ∨ p2027 ∨ (¬ p5568) ∨ (¬ p2957) ∨ (¬ p4315) ∨ (¬ p4790) ∨ (¬ p2363) ∨ (¬ p4337)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2819) ∨ (¬ p2957) ∨ (¬ p4120) ∨ (¬ p4315) ∨ (¬ p4337) ∨ (¬ p4790) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial26689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory15945 t (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule26689 (meaning t m 2027) (meaning t m 2331) (meaning t m 2363) (meaning t m 2819) (meaning t m 2957) (meaning t m 4120) (meaning t m 4315) (meaning t m 4337) (meaning t m 4790) (meaning t m 5118) (meaning t m 5568) source

theorem rule26691 (p2027 p2663 p2810 p3355 p3359 p4790 : Prop) (h : (¬ p3355) ∨ (¬ p2663) ∨ (¬ p3359) ∨ (¬ p4790) ∨ (¬ p2810) ∨ p2027) : (p2027) ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p3355) ∨ (¬ p3359) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15947 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9)
  exact rule26691 (meaning t m 2027) (meaning t m 2663) (meaning t m 2810) (meaning t m 3355) (meaning t m 3359) (meaning t m 4790) source

theorem rule26694 (p1982 p2027 p2331 p2363 p2633 p2668 p3246 p3570 p3947 p4315 p4386 p4790 : Prop) (h : (¬ p1982) ∨ (¬ p4790) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3570) ∨ (¬ p4386) ∨ (¬ p2331) ∨ (¬ p3947) ∨ p2633 ∨ (¬ p4315)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (p2633) ∨ (¬ p2668) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3947) ∨ (¬ p4315) ∨ (¬ p4386) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26694 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory15950 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 3 7) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule26694 (meaning t m 1982) (meaning t m 2027) (meaning t m 2331) (meaning t m 2363) (meaning t m 2633) (meaning t m 2668) (meaning t m 3246) (meaning t m 3570) (meaning t m 3947) (meaning t m 4315) (meaning t m 4386) (meaning t m 4790) source

theorem rule26696 (p1998 p2027 p2264 p2842 p3201 p3516 p3575 p3947 : Prop) (h : (¬ p3575) ∨ p2842 ∨ (¬ p1998) ∨ (¬ p2264) ∨ (¬ p3516) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p3201)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2842) ∨ (¬ p3201) ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial26696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory15952 t (m.theta 0 7) (m.theta 2 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule26696 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2842) (meaning t m 3201) (meaning t m 3516) (meaning t m 3575) (meaning t m 3947) source

theorem rule26699 (p1998 p2027 p2323 p2449 p2651 p2911 p3580 p4278 : Prop) (h : (¬ p3580) ∨ (¬ p4278) ∨ (¬ p2449) ∨ p2027 ∨ p2323 ∨ (¬ p1998) ∨ (¬ p2651) ∨ (¬ p2911)) : (¬ p1998) ∨ (p2027) ∨ (p2323) ∨ (¬ p2449) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3580) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial26699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory15955 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule26699 (meaning t m 1998) (meaning t m 2027) (meaning t m 2323) (meaning t m 2449) (meaning t m 2651) (meaning t m 2911) (meaning t m 3580) (meaning t m 4278) source

theorem rule26701 (p1994 p2027 p2166 p2440 p2765 p3880 p4173 : Prop) (h : (¬ p2166) ∨ p2765 ∨ (¬ p4173) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p3880) ∨ (¬ p2440)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2440) ∨ (p2765) ∨ (¬ p3880) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial26701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory15957 t (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule26701 (meaning t m 1994) (meaning t m 2027) (meaning t m 2166) (meaning t m 2440) (meaning t m 2765) (meaning t m 3880) (meaning t m 4173) source

theorem rule26702 (p2027 p2220 p2579 p3880 p4399 p4715 : Prop) (h : (¬ p3880) ∨ p2027 ∨ (¬ p4399) ∨ (¬ p4715) ∨ (¬ p2579) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2579) ∨ (¬ p3880) ∨ (¬ p4399) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial26702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory15958 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8)
  exact rule26702 (meaning t m 2027) (meaning t m 2220) (meaning t m 2579) (meaning t m 3880) (meaning t m 4399) (meaning t m 4715) source

theorem rule26708 (p2662 p3343 p3346 : Prop) (h : (¬ p3346) ∨ (¬ p2662) ∨ (¬ p3343)) : (¬ p2662) ∨ (¬ p3343) ∨ (¬ p3346) := by
  classical
  tauto

theorem initial26708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3346)) := by
  have source := ElevenTheory.theory15964 (m.theta 0 4) (m.theta 3 4) (m.theta 4 9)
  exact rule26708 (meaning t m 2662) (meaning t m 3343) (meaning t m 3346) source

theorem rule26709 (p2662 p3346 p3359 : Prop) (h : (¬ p3346) ∨ (¬ p2662) ∨ p3359) : (¬ p2662) ∨ (¬ p3346) ∨ (p3359) := by
  classical
  tauto

theorem initial26709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3346)) ∨ (meaning t m 3359) := by
  have source := ElevenTheory.theory15965 (m.theta 0 4) (m.theta 3 4) (m.theta 4 9)
  exact rule26709 (meaning t m 2662) (meaning t m 3346) (meaning t m 3359) source

theorem rule26710 (p2027 p2901 p2950 p3136 p3556 p4787 : Prop) (h : (¬ p2901) ∨ (¬ p2950) ∨ (¬ p4787) ∨ (¬ p3556) ∨ (¬ p3136) ∨ p2027) : (p2027) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3136) ∨ (¬ p3556) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial26710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory15966 t (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7)
  exact rule26710 (meaning t m 2027) (meaning t m 2901) (meaning t m 2950) (meaning t m 3136) (meaning t m 3556) (meaning t m 4787) source

theorem rule26718 (p4034 p4702 p4960 : Prop) (h : (¬ p4034) ∨ (¬ p4702) ∨ p4960) : (¬ p4034) ∨ (¬ p4702) ∨ (p4960) := by
  classical
  tauto

theorem initial26718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4702)) ∨ (meaning t m 4960) := by
  have source := ElevenTheory.theory15974 t (m.theta 1 5) (m.theta 3 5) (m.theta 4 5)
  exact rule26718 (meaning t m 4034) (meaning t m 4702) (meaning t m 4960) source

theorem rule26720 (p3660 p4646 p4711 : Prop) (h : (¬ p4646) ∨ (¬ p3660) ∨ p4711) : (¬ p3660) ∨ (¬ p4646) ∨ (p4711) := by
  classical
  tauto

theorem initial26720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 4646)) ∨ (meaning t m 4711) := by
  have source := ElevenTheory.theory15976 t (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule26720 (meaning t m 3660) (meaning t m 4646) (meaning t m 4711) source

theorem rule26721 (p1987 p2027 p2202 p2437 p2440 p2696 p3540 p3905 : Prop) (h : (¬ p3540) ∨ (¬ p2437) ∨ (¬ p3905) ∨ (¬ p1987) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p2440) ∨ p2202) : (¬ p1987) ∨ (p2027) ∨ (p2202) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2696) ∨ (¬ p3540) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial26721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory15977 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule26721 (meaning t m 1987) (meaning t m 2027) (meaning t m 2202) (meaning t m 2437) (meaning t m 2440) (meaning t m 2696) (meaning t m 3540) (meaning t m 3905) source

theorem rule26730 (p1990 p2027 p2307 p2344 p2668 p3568 p3989 : Prop) (h : p2344 ∨ (¬ p3989) ∨ (¬ p2668) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p2307)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2307) ∨ (p2344) ∨ (¬ p2668) ∨ (¬ p3568) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial26730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory15986 t (m.theta 0 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule26730 (meaning t m 1990) (meaning t m 2027) (meaning t m 2307) (meaning t m 2344) (meaning t m 2668) (meaning t m 3568) (meaning t m 3989) source

theorem rule26731 (p3136 p4195 p4336 : Prop) (h : (¬ p4336) ∨ (¬ p3136) ∨ (¬ p4195)) : (¬ p3136) ∨ (¬ p4195) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial26731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory15987 (m.theta 2 3) (m.theta 3 5) (m.theta 3 6)
  exact rule26731 (meaning t m 3136) (meaning t m 4195) (meaning t m 4336) source

theorem rule26735 (p2027 p2573 p2911 p3551 p3741 p4717 p5197 : Prop) (h : (¬ p2911) ∨ (¬ p3741) ∨ (¬ p4717) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p5197) ∨ (¬ p2573)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4717) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial26735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4717)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory15991 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule26735 (meaning t m 2027) (meaning t m 2573) (meaning t m 2911) (meaning t m 3551) (meaning t m 3741) (meaning t m 4717) (meaning t m 5197) source

theorem rule26736 (p2007 p2027 p2202 p2437 p2440 p2518 p3347 p3540 : Prop) (h : (¬ p2440) ∨ p2027 ∨ p2202 ∨ (¬ p2007) ∨ (¬ p3540) ∨ (¬ p3347) ∨ (¬ p2437) ∨ (¬ p2518)) : (¬ p2007) ∨ (p2027) ∨ (p2202) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2518) ∨ (¬ p3347) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial26736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory15992 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8)
  exact rule26736 (meaning t m 2007) (meaning t m 2027) (meaning t m 2202) (meaning t m 2437) (meaning t m 2440) (meaning t m 2518) (meaning t m 3347) (meaning t m 3540) source

theorem rule26738 (p1975 p2027 p2202 p2299 p2437 p2440 p2911 : Prop) (h : (¬ p2440) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p1975) ∨ (¬ p2299) ∨ p2202 ∨ (¬ p2911)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2299) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2911) := by
  classical
  tauto

theorem initial26738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2911)) := by
  have source := ElevenTheory.theory15994 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule26738 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2299) (meaning t m 2437) (meaning t m 2440) (meaning t m 2911) source

theorem rule26740 (p4138 p4832 p4995 : Prop) (h : (¬ p4832) ∨ (¬ p4138) ∨ p4995) : (¬ p4138) ∨ (¬ p4832) ∨ (p4995) := by
  classical
  tauto

theorem initial26740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4832)) ∨ (meaning t m 4995) := by
  have source := ElevenTheory.theory15996 t (m.theta 1 8) (m.theta 6 8) (m.theta 7 8)
  exact rule26740 (meaning t m 4138) (meaning t m 4832) (meaning t m 4995) source

theorem rule26741 (p1987 p2027 p2202 p2440 p2476 p2737 p3083 p3347 p4257 : Prop) (h : p2027 ∨ (¬ p2476) ∨ (¬ p3083) ∨ p2202 ∨ (¬ p1987) ∨ (¬ p2737) ∨ (¬ p2440) ∨ (¬ p3347) ∨ (¬ p4257)) : (¬ p1987) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2737) ∨ (¬ p3083) ∨ (¬ p3347) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial26741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory15997 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule26741 (meaning t m 1987) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2476) (meaning t m 2737) (meaning t m 3083) (meaning t m 3347) (meaning t m 4257) source

theorem rule26744 (p2476 p3346 p4045 : Prop) (h : (¬ p4045) ∨ (¬ p2476) ∨ p3346) : (¬ p2476) ∨ (p3346) ∨ (¬ p4045) := by
  classical
  tauto

theorem initial26744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2476)) ∨ (meaning t m 3346) ∨ (¬ (meaning t m 4045)) := by
  have source := ElevenTheory.theory16000 (m.theta 0 4) (m.theta 4 8) (m.theta 4 9)
  exact rule26744 (meaning t m 2476) (meaning t m 3346) (meaning t m 4045) source

theorem rule26748 (p2027 p2138 p2598 p3201 p3698 p4646 : Prop) (h : (¬ p3698) ∨ (¬ p2598) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p4646) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3698) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial26748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory16004 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7)
  exact rule26748 (meaning t m 2027) (meaning t m 2138) (meaning t m 2598) (meaning t m 3201) (meaning t m 3698) (meaning t m 4646) source

theorem rule26751 (p2027 p2528 p2881 p3821 p4283 p4438 p4445 : Prop) (h : (¬ p2528) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p4283) ∨ (¬ p4445) ∨ (¬ p4438)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2881) ∨ (¬ p3821) ∨ (¬ p4283) ∨ (¬ p4438) ∨ (¬ p4445) := by
  classical
  tauto

theorem initial26751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4445)) := by
  have source := ElevenTheory.theory16007 t (m.theta 0 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule26751 (meaning t m 2027) (meaning t m 2528) (meaning t m 2881) (meaning t m 3821) (meaning t m 4283) (meaning t m 4438) (meaning t m 4445) source

theorem rule26752 (p2138 p3555 p3873 p4243 : Prop) (h : (¬ p3873) ∨ (¬ p2138) ∨ (¬ p4243) ∨ p3555) : (¬ p2138) ∨ (p3555) ∨ (¬ p3873) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial26752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (meaning t m 3555) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory16008 (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 5)
  exact rule26752 (meaning t m 2138) (meaning t m 3555) (meaning t m 3873) (meaning t m 4243) source

theorem rule26754 (p2027 p2230 p2440 p2663 p2810 p4790 : Prop) (h : (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p4790) ∨ p2027 ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26754 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory16010 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5)
  exact rule26754 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2663) (meaning t m 2810) (meaning t m 4790) source

theorem rule26755 (p2027 p2246 p2651 p2749 p2881 p3016 p3546 p3551 p3564 p3690 p4330 p4445 p4796 : Prop) (h : (¬ p2651) ∨ (¬ p2749) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p3016) ∨ (¬ p2881) ∨ (¬ p3564) ∨ (¬ p3546) ∨ (¬ p4796) ∨ (¬ p3551) ∨ (¬ p4445) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p2881) ∨ (¬ p3016) ∨ (¬ p3546) ∨ (¬ p3551) ∨ (¬ p3564) ∨ (¬ p3690) ∨ (¬ p4330) ∨ (¬ p4445) ∨ (¬ p4796) := by
  classical
  tauto

theorem initial26755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 4796)) := by
  have source := ElevenTheory.theory16011 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule26755 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2749) (meaning t m 2881) (meaning t m 3016) (meaning t m 3546) (meaning t m 3551) (meaning t m 3564) (meaning t m 3690) (meaning t m 4330) (meaning t m 4445) (meaning t m 4796) source

theorem rule26756 (p2027 p3146 p3657 p3767 p4381 p4456 p4905 : Prop) (h : (¬ p4456) ∨ (¬ p3146) ∨ (¬ p3767) ∨ (¬ p3657) ∨ p2027 ∨ (¬ p4905) ∨ (¬ p4381)) : (p2027) ∨ (¬ p3146) ∨ (¬ p3657) ∨ (¬ p3767) ∨ (¬ p4381) ∨ (¬ p4456) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial26756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4456)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory16012 t (m.theta 0 9) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26756 (meaning t m 2027) (meaning t m 3146) (meaning t m 3657) (meaning t m 3767) (meaning t m 4381) (meaning t m 4456) (meaning t m 4905) source

theorem rule26760 (p1997 p2027 p2542 p3128 p3461 p3742 p4425 p4635 : Prop) (h : p3128 ∨ (¬ p2542) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p1997) ∨ (¬ p4425) ∨ (¬ p4635) ∨ (¬ p3742)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (p3128) ∨ (¬ p3461) ∨ (¬ p3742) ∨ (¬ p4425) ∨ (¬ p4635) := by
  classical
  tauto

theorem initial26760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4635)) := by
  have source := ElevenTheory.theory16016 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule26760 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 3128) (meaning t m 3461) (meaning t m 3742) (meaning t m 4425) (meaning t m 4635) source

theorem rule26765 (p2027 p2598 p2608 p2753 p2761 p3946 p4166 p4191 p4638 p5021 p5126 : Prop) (h : p2027 ∨ (¬ p4166) ∨ (¬ p2598) ∨ (¬ p2608) ∨ (¬ p4191) ∨ (¬ p5126) ∨ (¬ p2761) ∨ (¬ p4638) ∨ (¬ p5021) ∨ (¬ p3946) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2608) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3946) ∨ (¬ p4166) ∨ (¬ p4191) ∨ (¬ p4638) ∨ (¬ p5021) ∨ (¬ p5126) := by
  classical
  tauto

theorem initial26765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4166)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 5021)) ∨ (¬ (meaning t m 5126)) := by
  have source := ElevenTheory.theory16021 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 4 10) (m.theta 4 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule26765 (meaning t m 2027) (meaning t m 2598) (meaning t m 2608) (meaning t m 2753) (meaning t m 2761) (meaning t m 3946) (meaning t m 4166) (meaning t m 4191) (meaning t m 4638) (meaning t m 5021) (meaning t m 5126) source

theorem rule26766 (p2246 p3286 p3842 : Prop) (h : (¬ p2246) ∨ (¬ p3286) ∨ p3842) : (¬ p2246) ∨ (¬ p3286) ∨ (p3842) := by
  classical
  tauto

theorem initial26766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 3286)) ∨ (meaning t m 3842) := by
  have source := ElevenTheory.theory16022 (m.theta 0 3) (m.theta 1 3) (m.theta 3 9)
  exact rule26766 (meaning t m 2246) (meaning t m 3286) (meaning t m 3842) source

theorem rule26772 (p2246 p2807 p3662 p4386 : Prop) (h : (¬ p2807) ∨ (¬ p3662) ∨ (¬ p2246) ∨ (¬ p4386)) : (¬ p2246) ∨ (¬ p2807) ∨ (¬ p3662) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial26772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory16028 (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7)
  exact rule26772 (meaning t m 2246) (meaning t m 2807) (meaning t m 3662) (meaning t m 4386) source

theorem rule26773 (p2027 p2797 p3115 p3413 p4385 p4392 p4975 : Prop) (h : (¬ p2797) ∨ p2027 ∨ (¬ p4392) ∨ (¬ p3413) ∨ (¬ p4385) ∨ (¬ p4975) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2797) ∨ (¬ p3115) ∨ (¬ p3413) ∨ (¬ p4385) ∨ (¬ p4392) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial26773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory16029 t (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 5 9)
  exact rule26773 (meaning t m 2027) (meaning t m 2797) (meaning t m 3115) (meaning t m 3413) (meaning t m 4385) (meaning t m 4392) (meaning t m 4975) source

theorem rule26775 (p2027 p2707 p2743 p2810 p4325 p4652 : Prop) (h : (¬ p4325) ∨ (¬ p2810) ∨ (¬ p2743) ∨ (¬ p4652) ∨ p2027 ∨ (¬ p2707)) : (p2027) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p4325) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial26775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4325)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory16031 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7)
  exact rule26775 (meaning t m 2027) (meaning t m 2707) (meaning t m 2743) (meaning t m 2810) (meaning t m 4325) (meaning t m 4652) source

theorem rule26778 (p2088 p2103 p3609 : Prop) (h : (¬ p2103) ∨ (¬ p2088) ∨ p3609) : (¬ p2088) ∨ (¬ p2103) ∨ (p3609) := by
  classical
  tauto

theorem initial26778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2103)) ∨ (meaning t m 3609) := by
  have source := ElevenTheory.theory16034 (m.theta 0 8) (m.theta 2 8) (m.theta 8 9)
  exact rule26778 (meaning t m 2088) (meaning t m 2103) (meaning t m 3609) source

theorem rule26779 (p2027 p2748 p3276 p3355 p3365 p3367 p3759 p4312 p4360 p4734 p5123 p5568 : Prop) (h : (¬ p4360) ∨ (¬ p5568) ∨ (¬ p4312) ∨ (¬ p3276) ∨ (¬ p3367) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p3759) ∨ (¬ p5123) ∨ (¬ p3355)) : (p2027) ∨ (¬ p2748) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4312) ∨ (¬ p4360) ∨ (¬ p4734) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial26779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory16035 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule26779 (meaning t m 2027) (meaning t m 2748) (meaning t m 3276) (meaning t m 3355) (meaning t m 3365) (meaning t m 3367) (meaning t m 3759) (meaning t m 4312) (meaning t m 4360) (meaning t m 4734) (meaning t m 5123) (meaning t m 5568) source

theorem rule26784 (p2027 p2122 p2177 p2245 p2774 p2952 p2992 p4041 p4360 p4733 : Prop) (h : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2774) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p4041) ∨ (¬ p2992) ∨ (¬ p4360) ∨ (¬ p2952) ∨ (¬ p2245)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial26784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory16040 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule26784 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2245) (meaning t m 2774) (meaning t m 2952) (meaning t m 2992) (meaning t m 4041) (meaning t m 4360) (meaning t m 4733) source

theorem rule26785 (p3027 p4044 p4360 : Prop) (h : (¬ p4044) ∨ (¬ p3027) ∨ (¬ p4360)) : (¬ p3027) ∨ (¬ p4044) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial26785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory16041 (m.theta 1 3) (m.theta 3 7) (m.theta 3 8)
  exact rule26785 (meaning t m 3027) (meaning t m 4044) (meaning t m 4360) source

theorem rule26786 (p3027 p3189 p4044 : Prop) (h : (¬ p4044) ∨ (¬ p3027) ∨ p3189) : (¬ p3027) ∨ (p3189) ∨ (¬ p4044) := by
  classical
  tauto

theorem initial26786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3027)) ∨ (meaning t m 3189) ∨ (¬ (meaning t m 4044)) := by
  have source := ElevenTheory.theory16042 (m.theta 1 3) (m.theta 3 7) (m.theta 3 8)
  exact rule26786 (meaning t m 3027) (meaning t m 3189) (meaning t m 4044) source

theorem rule26789 (p2005 p2027 p2114 p2476 p2573 p3367 p3641 : Prop) (h : (¬ p2005) ∨ p2114 ∨ (¬ p3367) ∨ (¬ p3641) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2476)) : (¬ p2005) ∨ (p2027) ∨ (p2114) ∨ (¬ p2476) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3641) := by
  classical
  tauto

theorem initial26789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3641)) := by
  have source := ElevenTheory.theory16045 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8)
  exact rule26789 (meaning t m 2005) (meaning t m 2027) (meaning t m 2114) (meaning t m 2476) (meaning t m 2573) (meaning t m 3367) (meaning t m 3641) source

theorem rule26792 (p2027 p2911 p3201 p3551 p4727 p5197 : Prop) (h : (¬ p3551) ∨ (¬ p5197) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p4727) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3551) ∨ (¬ p4727) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial26792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4727)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory16048 t (m.theta 0 4) (m.theta 0 7) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8)
  exact rule26792 (meaning t m 2027) (meaning t m 2911) (meaning t m 3201) (meaning t m 3551) (meaning t m 4727) (meaning t m 5197) source

theorem rule26795 (p1988 p2027 p2761 p2870 p3212 p3474 p3556 p4135 : Prop) (h : p2027 ∨ (¬ p3212) ∨ (¬ p2761) ∨ (¬ p4135) ∨ (¬ p1988) ∨ (¬ p2870) ∨ (¬ p3556) ∨ p3474) : (¬ p1988) ∨ (p2027) ∨ (¬ p2761) ∨ (¬ p2870) ∨ (¬ p3212) ∨ (p3474) ∨ (¬ p3556) ∨ (¬ p4135) := by
  classical
  tauto

theorem initial26795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3212)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4135)) := by
  have source := ElevenTheory.theory16051 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule26795 (meaning t m 1988) (meaning t m 2027) (meaning t m 2761) (meaning t m 2870) (meaning t m 3212) (meaning t m 3474) (meaning t m 3556) (meaning t m 4135) source

theorem rule26796 (p1984 p2027 p2114 p2819 p2829 p3591 p3923 : Prop) (h : p2114 ∨ p2027 ∨ (¬ p3923) ∨ (¬ p3591) ∨ (¬ p1984) ∨ (¬ p2819) ∨ (¬ p2829)) : (¬ p1984) ∨ (p2027) ∨ (p2114) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3591) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial26796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory16052 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 6) (m.theta 6 8)
  exact rule26796 (meaning t m 1984) (meaning t m 2027) (meaning t m 2114) (meaning t m 2819) (meaning t m 2829) (meaning t m 3591) (meaning t m 3923) source

theorem rule26797 (p2027 p2312 p2563 p3309 p4235 p4283 p4518 : Prop) (h : (¬ p2312) ∨ (¬ p3309) ∨ (¬ p4235) ∨ (¬ p4283) ∨ p2027 ∨ (¬ p4518) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2312) ∨ (¬ p2563) ∨ (¬ p3309) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4518) := by
  classical
  tauto

theorem initial26797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4518)) := by
  have source := ElevenTheory.theory16053 t (m.theta 0 7) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule26797 (meaning t m 2027) (meaning t m 2312) (meaning t m 2563) (meaning t m 3309) (meaning t m 4235) (meaning t m 4283) (meaning t m 4518) source

theorem rule26799 (p1990 p2027 p2246 p2545 p2563 p2958 p3051 p4111 p4235 : Prop) (h : (¬ p4235) ∨ (¬ p2563) ∨ (¬ p1990) ∨ p2545 ∨ (¬ p4111) ∨ (¬ p2958) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p3051)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2246) ∨ (p2545) ∨ (¬ p2563) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4111) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial26799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory16055 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule26799 (meaning t m 1990) (meaning t m 2027) (meaning t m 2246) (meaning t m 2545) (meaning t m 2563) (meaning t m 2958) (meaning t m 3051) (meaning t m 4111) (meaning t m 4235) source

theorem rule26802 (p2437 p3016 p3920 : Prop) (h : (¬ p3920) ∨ (¬ p3016) ∨ p2437) : (p2437) ∨ (¬ p3016) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial26802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2437) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory16058 (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule26802 (meaning t m 2437) (meaning t m 3016) (meaning t m 3920) source

theorem rule26805 (p2005 p2027 p2819 p2829 p2842 p3585 p3956 : Prop) (h : p2027 ∨ (¬ p3956) ∨ (¬ p3585) ∨ (¬ p2829) ∨ (¬ p2005) ∨ p2842 ∨ (¬ p2819)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (p2842) ∨ (¬ p3585) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial26805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory16061 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 8)
  exact rule26805 (meaning t m 2005) (meaning t m 2027) (meaning t m 2819) (meaning t m 2829) (meaning t m 2842) (meaning t m 3585) (meaning t m 3956) source

theorem rule26806 (p2005 p2027 p2122 p2588 p2829 p2842 p3585 : Prop) (h : p2027 ∨ (¬ p2588) ∨ (¬ p3585) ∨ p2842 ∨ (¬ p2005) ∨ (¬ p2829) ∨ (¬ p2122)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2588) ∨ (¬ p2829) ∨ (p2842) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial26806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory16062 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule26806 (meaning t m 2005) (meaning t m 2027) (meaning t m 2122) (meaning t m 2588) (meaning t m 2829) (meaning t m 2842) (meaning t m 3585) source

theorem rule26808 (p2027 p2313 p2386 p3309 p3574 p3948 p4338 p4814 : Prop) (h : (¬ p3574) ∨ (¬ p4814) ∨ (¬ p2386) ∨ (¬ p3948) ∨ p2027 ∨ (¬ p4338) ∨ (¬ p2313) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p3948) ∨ (¬ p4338) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial26808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory16064 t (m.theta 0 6) (m.theta 1 4) (m.theta 1 5) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule26808 (meaning t m 2027) (meaning t m 2313) (meaning t m 2386) (meaning t m 3309) (meaning t m 3574) (meaning t m 3948) (meaning t m 4338) (meaning t m 4814) source

end SunPrize.SMT
