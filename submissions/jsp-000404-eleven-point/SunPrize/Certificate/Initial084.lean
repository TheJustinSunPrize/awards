import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory068
import SunPrize.Certificate.Theory069
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule39328 (p2027 p2241 p2299 p2313 p2717 p2901 p2992 p4898 p5021 : Prop) (h : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p5021) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4898) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2717)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2717) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4898) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial39328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4898)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory28584 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule39328 (meaning t m 2027) (meaning t m 2241) (meaning t m 2299) (meaning t m 2313) (meaning t m 2717) (meaning t m 2901) (meaning t m 2992) (meaning t m 4898) (meaning t m 5021) source

theorem rule39329 (p2005 p2027 p2230 p2323 p2505 p2588 p2663 p3238 p3309 : Prop) (h : (¬ p2663) ∨ (¬ p2005) ∨ p2027 ∨ p2323 ∨ (¬ p2588) ∨ (¬ p3309) ∨ (¬ p2230) ∨ (¬ p2505) ∨ (¬ p3238)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2230) ∨ (p2323) ∨ (¬ p2505) ∨ (¬ p2588) ∨ (¬ p2663) ∨ (¬ p3238) ∨ (¬ p3309) := by
  classical
  tauto

theorem initial39329 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3309)) := by
  have source := ElevenTheory.theory28585 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule39329 (meaning t m 2005) (meaning t m 2027) (meaning t m 2230) (meaning t m 2323) (meaning t m 2505) (meaning t m 2588) (meaning t m 2663) (meaning t m 3238) (meaning t m 3309) source

theorem rule39330 (p2005 p2027 p2230 p2295 p2323 p2440 p2588 p2663 p3019 : Prop) (h : (¬ p3019) ∨ (¬ p2588) ∨ (¬ p2295) ∨ (¬ p2230) ∨ (¬ p2663) ∨ (¬ p2005) ∨ p2323 ∨ p2027 ∨ (¬ p2440)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2295) ∨ (p2323) ∨ (¬ p2440) ∨ (¬ p2588) ∨ (¬ p2663) ∨ (¬ p3019) := by
  classical
  tauto

theorem initial39330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3019)) := by
  have source := ElevenTheory.theory28586 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule39330 (meaning t m 2005) (meaning t m 2027) (meaning t m 2230) (meaning t m 2295) (meaning t m 2323) (meaning t m 2440) (meaning t m 2588) (meaning t m 2663) (meaning t m 3019) source

theorem rule39332 (p3743 p3744 p4036 p4038 : Prop) (h : (¬ p3744) ∨ (¬ p4036) ∨ (¬ p4038) ∨ (¬ p3743)) : (¬ p3743) ∨ (¬ p3744) ∨ (¬ p4036) ∨ (¬ p4038) := by
  classical
  tauto

theorem initial39332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4036)) ∨ (¬ (meaning t m 4038)) := by
  have source := ElevenTheory.theory28588 (m.theta 0 6) (m.theta 0 9) (m.theta 5 6) (m.theta 6 9)
  exact rule39332 (meaning t m 3743) (meaning t m 3744) (meaning t m 4036) (meaning t m 4038) source

theorem rule39333 (p2027 p2241 p2264 p3027 p3097 p3646 p4107 p4524 p4666 : Prop) (h : (¬ p4666) ∨ (¬ p2241) ∨ (¬ p3097) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p2264) ∨ (¬ p4524) ∨ (¬ p3027)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4524) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial39333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory28589 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39333 (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 3027) (meaning t m 3097) (meaning t m 3646) (meaning t m 4107) (meaning t m 4524) (meaning t m 4666) source

theorem rule39335 (p1979 p2027 p2313 p2459 p2633 p3952 p3955 p4347 p4356 : Prop) (h : p2633 ∨ (¬ p1979) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p4356) ∨ (¬ p3952) ∨ (¬ p4347) ∨ (¬ p2459) ∨ (¬ p3955)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3952) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial39335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory28591 t (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39335 (meaning t m 1979) (meaning t m 2027) (meaning t m 2313) (meaning t m 2459) (meaning t m 2633) (meaning t m 3952) (meaning t m 3955) (meaning t m 4347) (meaning t m 4356) source

theorem rule39338 (p2027 p2246 p2417 p2437 p2608 p2651 p2744 p3860 p3950 p4261 : Prop) (h : (¬ p2417) ∨ (¬ p2651) ∨ (¬ p3860) ∨ (¬ p2437) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2246) ∨ (¬ p3950) ∨ (¬ p2744) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial39338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory28594 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule39338 (meaning t m 2027) (meaning t m 2246) (meaning t m 2417) (meaning t m 2437) (meaning t m 2608) (meaning t m 2651) (meaning t m 2744) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) source

theorem rule39339 (p3690 p3817 p4909 : Prop) (h : (¬ p4909) ∨ (¬ p3690) ∨ p3817) : (¬ p3690) ∨ (p3817) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial39339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3690)) ∨ (meaning t m 3817) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory28595 (m.theta 1 7) (m.theta 5 7) (m.theta 7 9)
  exact rule39339 (meaning t m 3690) (meaning t m 3817) (meaning t m 4909) source

theorem rule39342 (p1998 p2027 p2247 p2688 p3256 p3449 p4288 p4348 : Prop) (h : p2688 ∨ (¬ p4288) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p1998) ∨ (¬ p2247) ∨ (¬ p3256)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3256) ∨ (¬ p3449) ∨ (¬ p4288) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial39342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4288)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory28598 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39342 (meaning t m 1998) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3256) (meaning t m 3449) (meaning t m 4288) (meaning t m 4348) source

theorem rule39343 (p2027 p2246 p2744 p2780 p2901 p2946 p3246 p3366 p3950 p4347 p4358 : Prop) (h : (¬ p3246) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p2780) ∨ (¬ p4347) ∨ (¬ p3950) ∨ (¬ p2246) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p4358)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial39343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory28599 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule39343 (meaning t m 2027) (meaning t m 2246) (meaning t m 2744) (meaning t m 2780) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3366) (meaning t m 3950) (meaning t m 4347) (meaning t m 4358) source

theorem rule39345 (p2027 p2246 p2387 p2744 p2778 p2819 p2901 p2946 p3246 p3366 p3917 p4625 : Prop) (h : (¬ p4625) ∨ (¬ p2901) ∨ (¬ p3917) ∨ (¬ p2387) ∨ (¬ p2819) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2778) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2387) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3917) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial39345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory28601 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule39345 (meaning t m 2027) (meaning t m 2246) (meaning t m 2387) (meaning t m 2744) (meaning t m 2778) (meaning t m 2819) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3366) (meaning t m 3917) (meaning t m 4625) source

theorem rule39347 (p2027 p2860 p3083 p3389 p3519 p3645 p3646 p3694 p3742 p4158 p4376 p4874 : Prop) (h : (¬ p4376) ∨ (¬ p3083) ∨ (¬ p3519) ∨ (¬ p3742) ∨ (¬ p3694) ∨ (¬ p3645) ∨ (¬ p4158) ∨ (¬ p3389) ∨ p2027 ∨ (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4874)) : (p2027) ∨ (¬ p2860) ∨ (¬ p3083) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3694) ∨ (¬ p3742) ∨ (¬ p4158) ∨ (¬ p4376) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial39347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4158)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory28603 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8)
  exact rule39347 (meaning t m 2027) (meaning t m 2860) (meaning t m 3083) (meaning t m 3389) (meaning t m 3519) (meaning t m 3645) (meaning t m 3646) (meaning t m 3694) (meaning t m 3742) (meaning t m 4158) (meaning t m 4376) (meaning t m 4874) source

theorem rule39348 (p2027 p2230 p2246 p2440 p2663 p2744 p3266 p3343 p4332 p4379 p5387 : Prop) (h : (¬ p2744) ∨ (¬ p2246) ∨ (¬ p2663) ∨ (¬ p5387) ∨ (¬ p4379) ∨ (¬ p2440) ∨ (¬ p3343) ∨ (¬ p4332) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3266)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3266) ∨ (¬ p3343) ∨ (¬ p4332) ∨ (¬ p4379) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial39348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory28604 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 9) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule39348 (meaning t m 2027) (meaning t m 2230) (meaning t m 2246) (meaning t m 2440) (meaning t m 2663) (meaning t m 2744) (meaning t m 3266) (meaning t m 3343) (meaning t m 4332) (meaning t m 4379) (meaning t m 5387) source

theorem rule39349 (p2027 p2138 p3083 p3366 p3389 p3519 p3742 p3758 p3989 p4376 p4596 : Prop) (h : (¬ p3758) ∨ (¬ p4596) ∨ (¬ p2138) ∨ (¬ p3989) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3742) ∨ (¬ p3083) ∨ p2027 ∨ (¬ p4376) ∨ (¬ p3389)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3742) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4376) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial39349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory28605 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule39349 (meaning t m 2027) (meaning t m 2138) (meaning t m 3083) (meaning t m 3366) (meaning t m 3389) (meaning t m 3519) (meaning t m 3742) (meaning t m 3758) (meaning t m 3989) (meaning t m 4376) (meaning t m 4596) source

theorem rule39350 (p2027 p2246 p2387 p2744 p2778 p2901 p2946 p3366 p4129 p4347 p4444 p4826 : Prop) (h : (¬ p4129) ∨ (¬ p2778) ∨ (¬ p4826) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p4444) ∨ (¬ p2946) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p4347) ∨ (¬ p2387) ∨ (¬ p3366)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2387) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3366) ∨ (¬ p4129) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial39350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory28606 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule39350 (meaning t m 2027) (meaning t m 2246) (meaning t m 2387) (meaning t m 2744) (meaning t m 2778) (meaning t m 2901) (meaning t m 2946) (meaning t m 3366) (meaning t m 4129) (meaning t m 4347) (meaning t m 4444) (meaning t m 4826) source

theorem rule39353 (p2027 p2136 p2860 p3166 p3256 p3646 p3694 p4348 p4786 p4905 : Prop) (h : (¬ p4905) ∨ p2027 ∨ (¬ p3694) ∨ (¬ p4348) ∨ (¬ p4786) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p2860) ∨ (¬ p2136) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2860) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3646) ∨ (¬ p3694) ∨ (¬ p4348) ∨ (¬ p4786) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial39353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory28609 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 5) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39353 (meaning t m 2027) (meaning t m 2136) (meaning t m 2860) (meaning t m 3166) (meaning t m 3256) (meaning t m 3646) (meaning t m 3694) (meaning t m 4348) (meaning t m 4786) (meaning t m 4905) source

theorem rule39355 (p2027 p2780 p2946 p3115 p3680 p4358 p4786 p5123 p5580 : Prop) (h : (¬ p3680) ∨ (¬ p5123) ∨ (¬ p4358) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p5580) ∨ (¬ p2780) ∨ (¬ p4786) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p4358) ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial39355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory28611 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule39355 (meaning t m 2027) (meaning t m 2780) (meaning t m 2946) (meaning t m 3115) (meaning t m 3680) (meaning t m 4358) (meaning t m 4786) (meaning t m 5123) (meaning t m 5580) source

theorem rule39356 (p2027 p2608 p3343 p3389 p3519 p3742 p3860 p4261 p4332 p4376 : Prop) (h : (¬ p4332) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p4261) ∨ (¬ p3860) ∨ (¬ p3343) ∨ (¬ p2608) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p4376)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3343) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3742) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4332) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial39356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory28612 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 8 9)
  exact rule39356 (meaning t m 2027) (meaning t m 2608) (meaning t m 3343) (meaning t m 3389) (meaning t m 3519) (meaning t m 3742) (meaning t m 3860) (meaning t m 4261) (meaning t m 4332) (meaning t m 4376) source

theorem rule39357 (p2027 p2608 p3083 p3389 p3519 p3591 p3742 p3923 p4376 p4596 : Prop) (h : p2027 ∨ (¬ p3389) ∨ (¬ p2608) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p3519) ∨ (¬ p3742) ∨ (¬ p4596) ∨ (¬ p4376) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3083) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p3742) ∨ (¬ p3923) ∨ (¬ p4376) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial39357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory28613 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8)
  exact rule39357 (meaning t m 2027) (meaning t m 2608) (meaning t m 3083) (meaning t m 3389) (meaning t m 3519) (meaning t m 3591) (meaning t m 3742) (meaning t m 3923) (meaning t m 4376) (meaning t m 4596) source

theorem rule39360 (p2608 p3834 p5333 : Prop) (h : (¬ p2608) ∨ (¬ p3834) ∨ (¬ p5333)) : (¬ p2608) ∨ (¬ p3834) ∨ (¬ p5333) := by
  classical
  tauto

theorem initial39360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 5333)) := by
  have source := ElevenTheory.theory28616 (m.theta 0 1) (m.theta 1 2) (m.theta 1 9)
  exact rule39360 (meaning t m 2608) (meaning t m 3834) (meaning t m 5333) source

theorem rule39363 (p2027 p2246 p2608 p2744 p2946 p3115 p3680 p3860 p5123 p5693 : Prop) (h : p2027 ∨ (¬ p5123) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p2946) ∨ (¬ p3860) ∨ (¬ p3115) ∨ (¬ p5693) ∨ (¬ p2608) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p3860) ∨ (¬ p5123) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial39363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory28619 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 5) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule39363 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 2946) (meaning t m 3115) (meaning t m 3680) (meaning t m 3860) (meaning t m 5123) (meaning t m 5693) source

theorem rule39364 (p2027 p2246 p2608 p2663 p2744 p3276 p3355 p3817 p4322 p4366 p4395 : Prop) (h : (¬ p3355) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p4395) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2663) ∨ (¬ p3817) ∨ (¬ p2608) ∨ (¬ p3276) ∨ (¬ p4322)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3817) ∨ (¬ p4322) ∨ (¬ p4366) ∨ (¬ p4395) := by
  classical
  tauto

theorem initial39364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4395)) := by
  have source := ElevenTheory.theory28620 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 4 9) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule39364 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2663) (meaning t m 2744) (meaning t m 3276) (meaning t m 3355) (meaning t m 3817) (meaning t m 4322) (meaning t m 4366) (meaning t m 4395) source

theorem rule39367 (p2027 p2246 p2299 p2313 p2744 p2778 p2946 p3115 p3366 p3680 p5123 p5558 : Prop) (h : (¬ p3366) ∨ (¬ p2744) ∨ (¬ p5558) ∨ (¬ p2246) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p2778) ∨ (¬ p2946) ∨ (¬ p2313) ∨ (¬ p2299) ∨ (¬ p5123) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3366) ∨ (¬ p3680) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial39367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory28623 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule39367 (meaning t m 2027) (meaning t m 2246) (meaning t m 2299) (meaning t m 2313) (meaning t m 2744) (meaning t m 2778) (meaning t m 2946) (meaning t m 3115) (meaning t m 3366) (meaning t m 3680) (meaning t m 5123) (meaning t m 5558) source

theorem rule39370 (p2027 p2156 p2881 p3551 p4555 p4984 : Prop) (h : p2027 ∨ (¬ p2881) ∨ (¬ p2156) ∨ (¬ p4555) ∨ (¬ p4984) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p4555) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial39370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4555)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory28626 t (m.theta 0 5) (m.theta 0 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule39370 (meaning t m 2027) (meaning t m 2156) (meaning t m 2881) (meaning t m 3551) (meaning t m 4555) (meaning t m 4984) source

theorem rule39375 (p2027 p2138 p2246 p2437 p2651 p2744 p2911 p3366 p3758 p3989 p4503 : Prop) (h : (¬ p2437) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2651) ∨ (¬ p2138) ∨ (¬ p3758) ∨ (¬ p4503) ∨ (¬ p2246) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2911) ∨ (¬ p3366) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial39375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory28631 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule39375 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2437) (meaning t m 2651) (meaning t m 2744) (meaning t m 2911) (meaning t m 3366) (meaning t m 3758) (meaning t m 3989) (meaning t m 4503) source

theorem rule39378 (p2027 p2498 p2922 p3379 p3591 p4711 : Prop) (h : (¬ p2922) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4711) ∨ (¬ p2498) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2498) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p4711) := by
  classical
  tauto

theorem initial39378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4711)) := by
  have source := ElevenTheory.theory28634 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6) (m.theta 4 7)
  exact rule39378 (meaning t m 2027) (meaning t m 2498) (meaning t m 2922) (meaning t m 3379) (meaning t m 3591) (meaning t m 4711) source

theorem rule39379 (p1975 p2027 p2406 p2409 p2553 p2573 p2589 : Prop) (h : (¬ p2573) ∨ (¬ p2553) ∨ (¬ p2589) ∨ p2027 ∨ p2409 ∨ (¬ p1975) ∨ (¬ p2406)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2589) := by
  classical
  tauto

theorem initial39379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) := by
  have source := ElevenTheory.theory28635 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule39379 (meaning t m 1975) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2553) (meaning t m 2573) (meaning t m 2589) source

theorem rule39380 (p2017 p2027 p2323 p2553 p2651 p3016 p3791 : Prop) (h : p2027 ∨ (¬ p2017) ∨ p2323 ∨ (¬ p2651) ∨ (¬ p2553) ∨ (¬ p3791) ∨ (¬ p3016)) : (¬ p2017) ∨ (p2027) ∨ (p2323) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3791) := by
  classical
  tauto

theorem initial39380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2017)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3791)) := by
  have source := ElevenTheory.theory28636 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 10)
  exact rule39380 (meaning t m 2017) (meaning t m 2027) (meaning t m 2323) (meaning t m 2553) (meaning t m 2651) (meaning t m 3016) (meaning t m 3791) source

theorem rule39382 (p2027 p2249 p2499 p2657 p3027 p3487 p3506 p4137 p4381 p4625 p4661 : Prop) (h : (¬ p2249) ∨ (¬ p3487) ∨ (¬ p3027) ∨ (¬ p2499) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p4625) ∨ (¬ p2657) ∨ (¬ p4137) ∨ (¬ p4661) ∨ (¬ p3506)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3027) ∨ (¬ p3487) ∨ (¬ p3506) ∨ (¬ p4137) ∨ (¬ p4381) ∨ (¬ p4625) ∨ (¬ p4661) := by
  classical
  tauto

theorem initial39382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4661)) := by
  have source := ElevenTheory.theory28638 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 3 9) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule39382 (meaning t m 2027) (meaning t m 2249) (meaning t m 2499) (meaning t m 2657) (meaning t m 3027) (meaning t m 3487) (meaning t m 3506) (meaning t m 4137) (meaning t m 4381) (meaning t m 4625) (meaning t m 4661) source

theorem rule39383 (p1998 p2027 p2470 p2528 p2656 p2688 p2727 p4348 : Prop) (h : (¬ p2656) ∨ (¬ p4348) ∨ (¬ p1998) ∨ (¬ p2528) ∨ (¬ p2470) ∨ p2688 ∨ p2027 ∨ (¬ p2727)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial39383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory28639 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39383 (meaning t m 1998) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 4348) source

theorem rule39385 (p2509 p4116 p4256 : Prop) (h : (¬ p4256) ∨ (¬ p4116) ∨ p2509) : (p2509) ∨ (¬ p4116) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial39385 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2509) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory28641 (m.theta 1 4) (m.theta 3 4) (m.theta 4 8)
  exact rule39385 (meaning t m 2509) (meaning t m 4116) (meaning t m 4256) source

theorem rule39387 (p1998 p2027 p2264 p2396 p2553 p3008 p3947 : Prop) (h : (¬ p2396) ∨ (¬ p2553) ∨ (¬ p1998) ∨ p3008 ∨ p2027 ∨ (¬ p2264) ∨ (¬ p3947)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial39387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory28643 t (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39387 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2396) (meaning t m 2553) (meaning t m 3008) (meaning t m 3947) source

theorem rule39390 (p2510 p3584 p3874 : Prop) (h : (¬ p2510) ∨ (¬ p3874) ∨ p3584) : (¬ p2510) ∨ (p3584) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial39390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2510)) ∨ (meaning t m 3584) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory28646 (m.theta 2 4) (m.theta 4 6) (m.theta 4 8)
  exact rule39390 (meaning t m 2510) (meaning t m 3584) (meaning t m 3874) source

theorem rule39393 (p2027 p2103 p2299 p3537 p3588 p4403 p4477 : Prop) (h : (¬ p2299) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p4477) ∨ (¬ p2103) ∨ p2027 ∨ (¬ p4403)) : (p2027) ∨ (¬ p2103) ∨ (¬ p2299) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p4403) ∨ (¬ p4477) := by
  classical
  tauto

theorem initial39393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2103)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4403)) ∨ (¬ (meaning t m 4477)) := by
  have source := ElevenTheory.theory28649 t (m.theta 0 8) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 6 7) (m.theta 7 8)
  exact rule39393 (meaning t m 2027) (meaning t m 2103) (meaning t m 2299) (meaning t m 3537) (meaning t m 3588) (meaning t m 4403) (meaning t m 4477) source

theorem rule39400 (p1998 p2027 p2313 p2383 p2997 p3979 p5558 : Prop) (h : p2997 ∨ (¬ p2383) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p5558) ∨ (¬ p3979)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (p2997) ∨ (¬ p3979) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial39400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory28656 t (m.theta 0 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule39400 (meaning t m 1998) (meaning t m 2027) (meaning t m 2313) (meaning t m 2383) (meaning t m 2997) (meaning t m 3979) (meaning t m 5558) source

theorem rule39405 (p1977 p2027 p2202 p2589 p3389 p3742 p4111 : Prop) (h : (¬ p4111) ∨ (¬ p1977) ∨ (¬ p2589) ∨ p2027 ∨ p2202 ∨ (¬ p3742) ∨ (¬ p3389)) : (¬ p1977) ∨ (p2027) ∨ (p2202) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial39405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory28661 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule39405 (meaning t m 1977) (meaning t m 2027) (meaning t m 2202) (meaning t m 2589) (meaning t m 3389) (meaning t m 3742) (meaning t m 4111) source

theorem rule39407 (p2437 p2901 p3569 p4700 : Prop) (h : (¬ p3569) ∨ (¬ p4700) ∨ (¬ p2437) ∨ p2901) : (¬ p2437) ∨ (p2901) ∨ (¬ p3569) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial39407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2437)) ∨ (meaning t m 2901) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory28663 (m.theta 3 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7)
  exact rule39407 (meaning t m 2437) (meaning t m 2901) (meaning t m 3569) (meaning t m 4700) source

theorem rule39409 (p2027 p2248 p2651 p3083 p3548 p4149 p4348 p4366 p5122 : Prop) (h : (¬ p4366) ∨ (¬ p4149) ∨ (¬ p3083) ∨ (¬ p5122) ∨ (¬ p2651) ∨ (¬ p2248) ∨ (¬ p3548) ∨ (¬ p4348) ∨ p2027) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3548) ∨ (¬ p4149) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial39409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory28665 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule39409 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 3083) (meaning t m 3548) (meaning t m 4149) (meaning t m 4348) (meaning t m 4366) (meaning t m 5122) source

theorem rule39410 (p2619 p2860 p3988 : Prop) (h : (¬ p3988) ∨ (¬ p2619) ∨ p2860) : (¬ p2619) ∨ (p2860) ∨ (¬ p3988) := by
  classical
  tauto

theorem initial39410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2619)) ∨ (meaning t m 2860) ∨ (¬ (meaning t m 3988)) := by
  have source := ElevenTheory.theory28666 (m.theta 2 5) (m.theta 5 6) (m.theta 5 8)
  exact rule39410 (meaning t m 2619) (meaning t m 2860) (meaning t m 3988) source

theorem rule39414 (p2027 p2248 p2651 p3016 p3564 p3954 p4242 p4330 p4340 : Prop) (h : (¬ p4242) ∨ (¬ p4330) ∨ (¬ p2651) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p2248) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4330) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial39414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory28670 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9)
  exact rule39414 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 3016) (meaning t m 3564) (meaning t m 3954) (meaning t m 4242) (meaning t m 4330) (meaning t m 4340) source

theorem rule39417 (p1985 p2027 p2166 p2210 p2699 p2901 p3497 : Prop) (h : (¬ p2901) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ p2699 ∨ (¬ p1985) ∨ (¬ p3497)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2901) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial39417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory28673 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8)
  exact rule39417 (meaning t m 1985) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2699) (meaning t m 2901) (meaning t m 3497) source

theorem rule39420 (p2027 p2248 p2427 p2542 p2651 p3551 p3609 p4348 p4805 p4898 p5206 : Prop) (h : (¬ p3551) ∨ (¬ p2427) ∨ (¬ p2248) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p4805) ∨ (¬ p5206) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4898)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3551) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4805) ∨ (¬ p4898) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial39420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4805)) ∨ (¬ (meaning t m 4898)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory28676 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 7) (m.theta 2 7) (m.theta 2 8) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule39420 (meaning t m 2027) (meaning t m 2248) (meaning t m 2427) (meaning t m 2542) (meaning t m 2651) (meaning t m 3551) (meaning t m 3609) (meaning t m 4348) (meaning t m 4805) (meaning t m 4898) (meaning t m 5206) source

theorem rule39421 (p1991 p2027 p2819 p2963 p2997 p3324 p3822 : Prop) (h : p2997 ∨ (¬ p1991) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p2963)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2819) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3324) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial39421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory28677 t (m.theta 0 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule39421 (meaning t m 1991) (meaning t m 2027) (meaning t m 2819) (meaning t m 2963) (meaning t m 2997) (meaning t m 3324) (meaning t m 3822) source

theorem rule39423 (p2396 p3644 p3657 p4710 : Prop) (h : (¬ p3657) ∨ (¬ p3644) ∨ (¬ p4710) ∨ (¬ p2396)) : (¬ p2396) ∨ (¬ p3644) ∨ (¬ p3657) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial39423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory28679 (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39423 (meaning t m 2396) (meaning t m 3644) (meaning t m 3657) (meaning t m 4710) source

theorem rule39429 (p1992 p2027 p2427 p2765 p3583 p4110 p4244 : Prop) (h : (¬ p4110) ∨ (¬ p2427) ∨ p2765 ∨ (¬ p1992) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p4244)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2427) ∨ (p2765) ∨ (¬ p3583) ∨ (¬ p4110) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial39429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory28685 t (m.theta 1 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule39429 (meaning t m 1992) (meaning t m 2027) (meaning t m 2427) (meaning t m 2765) (meaning t m 3583) (meaning t m 4110) (meaning t m 4244) source

theorem rule39431 (p2027 p2459 p2534 p2696 p2753 p3136 p3156 p3347 p3540 p4186 p4902 p5216 : Prop) (h : (¬ p4902) ∨ (¬ p2459) ∨ (¬ p4186) ∨ (¬ p3540) ∨ (¬ p3347) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2696) ∨ (¬ p3156) ∨ (¬ p5216) ∨ (¬ p3136)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p4186) ∨ (¬ p4902) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28687 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39431 (meaning t m 2027) (meaning t m 2459) (meaning t m 2534) (meaning t m 2696) (meaning t m 2753) (meaning t m 3136) (meaning t m 3156) (meaning t m 3347) (meaning t m 3540) (meaning t m 4186) (meaning t m 4902) (meaning t m 5216) source

theorem rule39432 (p1996 p2027 p2459 p2475 p2534 p2633 p2685 p3177 p3877 : Prop) (h : (¬ p1996) ∨ (¬ p2459) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p3177) ∨ (¬ p2475) ∨ p2633 ∨ (¬ p2685) ∨ (¬ p3877)) : (¬ p1996) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2475) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p2685) ∨ (¬ p3177) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial39432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory28688 t (m.theta 0 8) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39432 (meaning t m 1996) (meaning t m 2027) (meaning t m 2459) (meaning t m 2475) (meaning t m 2534) (meaning t m 2633) (meaning t m 2685) (meaning t m 3177) (meaning t m 3877) source

theorem rule39436 (p2027 p2870 p2957 p3556 p4195 p4313 p4700 p4972 : Prop) (h : (¬ p4700) ∨ (¬ p4195) ∨ (¬ p3556) ∨ (¬ p4313) ∨ (¬ p2957) ∨ (¬ p2870) ∨ p2027 ∨ (¬ p4972)) : (p2027) ∨ (¬ p2870) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4195) ∨ (¬ p4313) ∨ (¬ p4700) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial39436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory28692 t (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7)
  exact rule39436 (meaning t m 2027) (meaning t m 2870) (meaning t m 2957) (meaning t m 3556) (meaning t m 4195) (meaning t m 4313) (meaning t m 4700) (meaning t m 4972) source

theorem rule39437 (p2027 p2608 p2829 p3483 p3540 p3644 p4330 p4348 p5193 : Prop) (h : (¬ p2829) ∨ (¬ p4348) ∨ (¬ p5193) ∨ (¬ p3644) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p4330) ∨ (¬ p2608) ∨ (¬ p3483)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3483) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28693 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule39437 (meaning t m 2027) (meaning t m 2608) (meaning t m 2829) (meaning t m 3483) (meaning t m 3540) (meaning t m 3644) (meaning t m 4330) (meaning t m 4348) (meaning t m 5193) source

theorem rule39438 (p2027 p2122 p2177 p2406 p2509 p2589 p2774 p4108 p4438 p4733 : Prop) (h : (¬ p2774) ∨ (¬ p2177) ∨ (¬ p4733) ∨ (¬ p4108) ∨ (¬ p2589) ∨ (¬ p2122) ∨ (¬ p4438) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2589) ∨ (¬ p2774) ∨ (¬ p4108) ∨ (¬ p4438) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial39438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory28694 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule39438 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2406) (meaning t m 2509) (meaning t m 2589) (meaning t m 2774) (meaning t m 4108) (meaning t m 4438) (meaning t m 4733) source

theorem rule39439 (p2737 p3599 p5459 : Prop) (h : (¬ p2737) ∨ (¬ p5459) ∨ p3599) : (¬ p2737) ∨ (p3599) ∨ (¬ p5459) := by
  classical
  tauto

theorem initial39439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2737)) ∨ (meaning t m 3599) ∨ (¬ (meaning t m 5459)) := by
  have source := ElevenTheory.theory28695 (m.theta 1 2) (m.theta 2 3) (m.theta 2 9)
  exact rule39439 (meaning t m 2737) (meaning t m 3599) (meaning t m 5459) source

theorem rule39441 (p1977 p2027 p2765 p2952 p3166 p3879 p4110 p4360 : Prop) (h : (¬ p4110) ∨ (¬ p1977) ∨ (¬ p2952) ∨ p2765 ∨ (¬ p3879) ∨ p2027 ∨ (¬ p3166) ∨ (¬ p4360)) : (¬ p1977) ∨ (p2027) ∨ (p2765) ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p3879) ∨ (¬ p4110) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial39441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory28697 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6)
  exact rule39441 (meaning t m 1977) (meaning t m 2027) (meaning t m 2765) (meaning t m 2952) (meaning t m 3166) (meaning t m 3879) (meaning t m 4110) (meaning t m 4360) source

theorem rule39444 (p2027 p2284 p2745 p3136 p3368 p4173 : Prop) (h : p2027 ∨ (¬ p2745) ∨ (¬ p3368) ∨ (¬ p2284) ∨ (¬ p4173) ∨ (¬ p3136)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2745) ∨ (¬ p3136) ∨ (¬ p3368) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial39444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory28700 t (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6)
  exact rule39444 (meaning t m 2027) (meaning t m 2284) (meaning t m 2745) (meaning t m 3136) (meaning t m 3368) (meaning t m 4173) source

theorem rule39445 (p2027 p2255 p2331 p3323 p4026 p4245 : Prop) (h : p2027 ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p4245) ∨ (¬ p4026)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p4026) ∨ (¬ p4245) := by
  classical
  tauto

theorem initial39445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4245)) := by
  have source := ElevenTheory.theory28701 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 6 9)
  exact rule39445 (meaning t m 2027) (meaning t m 2255) (meaning t m 2331) (meaning t m 3323) (meaning t m 4026) (meaning t m 4245) source

theorem rule39446 (p2027 p2192 p2210 p3125 p3425 p3659 p4330 p4348 p4736 : Prop) (h : (¬ p4736) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p3425) ∨ (¬ p2210) ∨ (¬ p3125) ∨ (¬ p4330) ∨ (¬ p3659) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3125) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial39446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory28702 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule39446 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 3125) (meaning t m 3425) (meaning t m 3659) (meaning t m 4330) (meaning t m 4348) (meaning t m 4736) source

theorem rule39448 (p2027 p2210 p2972 p3347 p3540 p3644 p3954 p4348 p4450 p5216 : Prop) (h : (¬ p2210) ∨ (¬ p4348) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p5216) ∨ (¬ p3954) ∨ (¬ p2972) ∨ (¬ p3347) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2972) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28704 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule39448 (meaning t m 2027) (meaning t m 2210) (meaning t m 2972) (meaning t m 3347) (meaning t m 3540) (meaning t m 3644) (meaning t m 3954) (meaning t m 4348) (meaning t m 4450) (meaning t m 5216) source

theorem rule39450 (p2027 p2341 p2665 p3644 p3742 p5201 : Prop) (h : (¬ p2665) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p5201) ∨ (¬ p3742) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2665) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial39450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory28706 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule39450 (meaning t m 2027) (meaning t m 2341) (meaning t m 2665) (meaning t m 3644) (meaning t m 3742) (meaning t m 5201) source

theorem rule39451 (p2027 p2531 p3641 p3684 p4110 p4509 : Prop) (h : p2027 ∨ (¬ p2531) ∨ (¬ p3684) ∨ (¬ p4509) ∨ (¬ p4110) ∨ (¬ p3641)) : (p2027) ∨ (¬ p2531) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4110) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial39451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory28707 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8)
  exact rule39451 (meaning t m 2027) (meaning t m 2531) (meaning t m 3641) (meaning t m 3684) (meaning t m 4110) (meaning t m 4509) source

theorem rule39454 (p1997 p2027 p2764 p3051 p4032 p4235 p4381 p4382 : Prop) (h : (¬ p3051) ∨ p2027 ∨ (¬ p4381) ∨ p2764 ∨ (¬ p4235) ∨ (¬ p1997) ∨ (¬ p4382) ∨ (¬ p4032)) : (¬ p1997) ∨ (p2027) ∨ (p2764) ∨ (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4235) ∨ (¬ p4381) ∨ (¬ p4382) := by
  classical
  tauto

theorem initial39454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4382)) := by
  have source := ElevenTheory.theory28710 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule39454 (meaning t m 1997) (meaning t m 2027) (meaning t m 2764) (meaning t m 3051) (meaning t m 4032) (meaning t m 4235) (meaning t m 4381) (meaning t m 4382) source

theorem rule39456 (p2027 p3609 p3692 p3758 p4509 p4744 : Prop) (h : (¬ p3692) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p4744) ∨ (¬ p4509) ∨ (¬ p3609)) : (p2027) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3758) ∨ (¬ p4509) ∨ (¬ p4744) := by
  classical
  tauto

theorem initial39456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4509)) ∨ (¬ (meaning t m 4744)) := by
  have source := ElevenTheory.theory28712 t (m.theta 2 5) (m.theta 2 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule39456 (meaning t m 2027) (meaning t m 3609) (meaning t m 3692) (meaning t m 3758) (meaning t m 4509) (meaning t m 4744) source

theorem rule39457 (p2027 p2192 p2210 p2274 p2911 p3055 p3659 p3686 p4712 p4736 : Prop) (h : (¬ p4736) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p4712) ∨ (¬ p2911) ∨ (¬ p3055) ∨ (¬ p2192) ∨ (¬ p3686) ∨ (¬ p2210) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (¬ p2911) ∨ (¬ p3055) ∨ (¬ p3659) ∨ (¬ p3686) ∨ (¬ p4712) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial39457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory28713 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule39457 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2274) (meaning t m 2911) (meaning t m 3055) (meaning t m 3659) (meaning t m 3686) (meaning t m 4712) (meaning t m 4736) source

theorem rule39458 (p2027 p3537 p3583 p3758 p4188 p4509 : Prop) (h : (¬ p4188) ∨ (¬ p4509) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p3537) ∨ (¬ p3758)) : (p2027) ∨ (¬ p3537) ∨ (¬ p3583) ∨ (¬ p3758) ∨ (¬ p4188) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial39458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory28714 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 5 6) (m.theta 5 8)
  exact rule39458 (meaning t m 2027) (meaning t m 3537) (meaning t m 3583) (meaning t m 3758) (meaning t m 4188) (meaning t m 4509) source

theorem rule39459 (p1988 p2027 p2202 p2427 p3212 p3556 p3680 : Prop) (h : (¬ p3212) ∨ p2202 ∨ (¬ p2427) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3556) ∨ (¬ p3680)) : (¬ p1988) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p3212) ∨ (¬ p3556) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial39459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory28715 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule39459 (meaning t m 1988) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 3212) (meaning t m 3556) (meaning t m 3680) source

theorem rule39461 (p2027 p3875 p4149 p4278 p4666 p5558 : Prop) (h : (¬ p3875) ∨ (¬ p4666) ∨ (¬ p4278) ∨ (¬ p4149) ∨ (¬ p5558) ∨ p2027) : (p2027) ∨ (¬ p3875) ∨ (¬ p4149) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial39461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory28717 t (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule39461 (meaning t m 2027) (meaning t m 3875) (meaning t m 4149) (meaning t m 4278) (meaning t m 4666) (meaning t m 5558) source

theorem rule39464 (p1998 p2027 p2177 p2319 p2641 p2688 p3516 p3567 p4107 : Prop) (h : (¬ p1998) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p3567) ∨ p2688 ∨ (¬ p2319) ∨ (¬ p3516) ∨ (¬ p4107)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2319) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p3516) ∨ (¬ p3567) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial39464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory28720 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39464 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2319) (meaning t m 2641) (meaning t m 2688) (meaning t m 3516) (meaning t m 3567) (meaning t m 4107) source

theorem rule39465 (p2027 p2166 p2299 p3486 p4042 p4559 : Prop) (h : (¬ p4559) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3486) ∨ (¬ p4042) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2299) ∨ (¬ p3486) ∨ (¬ p4042) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial39465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory28721 t (m.theta 1 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule39465 (meaning t m 2027) (meaning t m 2166) (meaning t m 2299) (meaning t m 3486) (meaning t m 4042) (meaning t m 4559) source

theorem rule39466 (p2027 p3549 p4181 p4317 p4405 p5580 : Prop) (h : (¬ p4317) ∨ (¬ p3549) ∨ (¬ p5580) ∨ (¬ p4405) ∨ p2027 ∨ (¬ p4181)) : (p2027) ∨ (¬ p3549) ∨ (¬ p4181) ∨ (¬ p4317) ∨ (¬ p4405) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial39466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4317)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory28722 t (m.theta 1 6) (m.theta 1 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule39466 (meaning t m 2027) (meaning t m 3549) (meaning t m 4181) (meaning t m 4317) (meaning t m 4405) (meaning t m 5580) source

theorem rule39469 (p2027 p2122 p2177 p2476 p2534 p2774 p3146 p4108 p4733 p4905 : Prop) (h : (¬ p4905) ∨ (¬ p2774) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p2476) ∨ p2027 ∨ (¬ p4108) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2774) ∨ (¬ p3146) ∨ (¬ p4108) ∨ (¬ p4733) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial39469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory28725 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule39469 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2476) (meaning t m 2534) (meaning t m 2774) (meaning t m 3146) (meaning t m 4108) (meaning t m 4733) (meaning t m 4905) source

theorem rule39470 (p2027 p2497 p2518 p2553 p3549 p4598 : Prop) (h : (¬ p4598) ∨ (¬ p3549) ∨ (¬ p2497) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p2518)) : (p2027) ∨ (¬ p2497) ∨ (¬ p2518) ∨ (¬ p2553) ∨ (¬ p3549) ∨ (¬ p4598) := by
  classical
  tauto

theorem initial39470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4598)) := by
  have source := ElevenTheory.theory28726 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule39470 (meaning t m 2027) (meaning t m 2497) (meaning t m 2518) (meaning t m 2553) (meaning t m 3549) (meaning t m 4598) source

theorem rule39471 (p2027 p2241 p2589 p3506 p3842 p4235 p4831 p5193 p5660 : Prop) (h : (¬ p5660) ∨ (¬ p3842) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p5193) ∨ (¬ p2589) ∨ (¬ p4831) ∨ (¬ p2241) ∨ (¬ p3506)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4235) ∨ (¬ p4831) ∨ (¬ p5193) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial39471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory28727 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule39471 (meaning t m 2027) (meaning t m 2241) (meaning t m 2589) (meaning t m 3506) (meaning t m 3842) (meaning t m 4235) (meaning t m 4831) (meaning t m 5193) (meaning t m 5660) source

theorem rule39473 (p2027 p2459 p2534 p2608 p2819 p2829 p3540 p4133 p4186 p5193 : Prop) (h : (¬ p2829) ∨ (¬ p5193) ∨ (¬ p2819) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p4186) ∨ (¬ p2459) ∨ (¬ p3540) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3540) ∨ (¬ p4133) ∨ (¬ p4186) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28729 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39473 (meaning t m 2027) (meaning t m 2459) (meaning t m 2534) (meaning t m 2608) (meaning t m 2819) (meaning t m 2829) (meaning t m 3540) (meaning t m 4133) (meaning t m 4186) (meaning t m 5193) source

theorem rule39476 (p2027 p2528 p3692 p4110 p4355 p4509 : Prop) (h : (¬ p2528) ∨ (¬ p4509) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p4355) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3692) ∨ (¬ p4110) ∨ (¬ p4355) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial39476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory28732 t (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule39476 (meaning t m 2027) (meaning t m 2528) (meaning t m 3692) (meaning t m 4110) (meaning t m 4355) (meaning t m 4509) source

theorem rule39478 (p2027 p2253 p2476 p2946 p3189 p3641 p3662 p3876 p4119 p4311 p4647 p5193 : Prop) (h : (¬ p2476) ∨ (¬ p2253) ∨ (¬ p3876) ∨ (¬ p3189) ∨ (¬ p4311) ∨ (¬ p3641) ∨ (¬ p5193) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p4647) ∨ (¬ p4119)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2476) ∨ (¬ p2946) ∨ (¬ p3189) ∨ (¬ p3641) ∨ (¬ p3662) ∨ (¬ p3876) ∨ (¬ p4119) ∨ (¬ p4311) ∨ (¬ p4647) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28734 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 3 8) (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8)
  exact rule39478 (meaning t m 2027) (meaning t m 2253) (meaning t m 2476) (meaning t m 2946) (meaning t m 3189) (meaning t m 3641) (meaning t m 3662) (meaning t m 3876) (meaning t m 4119) (meaning t m 4311) (meaning t m 4647) (meaning t m 5193) source

theorem rule39481 (p2027 p2534 p3055 p3399 p3707 p3874 p3950 p4381 p4736 p5363 : Prop) (h : (¬ p3055) ∨ (¬ p3399) ∨ (¬ p3707) ∨ (¬ p3950) ∨ (¬ p4381) ∨ (¬ p4736) ∨ (¬ p5363) ∨ (¬ p3874) ∨ (¬ p2534) ∨ p2027) : (p2027) ∨ (¬ p2534) ∨ (¬ p3055) ∨ (¬ p3399) ∨ (¬ p3707) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4381) ∨ (¬ p4736) ∨ (¬ p5363) := by
  classical
  tauto

theorem initial39481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5363)) := by
  have source := ElevenTheory.theory28737 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 1 9) (m.theta 2 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule39481 (meaning t m 2027) (meaning t m 2534) (meaning t m 3055) (meaning t m 3399) (meaning t m 3707) (meaning t m 3874) (meaning t m 3950) (meaning t m 4381) (meaning t m 4736) (meaning t m 5363) source

theorem rule39483 (p2027 p2138 p2241 p2641 p3323 p3692 p3694 p4330 p4736 : Prop) (h : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p4736) ∨ (¬ p3323) ∨ (¬ p3694) ∨ (¬ p3692) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4330) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial39483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory28739 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule39483 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 2641) (meaning t m 3323) (meaning t m 3692) (meaning t m 3694) (meaning t m 4330) (meaning t m 4736) source

theorem rule39484 (p2027 p2177 p2255 p2331 p2474 p2528 p2662 p3309 p3857 p4111 p4319 p4438 : Prop) (h : (¬ p3309) ∨ (¬ p4319) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2177) ∨ (¬ p4438) ∨ p2027 ∨ (¬ p2662) ∨ (¬ p2474) ∨ (¬ p2528) ∨ (¬ p3857) ∨ (¬ p4111)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2474) ∨ (¬ p2528) ∨ (¬ p2662) ∨ (¬ p3309) ∨ (¬ p3857) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial39484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2474)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory28740 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 8) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule39484 (meaning t m 2027) (meaning t m 2177) (meaning t m 2255) (meaning t m 2331) (meaning t m 2474) (meaning t m 2528) (meaning t m 2662) (meaning t m 3309) (meaning t m 3857) (meaning t m 4111) (meaning t m 4319) (meaning t m 4438) source

theorem rule39488 (p2027 p2589 p3690 p3707 p3830 p4235 p4444 p4669 p5193 : Prop) (h : (¬ p3830) ∨ (¬ p3707) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p5193) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3690) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4235) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28744 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 9) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule39488 (meaning t m 2027) (meaning t m 2589) (meaning t m 3690) (meaning t m 3707) (meaning t m 3830) (meaning t m 4235) (meaning t m 4444) (meaning t m 4669) (meaning t m 5193) source

theorem rule39489 (p2027 p2696 p2753 p3005 p3256 p3379 p3817 p4366 p4669 p5216 : Prop) (h : (¬ p3005) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p2696) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) ∨ (¬ p3379) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3379) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28745 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 3) (m.theta 3 8) (m.theta 7 9) (m.theta 8 9)
  exact rule39489 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 3005) (meaning t m 3256) (meaning t m 3379) (meaning t m 3817) (meaning t m 4366) (meaning t m 4669) (meaning t m 5216) source

theorem rule39490 (p2027 p2241 p2641 p3323 p3556 p3570 p4330 p4348 p4524 : Prop) (h : (¬ p3570) ∨ (¬ p4524) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2641) ∨ (¬ p2241) ∨ (¬ p3323) ∨ (¬ p4348) ∨ (¬ p4330)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial39490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory28746 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule39490 (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 3323) (meaning t m 3556) (meaning t m 3570) (meaning t m 4330) (meaning t m 4348) (meaning t m 4524) source

theorem rule39494 (p1987 p2027 p2169 p2553 p3549 p3922 p3956 p4195 : Prop) (h : (¬ p1987) ∨ p2169 ∨ (¬ p4195) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3956) ∨ (¬ p3549) ∨ (¬ p3922)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2553) ∨ (¬ p3549) ∨ (¬ p3922) ∨ (¬ p3956) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial39494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory28750 t (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule39494 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2553) (meaning t m 3549) (meaning t m 3922) (meaning t m 3956) (meaning t m 4195) source

theorem rule39496 (p2027 p2499 p2573 p2663 p2811 p2839 p4257 p5052 : Prop) (h : (¬ p2663) ∨ (¬ p2573) ∨ (¬ p2811) ∨ (¬ p2499) ∨ p2027 ∨ (¬ p5052) ∨ (¬ p4257) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p2811) ∨ (¬ p2839) ∨ (¬ p4257) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial39496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory28752 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 5) (m.theta 4 6)
  exact rule39496 (meaning t m 2027) (meaning t m 2499) (meaning t m 2573) (meaning t m 2663) (meaning t m 2811) (meaning t m 2839) (meaning t m 4257) (meaning t m 5052) source

theorem rule39499 (p1981 p2027 p2202 p2427 p3073 p4169 p4189 p4253 p4347 p4442 : Prop) (h : (¬ p4442) ∨ (¬ p1981) ∨ (¬ p3073) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p4253) ∨ (¬ p4189) ∨ (¬ p4169) ∨ (¬ p2427) ∨ p2202) : (¬ p1981) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p3073) ∨ (¬ p4169) ∨ (¬ p4189) ∨ (¬ p4253) ∨ (¬ p4347) ∨ (¬ p4442) := by
  classical
  tauto

theorem initial39499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 4189)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4442)) := by
  have source := ElevenTheory.theory28755 t (m.theta 1 7) (m.theta 1 8) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 10) (m.theta 8 9)
  exact rule39499 (meaning t m 1981) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 3073) (meaning t m 4169) (meaning t m 4189) (meaning t m 4253) (meaning t m 4347) (meaning t m 4442) source

theorem rule39505 (p2027 p3347 p3365 p3540 p3619 p3644 p3670 p4030 p4752 p5123 p5558 : Prop) (h : (¬ p4030) ∨ (¬ p5123) ∨ (¬ p4752) ∨ (¬ p3540) ∨ (¬ p3670) ∨ (¬ p3347) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p5558) ∨ (¬ p3365) ∨ (¬ p3619)) : (p2027) ∨ (¬ p3347) ∨ (¬ p3365) ∨ (¬ p3540) ∨ (¬ p3619) ∨ (¬ p3644) ∨ (¬ p3670) ∨ (¬ p4030) ∨ (¬ p4752) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial39505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory28761 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule39505 (meaning t m 2027) (meaning t m 3347) (meaning t m 3365) (meaning t m 3540) (meaning t m 3619) (meaning t m 3644) (meaning t m 3670) (meaning t m 4030) (meaning t m 4752) (meaning t m 5123) (meaning t m 5558) source

theorem rule39507 (p1975 p2027 p2253 p2299 p2331 p2699 p3189 p4154 p4378 : Prop) (h : (¬ p2331) ∨ p2699 ∨ (¬ p4154) ∨ (¬ p2253) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p1975) ∨ (¬ p3189) ∨ (¬ p4378)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2299) ∨ (¬ p2331) ∨ (p2699) ∨ (¬ p3189) ∨ (¬ p4154) ∨ (¬ p4378) := by
  classical
  tauto

theorem initial39507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4378)) := by
  have source := ElevenTheory.theory28763 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule39507 (meaning t m 1975) (meaning t m 2027) (meaning t m 2253) (meaning t m 2299) (meaning t m 2331) (meaning t m 2699) (meaning t m 3189) (meaning t m 4154) (meaning t m 4378) source

theorem rule39510 (p2027 p2563 p3204 p3309 p3743 p3880 p4501 p4506 : Prop) (h : (¬ p4506) ∨ (¬ p3743) ∨ (¬ p3204) ∨ (¬ p3309) ∨ (¬ p2563) ∨ (¬ p3880) ∨ (¬ p4501) ∨ p2027) : (p2027) ∨ (¬ p2563) ∨ (¬ p3204) ∨ (¬ p3309) ∨ (¬ p3743) ∨ (¬ p3880) ∨ (¬ p4501) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial39510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory28766 t (m.theta 0 6) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule39510 (meaning t m 2027) (meaning t m 2563) (meaning t m 3204) (meaning t m 3309) (meaning t m 3743) (meaning t m 3880) (meaning t m 4501) (meaning t m 4506) source

theorem rule39518 (p2928 p3742 p4116 : Prop) (h : (¬ p3742) ∨ (¬ p4116) ∨ p2928) : (p2928) ∨ (¬ p3742) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial39518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2928) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory28774 (m.theta 1 4) (m.theta 3 4) (m.theta 4 7)
  exact rule39518 (meaning t m 2928) (meaning t m 3742) (meaning t m 4116) source

theorem rule39521 (p1975 p2027 p2295 p2641 p2765 p3125 p3848 p4190 : Prop) (h : (¬ p4190) ∨ (¬ p2295) ∨ (¬ p3848) ∨ p2765 ∨ (¬ p3125) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (p2765) ∨ (¬ p3125) ∨ (¬ p3848) ∨ (¬ p4190) := by
  classical
  tauto

theorem initial39521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4190)) := by
  have source := ElevenTheory.theory28777 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 9) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule39521 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2641) (meaning t m 2765) (meaning t m 3125) (meaning t m 3848) (meaning t m 4190) source

theorem rule39522 (p1992 p2608 p2699 p4187 p4620 : Prop) (h : p2699 ∨ (¬ p4187) ∨ p4620 ∨ (¬ p1992) ∨ (¬ p2608)) : (¬ p1992) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p4187) ∨ (p4620) := by
  classical
  tauto

theorem initial39522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 4187)) ∨ (meaning t m 4620) := by
  have source := ElevenTheory.theory28778 t (m.theta 0 1) (m.theta 1 2) (m.theta 6 7) (m.theta 6 9)
  exact rule39522 (meaning t m 1992) (meaning t m 2608) (meaning t m 2699) (meaning t m 4187) (meaning t m 4620) source

theorem rule39523 (p2027 p2563 p2992 p3745 p4154 p4702 : Prop) (h : (¬ p4702) ∨ (¬ p2992) ∨ (¬ p2563) ∨ (¬ p3745) ∨ p2027 ∨ (¬ p4154)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4154) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial39523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory28779 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6)
  exact rule39523 (meaning t m 2027) (meaning t m 2563) (meaning t m 2992) (meaning t m 3745) (meaning t m 4154) (meaning t m 4702) source

theorem rule39525 (p2027 p2437 p2440 p3569 p4110 p4558 : Prop) (h : (¬ p4558) ∨ (¬ p2440) ∨ (¬ p2437) ∨ (¬ p3569) ∨ p2027 ∨ (¬ p4110)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p3569) ∨ (¬ p4110) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial39525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory28781 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule39525 (meaning t m 2027) (meaning t m 2437) (meaning t m 2440) (meaning t m 3569) (meaning t m 4110) (meaning t m 4558) source

theorem rule39526 (p2027 p2246 p2476 p2744 p2901 p2946 p3246 p3366 p3641 p3905 p4641 p5160 : Prop) (h : (¬ p2246) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p3641) ∨ (¬ p3366) ∨ (¬ p2476) ∨ (¬ p4641) ∨ (¬ p5160) ∨ (¬ p3905) ∨ (¬ p2901) ∨ (¬ p2744) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2476) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3641) ∨ (¬ p3905) ∨ (¬ p4641) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial39526 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory28782 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule39526 (meaning t m 2027) (meaning t m 2246) (meaning t m 2476) (meaning t m 2744) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3366) (meaning t m 3641) (meaning t m 3905) (meaning t m 4641) (meaning t m 5160) source

theorem rule39529 (p2027 p2246 p2651 p2744 p3016 p3266 p3366 p3564 p3820 p3821 p4330 p4381 : Prop) (h : (¬ p4381) ∨ (¬ p3266) ∨ (¬ p3564) ∨ (¬ p3820) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p4330) ∨ (¬ p2246) ∨ (¬ p3821) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p2651)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3564) ∨ (¬ p3820) ∨ (¬ p3821) ∨ (¬ p4330) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial39529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory28785 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule39529 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2744) (meaning t m 3016) (meaning t m 3266) (meaning t m 3366) (meaning t m 3564) (meaning t m 3820) (meaning t m 3821) (meaning t m 4330) (meaning t m 4381) source

theorem rule39530 (p2027 p2246 p2651 p2744 p3016 p3366 p3551 p3820 p3888 p4348 p4444 p5250 : Prop) (h : (¬ p3820) ∨ (¬ p2246) ∨ (¬ p3551) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p4444) ∨ (¬ p3366) ∨ (¬ p2651) ∨ (¬ p5250) ∨ (¬ p3888) ∨ (¬ p3016)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3366) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p3888) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial39530 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory28786 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule39530 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2744) (meaning t m 3016) (meaning t m 3366) (meaning t m 3551) (meaning t m 3820) (meaning t m 3888) (meaning t m 4348) (meaning t m 4444) (meaning t m 5250) source

theorem rule39531 (p2027 p3572 p4063 p4104 p4391 p4790 : Prop) (h : (¬ p3572) ∨ (¬ p4790) ∨ (¬ p4391) ∨ p2027 ∨ (¬ p4063) ∨ (¬ p4104)) : (p2027) ∨ (¬ p3572) ∨ (¬ p4063) ∨ (¬ p4104) ∨ (¬ p4391) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial39531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4063)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory28787 t (m.theta 0 3) (m.theta 0 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 10)
  exact rule39531 (meaning t m 2027) (meaning t m 3572) (meaning t m 4063) (meaning t m 4104) (meaning t m 4391) (meaning t m 4790) source

theorem rule39533 (p2027 p2246 p2459 p2534 p2946 p3005 p3347 p3540 p4186 p4311 p4315 p4813 p4902 : Prop) (h : (¬ p4813) ∨ (¬ p2246) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p2946) ∨ (¬ p4186) ∨ (¬ p2459) ∨ (¬ p4315) ∨ (¬ p4902) ∨ (¬ p4311) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p4186) ∨ (¬ p4311) ∨ (¬ p4315) ∨ (¬ p4813) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial39533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4813)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory28789 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 4 7) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39533 (meaning t m 2027) (meaning t m 2246) (meaning t m 2459) (meaning t m 2534) (meaning t m 2946) (meaning t m 3005) (meaning t m 3347) (meaning t m 3540) (meaning t m 4186) (meaning t m 4311) (meaning t m 4315) (meaning t m 4813) (meaning t m 4902) source

theorem rule39534 (p2027 p2137 p2220 p2839 p2928 p3055 p3146 p4030 p4278 p4669 p4734 : Prop) (h : (¬ p4030) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p2137) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p4669) ∨ (¬ p4734) ∨ (¬ p2928) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2220) ∨ (¬ p2839) ∨ (¬ p2928) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p4030) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial39534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory28790 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule39534 (meaning t m 2027) (meaning t m 2137) (meaning t m 2220) (meaning t m 2839) (meaning t m 2928) (meaning t m 3055) (meaning t m 3146) (meaning t m 4030) (meaning t m 4278) (meaning t m 4669) (meaning t m 4734) source

theorem rule39535 (p2027 p2651 p3016 p3425 p3564 p3659 p4330 p4348 p4786 : Prop) (h : (¬ p3016) ∨ (¬ p2651) ∨ (¬ p3564) ∨ (¬ p3659) ∨ (¬ p4786) ∨ (¬ p3425) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p4330)) : (p2027) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3425) ∨ (¬ p3564) ∨ (¬ p3659) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial39535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory28791 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule39535 (meaning t m 2027) (meaning t m 2651) (meaning t m 3016) (meaning t m 3425) (meaning t m 3564) (meaning t m 3659) (meaning t m 4330) (meaning t m 4348) (meaning t m 4786) source

theorem rule39541 (p2027 p2696 p2797 p3817 p4228 p4366 p4381 p4733 p5250 : Prop) (h : (¬ p4366) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3817) ∨ (¬ p4381) ∨ (¬ p2797) ∨ (¬ p4228) ∨ (¬ p5250)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3817) ∨ (¬ p4228) ∨ (¬ p4366) ∨ (¬ p4381) ∨ (¬ p4733) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial39541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory28797 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule39541 (meaning t m 2027) (meaning t m 2696) (meaning t m 2797) (meaning t m 3817) (meaning t m 4228) (meaning t m 4366) (meaning t m 4381) (meaning t m 4733) (meaning t m 5250) source

theorem rule39546 (p1975 p2027 p2202 p2518 p2553 p3238 p3422 p3874 : Prop) (h : p2027 ∨ (¬ p3422) ∨ (¬ p2553) ∨ (¬ p3238) ∨ (¬ p1975) ∨ p2202 ∨ (¬ p2518) ∨ (¬ p3874)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2518) ∨ (¬ p2553) ∨ (¬ p3238) ∨ (¬ p3422) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial39546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory28802 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule39546 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2518) (meaning t m 2553) (meaning t m 3238) (meaning t m 3422) (meaning t m 3874) source

theorem rule39547 (p2027 p2247 p2608 p2707 p2742 p4782 : Prop) (h : (¬ p2742) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p4782) ∨ (¬ p2707)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2742) ∨ (¬ p4782) := by
  classical
  tauto

theorem initial39547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 4782)) := by
  have source := ElevenTheory.theory28803 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7)
  exact rule39547 (meaning t m 2027) (meaning t m 2247) (meaning t m 2608) (meaning t m 2707) (meaning t m 2742) (meaning t m 4782) source

theorem rule39550 (p2027 p2685 p2810 p3574 p3579 p4711 : Prop) (h : (¬ p3579) ∨ (¬ p2685) ∨ (¬ p4711) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3574) ∨ (¬ p3579) ∨ (¬ p4711) := by
  classical
  tauto

theorem initial39550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4711)) := by
  have source := ElevenTheory.theory28806 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7)
  exact rule39550 (meaning t m 2027) (meaning t m 2685) (meaning t m 2810) (meaning t m 3574) (meaning t m 3579) (meaning t m 4711) source

theorem rule39552 (p3115 p3879 p4948 : Prop) (h : (¬ p3115) ∨ (¬ p3879) ∨ (¬ p4948)) : (¬ p3115) ∨ (¬ p3879) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial39552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory28808 (m.theta 3 5) (m.theta 4 5) (m.theta 5 9)
  exact rule39552 (meaning t m 3115) (meaning t m 3879) (meaning t m 4948) source

theorem rule39556 (p3767 p4321 p5487 : Prop) (h : (¬ p5487) ∨ (¬ p4321) ∨ (¬ p3767)) : (¬ p3767) ∨ (¬ p4321) ∨ (¬ p5487) := by
  classical
  tauto

theorem initial39556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5487)) := by
  have source := ElevenTheory.theory28812 (m.theta 0 9) (m.theta 1 9) (m.theta 9 10)
  exact rule39556 (meaning t m 3767) (meaning t m 4321) (meaning t m 5487) source

theorem rule39558 (p2027 p2753 p3379 p3619 p3670 p3817 p4366 p4444 p4669 p5216 : Prop) (h : (¬ p4366) ∨ (¬ p4669) ∨ (¬ p3379) ∨ (¬ p3817) ∨ (¬ p3619) ∨ (¬ p5216) ∨ (¬ p3670) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3619) ∨ (¬ p3670) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28814 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule39558 (meaning t m 2027) (meaning t m 2753) (meaning t m 3379) (meaning t m 3619) (meaning t m 3670) (meaning t m 3817) (meaning t m 4366) (meaning t m 4444) (meaning t m 4669) (meaning t m 5216) source

theorem rule39560 (p2027 p2248 p2651 p3016 p3486 p3555 p3564 p3690 p4621 : Prop) (h : (¬ p3690) ∨ (¬ p3555) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3564) ∨ (¬ p4621)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3564) ∨ (¬ p3690) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial39560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory28816 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule39560 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 3016) (meaning t m 3486) (meaning t m 3555) (meaning t m 3564) (meaning t m 3690) (meaning t m 4621) source

theorem rule39561 (p2027 p3038 p3631 p3662 p3947 p4112 p4701 : Prop) (h : p2027 ∨ (¬ p4112) ∨ (¬ p3038) ∨ (¬ p3662) ∨ (¬ p3631) ∨ (¬ p4701) ∨ (¬ p3947)) : (p2027) ∨ (¬ p3038) ∨ (¬ p3631) ∨ (¬ p3662) ∨ (¬ p3947) ∨ (¬ p4112) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial39561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory28817 t (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7) (m.theta 7 9)
  exact rule39561 (meaning t m 2027) (meaning t m 3038) (meaning t m 3631) (meaning t m 3662) (meaning t m 3947) (meaning t m 4112) (meaning t m 4701) source

theorem rule39563 (p2027 p2156 p2459 p2619 p3758 p3860 p4261 p4521 p4902 : Prop) (h : (¬ p4521) ∨ (¬ p4902) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p3860) ∨ (¬ p2619) ∨ (¬ p4261) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2459) ∨ (¬ p2619) ∨ (¬ p3758) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4521) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial39563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory28819 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 8) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39563 (meaning t m 2027) (meaning t m 2156) (meaning t m 2459) (meaning t m 2619) (meaning t m 3758) (meaning t m 3860) (meaning t m 4261) (meaning t m 4521) (meaning t m 4902) source

theorem rule39564 (p2027 p3073 p3692 p4173 p4496 p4509 : Prop) (h : (¬ p3692) ∨ (¬ p3073) ∨ (¬ p4509) ∨ (¬ p4496) ∨ p2027 ∨ (¬ p4173)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4173) ∨ (¬ p4496) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial39564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4496)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory28820 t (m.theta 1 5) (m.theta 1 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule39564 (meaning t m 2027) (meaning t m 3073) (meaning t m 3692) (meaning t m 4173) (meaning t m 4496) (meaning t m 4509) source

theorem rule39568 (p2027 p3542 p3830 p3860 p4330 p4348 p5152 : Prop) (h : (¬ p5152) ∨ (¬ p4330) ∨ (¬ p3830) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p3542) ∨ (¬ p3860)) : (p2027) ∨ (¬ p3542) ∨ (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial39568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3542)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory28824 t (m.theta 0 1) (m.theta 1 8) (m.theta 1 9) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule39568 (meaning t m 2027) (meaning t m 3542) (meaning t m 3830) (meaning t m 3860) (meaning t m 4330) (meaning t m 4348) (meaning t m 5152) source

theorem rule39570 (p2027 p2098 p2499 p3452 p3609 p3692 p3956 p4433 p4733 : Prop) (h : (¬ p2098) ∨ (¬ p4733) ∨ (¬ p3609) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p3452) ∨ (¬ p2499)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial39570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory28826 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule39570 (meaning t m 2027) (meaning t m 2098) (meaning t m 2499) (meaning t m 3452) (meaning t m 3609) (meaning t m 3692) (meaning t m 3956) (meaning t m 4433) (meaning t m 4733) source

theorem rule39573 (p2027 p2313 p2553 p2696 p2753 p3136 p3156 p3204 p3956 p4433 p4870 : Prop) (h : (¬ p2553) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p3956) ∨ (¬ p2696) ∨ (¬ p4433) ∨ (¬ p3204) ∨ (¬ p3156) ∨ (¬ p4870) ∨ (¬ p2753) ∨ (¬ p3136)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3204) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial39573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory28829 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule39573 (meaning t m 2027) (meaning t m 2313) (meaning t m 2553) (meaning t m 2696) (meaning t m 2753) (meaning t m 3136) (meaning t m 3156) (meaning t m 3204) (meaning t m 3956) (meaning t m 4433) (meaning t m 4870) source

theorem rule39577 (p2027 p2098 p2753 p2927 p3266 p3379 p3609 p4366 p4831 p5216 p5503 : Prop) (h : (¬ p2753) ∨ (¬ p5216) ∨ (¬ p3609) ∨ p2027 ∨ (¬ p2098) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p5503) ∨ (¬ p3266) ∨ (¬ p4831)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2753) ∨ (¬ p2927) ∨ (¬ p3266) ∨ (¬ p3379) ∨ (¬ p3609) ∨ (¬ p4366) ∨ (¬ p4831) ∨ (¬ p5216) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial39577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory28833 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 8) (m.theta 4 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule39577 (meaning t m 2027) (meaning t m 2098) (meaning t m 2753) (meaning t m 2927) (meaning t m 3266) (meaning t m 3379) (meaning t m 3609) (meaning t m 4366) (meaning t m 4831) (meaning t m 5216) (meaning t m 5503) source

theorem rule39578 (p2001 p2027 p2323 p2331 p3136 p3156 p4195 : Prop) (h : p2323 ∨ p2027 ∨ (¬ p4195) ∨ (¬ p2331) ∨ (¬ p3156) ∨ (¬ p2001) ∨ (¬ p3136)) : (¬ p2001) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial39578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory28834 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8)
  exact rule39578 (meaning t m 2001) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 3136) (meaning t m 3156) (meaning t m 4195) source

theorem rule39582 (p2470 p3222 p3358 p3519 : Prop) (h : (¬ p3519) ∨ (¬ p3358) ∨ (¬ p2470) ∨ p3222) : (¬ p2470) ∨ (p3222) ∨ (¬ p3358) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial39582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (meaning t m 3222) ∨ (¬ (meaning t m 3358)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory28838 (m.theta 0 4) (m.theta 1 4) (m.theta 4 8) (m.theta 4 9)
  exact rule39582 (meaning t m 2470) (meaning t m 3222) (meaning t m 3358) (meaning t m 3519) source

theorem rule39583 (p2470 p3641 p3759 : Prop) (h : (¬ p3759) ∨ (¬ p2470) ∨ p3641) : (¬ p2470) ∨ (p3641) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial39583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (meaning t m 3641) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory28839 (m.theta 0 4) (m.theta 2 4) (m.theta 4 8)
  exact rule39583 (meaning t m 2470) (meaning t m 3641) (meaning t m 3759) source

theorem rule39584 (p2027 p2299 p2341 p3246 p3821 p4559 : Prop) (h : (¬ p2341) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p4559) ∨ (¬ p2299) ∨ (¬ p3821)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial39584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory28840 t (m.theta 0 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39584 (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 3246) (meaning t m 3821) (meaning t m 4559) source

theorem rule39586 (p2027 p2138 p2449 p2737 p2807 p2811 p3692 p3694 p3950 p4734 : Prop) (h : (¬ p3694) ∨ (¬ p2811) ∨ (¬ p2737) ∨ (¬ p2138) ∨ (¬ p2807) ∨ (¬ p4734) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2449) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial39586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory28842 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule39586 (meaning t m 2027) (meaning t m 2138) (meaning t m 2449) (meaning t m 2737) (meaning t m 2807) (meaning t m 2811) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) (meaning t m 4734) source

theorem rule39589 (p2098 p3619 p5344 : Prop) (h : (¬ p5344) ∨ (¬ p2098) ∨ p3619) : (¬ p2098) ∨ (p3619) ∨ (¬ p5344) := by
  classical
  tauto

theorem initial39589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2098)) ∨ (meaning t m 3619) ∨ (¬ (meaning t m 5344)) := by
  have source := ElevenTheory.theory28845 (m.theta 0 2) (m.theta 2 8) (m.theta 2 9)
  exact rule39589 (meaning t m 2098) (meaning t m 3619) (meaning t m 5344) source

theorem rule39590 (p2027 p2696 p2753 p2927 p3115 p3136 p3379 p4278 p4366 p4395 p5216 : Prop) (h : (¬ p4278) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p5216) ∨ (¬ p3136) ∨ (¬ p2753) ∨ (¬ p4395) ∨ (¬ p2696) ∨ (¬ p2927) ∨ (¬ p4366) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2927) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3379) ∨ (¬ p4278) ∨ (¬ p4366) ∨ (¬ p4395) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28846 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 3) (m.theta 3 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 9)
  exact rule39590 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 2927) (meaning t m 3115) (meaning t m 3136) (meaning t m 3379) (meaning t m 4278) (meaning t m 4366) (meaning t m 4395) (meaning t m 5216) source

theorem rule39591 (p2027 p2662 p2717 p3551 p4195 p4336 p4701 p4781 p5197 : Prop) (h : (¬ p5197) ∨ (¬ p2717) ∨ (¬ p2662) ∨ p2027 ∨ (¬ p4336) ∨ (¬ p4701) ∨ (¬ p4781) ∨ (¬ p4195) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2662) ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p4195) ∨ (¬ p4336) ∨ (¬ p4701) ∨ (¬ p4781) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial39591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4701)) ∨ (¬ (meaning t m 4781)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory28847 t (m.theta 0 4) (m.theta 0 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 7 8)
  exact rule39591 (meaning t m 2027) (meaning t m 2662) (meaning t m 2717) (meaning t m 3551) (meaning t m 4195) (meaning t m 4336) (meaning t m 4701) (meaning t m 4781) (meaning t m 5197) source

theorem rule39594 (p1979 p2027 p2169 p2387 p3136 p3654 p4035 p4190 : Prop) (h : (¬ p4035) ∨ (¬ p3136) ∨ (¬ p1979) ∨ p2027 ∨ p2169 ∨ (¬ p4190) ∨ (¬ p2387) ∨ (¬ p3654)) : (¬ p1979) ∨ (p2027) ∨ (p2169) ∨ (¬ p2387) ∨ (¬ p3136) ∨ (¬ p3654) ∨ (¬ p4035) ∨ (¬ p4190) := by
  classical
  tauto

theorem initial39594 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4190)) := by
  have source := ElevenTheory.theory28850 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 6 8) (m.theta 6 9)
  exact rule39594 (meaning t m 1979) (meaning t m 2027) (meaning t m 2169) (meaning t m 2387) (meaning t m 3136) (meaning t m 3654) (meaning t m 4035) (meaning t m 4190) source

theorem rule39601 (p3644 p3945 p4278 : Prop) (h : (¬ p3945) ∨ (¬ p4278) ∨ p3644) : (p3644) ∨ (¬ p3945) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial39601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3644) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory28857 (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39601 (meaning t m 3644) (meaning t m 3945) (meaning t m 4278) source

theorem rule39602 (p1995 p2027 p2187 p2765 p3379 p3591 p3923 : Prop) (h : (¬ p3923) ∨ (¬ p1995) ∨ p2027 ∨ (¬ p3379) ∨ p2765 ∨ (¬ p3591) ∨ (¬ p2187)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2187) ∨ (p2765) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial39602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory28858 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 5 6) (m.theta 6 8)
  exact rule39602 (meaning t m 1995) (meaning t m 2027) (meaning t m 2187) (meaning t m 2765) (meaning t m 3379) (meaning t m 3591) (meaning t m 3923) source

theorem rule39603 (p1987 p2027 p2651 p2765 p2810 p2952 p3952 : Prop) (h : p2765 ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3952) ∨ (¬ p1987) ∨ (¬ p2952)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2651) ∨ (p2765) ∨ (¬ p2810) ∨ (¬ p2952) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial39603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory28859 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule39603 (meaning t m 1987) (meaning t m 2027) (meaning t m 2651) (meaning t m 2765) (meaning t m 2810) (meaning t m 2952) (meaning t m 3952) source

theorem rule39607 (p2027 p2563 p2667 p3136 p3957 p4195 p4702 p5016 : Prop) (h : (¬ p5016) ∨ (¬ p2667) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p2563) ∨ (¬ p4195) ∨ (¬ p4702) ∨ (¬ p3957)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2667) ∨ (¬ p3136) ∨ (¬ p3957) ∨ (¬ p4195) ∨ (¬ p4702) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial39607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4702)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory28863 t (m.theta 0 6) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6)
  exact rule39607 (meaning t m 2027) (meaning t m 2563) (meaning t m 2667) (meaning t m 3136) (meaning t m 3957) (meaning t m 4195) (meaning t m 4702) (meaning t m 5016) source

theorem rule39610 (p2027 p2098 p2928 p3452 p3609 p3644 p3692 p4733 p4902 : Prop) (h : (¬ p4902) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p2928) ∨ (¬ p3692) ∨ (¬ p3644) ∨ (¬ p2098) ∨ (¬ p3452) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3644) ∨ (¬ p3692) ∨ (¬ p4733) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial39610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory28866 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 8) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39610 (meaning t m 2027) (meaning t m 2098) (meaning t m 2928) (meaning t m 3452) (meaning t m 3609) (meaning t m 3644) (meaning t m 3692) (meaning t m 4733) (meaning t m 4902) source

theorem rule39611 (p1988 p2027 p2122 p2396 p2761 p2765 p2774 p3238 p3452 p4110 p4733 : Prop) (h : (¬ p4733) ∨ (¬ p4110) ∨ p2765 ∨ (¬ p3452) ∨ (¬ p3238) ∨ (¬ p1988) ∨ (¬ p2761) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2122)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (p2765) ∨ (¬ p2774) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4110) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial39611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory28867 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule39611 (meaning t m 1988) (meaning t m 2027) (meaning t m 2122) (meaning t m 2396) (meaning t m 2761) (meaning t m 2765) (meaning t m 2774) (meaning t m 3238) (meaning t m 3452) (meaning t m 4110) (meaning t m 4733) source

theorem rule39616 (p2027 p2753 p3379 p3591 p3619 p3670 p4026 p4444 p4604 p5216 : Prop) (h : (¬ p4604) ∨ (¬ p4026) ∨ (¬ p3591) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p3670) ∨ (¬ p3379) ∨ (¬ p3619) ∨ (¬ p2753) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3619) ∨ (¬ p3670) ∨ (¬ p4026) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28872 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule39616 (meaning t m 2027) (meaning t m 2753) (meaning t m 3379) (meaning t m 3591) (meaning t m 3619) (meaning t m 3670) (meaning t m 4026) (meaning t m 4444) (meaning t m 4604) (meaning t m 5216) source

theorem rule39620 (p2027 p2788 p3998 p4114 p4358 p5580 : Prop) (h : (¬ p5580) ∨ (¬ p4114) ∨ (¬ p2788) ∨ (¬ p4358) ∨ p2027 ∨ (¬ p3998)) : (p2027) ∨ (¬ p2788) ∨ (¬ p3998) ∨ (¬ p4114) ∨ (¬ p4358) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial39620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2788)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory28876 t (m.theta 0 6) (m.theta 0 8) (m.theta 2 6) (m.theta 6 8) (m.theta 8 10)
  exact rule39620 (meaning t m 2027) (meaning t m 2788) (meaning t m 3998) (meaning t m 4114) (meaning t m 4358) (meaning t m 5580) source

theorem rule39622 (p2027 p2137 p2748 p2839 p2996 p3051 p3246 p3365 p3553 p4668 p4734 : Prop) (h : (¬ p2748) ∨ (¬ p3051) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p2137) ∨ (¬ p3246) ∨ (¬ p2839) ∨ (¬ p4668)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p2996) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p4668) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial39622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory28878 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39622 (meaning t m 2027) (meaning t m 2137) (meaning t m 2748) (meaning t m 2839) (meaning t m 2996) (meaning t m 3051) (meaning t m 3246) (meaning t m 3365) (meaning t m 3553) (meaning t m 4668) (meaning t m 4734) source

theorem rule39623 (p2027 p3324 p3998 p4114 p4584 p5580 : Prop) (h : (¬ p5580) ∨ (¬ p4114) ∨ (¬ p3998) ∨ (¬ p4584) ∨ p2027 ∨ (¬ p3324)) : (p2027) ∨ (¬ p3324) ∨ (¬ p3998) ∨ (¬ p4114) ∨ (¬ p4584) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial39623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4584)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory28879 t (m.theta 0 6) (m.theta 0 8) (m.theta 3 6) (m.theta 6 8) (m.theta 8 10)
  exact rule39623 (meaning t m 2027) (meaning t m 3324) (meaning t m 3998) (meaning t m 4114) (meaning t m 4584) (meaning t m 5580) source

theorem rule39625 (p1994 p2027 p2143 p2427 p2630 p2765 p3556 p4110 p4392 : Prop) (h : (¬ p1994) ∨ p2027 ∨ p2765 ∨ (¬ p2630) ∨ (¬ p2143) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p4110) ∨ (¬ p4392)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2143) ∨ (¬ p2427) ∨ (¬ p2630) ∨ (p2765) ∨ (¬ p3556) ∨ (¬ p4110) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial39625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory28881 t (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule39625 (meaning t m 1994) (meaning t m 2027) (meaning t m 2143) (meaning t m 2427) (meaning t m 2630) (meaning t m 2765) (meaning t m 3556) (meaning t m 4110) (meaning t m 4392) source

theorem rule39626 (p2027 p2662 p2891 p3556 p3904 p4154 p4365 p4972 : Prop) (h : (¬ p2662) ∨ (¬ p4154) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p3904) ∨ (¬ p3556) ∨ (¬ p4365) ∨ (¬ p4972)) : (p2027) ∨ (¬ p2662) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4154) ∨ (¬ p4365) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial39626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory28882 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 6) (m.theta 5 7)
  exact rule39626 (meaning t m 2027) (meaning t m 2662) (meaning t m 2891) (meaning t m 3556) (meaning t m 3904) (meaning t m 4154) (meaning t m 4365) (meaning t m 4972) source

theorem rule39628 (p2027 p2166 p2662 p3904 p4120 p4154 p4365 p4972 : Prop) (h : (¬ p2662) ∨ (¬ p4154) ∨ (¬ p3904) ∨ (¬ p2166) ∨ (¬ p4365) ∨ p2027 ∨ (¬ p4120) ∨ (¬ p4972)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2662) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p4154) ∨ (¬ p4365) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial39628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory28884 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 6) (m.theta 5 8)
  exact rule39628 (meaning t m 2027) (meaning t m 2166) (meaning t m 2662) (meaning t m 3904) (meaning t m 4120) (meaning t m 4154) (meaning t m 4365) (meaning t m 4972) source

theorem rule39630 (p1994 p2027 p2417 p2630 p2914 p3361 p3414 p3947 : Prop) (h : (¬ p1994) ∨ (¬ p3361) ∨ (¬ p2630) ∨ (¬ p3414) ∨ (¬ p2417) ∨ p2914 ∨ p2027 ∨ (¬ p3947)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2630) ∨ (p2914) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial39630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory28886 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule39630 (meaning t m 1994) (meaning t m 2027) (meaning t m 2417) (meaning t m 2630) (meaning t m 2914) (meaning t m 3361) (meaning t m 3414) (meaning t m 3947) source

theorem rule39632 (p2027 p2138 p2246 p2331 p2744 p3323 p3366 p3461 p3694 p5123 p5568 : Prop) (h : (¬ p2246) ∨ (¬ p3694) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p3323) ∨ (¬ p2331) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p5123) ∨ (¬ p5568)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2744) ∨ (¬ p3323) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p3694) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial39632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory28888 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule39632 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2331) (meaning t m 2744) (meaning t m 3323) (meaning t m 3366) (meaning t m 3461) (meaning t m 3694) (meaning t m 5123) (meaning t m 5568) source

theorem rule39633 (p2027 p2104 p2248 p2264 p2299 p2331 p3537 p3588 p3873 p4156 p4477 : Prop) (h : (¬ p2104) ∨ (¬ p2248) ∨ (¬ p4477) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4156) ∨ (¬ p3873) ∨ (¬ p3588) ∨ (¬ p3537)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2331) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4156) ∨ (¬ p4477) := by
  classical
  tauto

theorem initial39633 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4477)) := by
  have source := ElevenTheory.theory28889 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule39633 (meaning t m 2027) (meaning t m 2104) (meaning t m 2248) (meaning t m 2264) (meaning t m 2299) (meaning t m 2331) (meaning t m 3537) (meaning t m 3588) (meaning t m 3873) (meaning t m 4156) (meaning t m 4477) source

theorem rule39634 (p2027 p2247 p2744 p3093 p3319 p3366 p3540 p3644 p3905 p4330 p4348 : Prop) (h : (¬ p3319) ∨ (¬ p4330) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p3644) ∨ (¬ p3540) ∨ (¬ p3905) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3366) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3905) ∨ (¬ p4330) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial39634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory28890 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule39634 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3093) (meaning t m 3319) (meaning t m 3366) (meaning t m 3540) (meaning t m 3644) (meaning t m 3905) (meaning t m 4330) (meaning t m 4348) source

theorem rule39636 (p2027 p2247 p2534 p2744 p3055 p3093 p3319 p3366 p3874 p4330 : Prop) (h : p2027 ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p3055) ∨ (¬ p3319) ∨ (¬ p3093) ∨ (¬ p2534) ∨ (¬ p3366) ∨ (¬ p4330) ∨ (¬ p3874)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2534) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3366) ∨ (¬ p3874) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial39636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory28892 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9)
  exact rule39636 (meaning t m 2027) (meaning t m 2247) (meaning t m 2534) (meaning t m 2744) (meaning t m 3055) (meaning t m 3093) (meaning t m 3319) (meaning t m 3366) (meaning t m 3874) (meaning t m 4330) source

theorem rule39638 (p2027 p2313 p2696 p2753 p3115 p3136 p3204 p3644 p4348 p4450 p4710 p4870 : Prop) (h : (¬ p2753) ∨ (¬ p2696) ∨ (¬ p3644) ∨ (¬ p4710) ∨ (¬ p4870) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p4348) ∨ (¬ p3204) ∨ (¬ p4450) ∨ (¬ p3136) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3204) ∨ (¬ p3644) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p4710) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial39638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory28894 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 4 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule39638 (meaning t m 2027) (meaning t m 2313) (meaning t m 2696) (meaning t m 2753) (meaning t m 3115) (meaning t m 3136) (meaning t m 3204) (meaning t m 3644) (meaning t m 4348) (meaning t m 4450) (meaning t m 4710) (meaning t m 4870) source

theorem rule39639 (p2027 p2210 p2247 p2589 p2744 p2850 p2891 p3096 p3366 p3584 p3905 p4558 : Prop) (h : (¬ p3096) ∨ (¬ p2850) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p4558) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2589) ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p3584)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p2850) ∨ (¬ p2891) ∨ (¬ p3096) ∨ (¬ p3366) ∨ (¬ p3584) ∨ (¬ p3905) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial39639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory28895 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule39639 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2589) (meaning t m 2744) (meaning t m 2850) (meaning t m 2891) (meaning t m 3096) (meaning t m 3366) (meaning t m 3584) (meaning t m 3905) (meaning t m 4558) source

theorem rule39643 (p2027 p2373 p2850 p3096 p3584 p4509 : Prop) (h : p2027 ∨ (¬ p2373) ∨ (¬ p3096) ∨ (¬ p4509) ∨ (¬ p3584) ∨ (¬ p2850)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3584) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial39643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory28899 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8)
  exact rule39643 (meaning t m 2027) (meaning t m 2373) (meaning t m 2850) (meaning t m 3096) (meaning t m 3584) (meaning t m 4509) source

theorem rule39655 (p2027 p2122 p2132 p2396 p2753 p3379 p3860 p3950 p3985 p4261 p5216 : Prop) (h : (¬ p2132) ∨ (¬ p3985) ∨ (¬ p3379) ∨ (¬ p2122) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p2753) ∨ (¬ p2396) ∨ (¬ p3950) ∨ (¬ p3860)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2132) ∨ (¬ p2396) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p3985) ∨ (¬ p4261) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28911 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 5) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule39655 (meaning t m 2027) (meaning t m 2122) (meaning t m 2132) (meaning t m 2396) (meaning t m 2753) (meaning t m 3379) (meaning t m 3860) (meaning t m 3950) (meaning t m 3985) (meaning t m 4261) (meaning t m 5216) source

theorem rule39657 (p2027 p2247 p2476 p2744 p3366 p3399 p3631 p3641 p3905 p4641 p5160 : Prop) (h : (¬ p3366) ∨ (¬ p2476) ∨ (¬ p3641) ∨ (¬ p3905) ∨ (¬ p4641) ∨ (¬ p2744) ∨ (¬ p3399) ∨ (¬ p2247) ∨ (¬ p3631) ∨ p2027 ∨ (¬ p5160)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2476) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3641) ∨ (¬ p3905) ∨ (¬ p4641) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial39657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory28913 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 4) (m.theta 4 8) (m.theta 4 9) (m.theta 7 9)
  exact rule39657 (meaning t m 2027) (meaning t m 2247) (meaning t m 2476) (meaning t m 2744) (meaning t m 3366) (meaning t m 3399) (meaning t m 3631) (meaning t m 3641) (meaning t m 3905) (meaning t m 4641) (meaning t m 5160) source

theorem rule39666 (p2476 p3759 p3874 : Prop) (h : (¬ p3759) ∨ (¬ p3874) ∨ p2476) : (p2476) ∨ (¬ p3759) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial39666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2476) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory28922 (m.theta 0 4) (m.theta 2 4) (m.theta 4 8)
  exact rule39666 (meaning t m 2476) (meaning t m 3759) (meaning t m 3874) source

theorem rule39667 (p2027 p2122 p2177 p2753 p2774 p3379 p3690 p4366 p4666 p4909 p5216 : Prop) (h : (¬ p2753) ∨ (¬ p3379) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p4666) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p4909) ∨ (¬ p4366) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3379) ∨ (¬ p3690) ∨ (¬ p4366) ∨ (¬ p4666) ∨ (¬ p4909) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4909)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28923 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39667 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2753) (meaning t m 2774) (meaning t m 3379) (meaning t m 3690) (meaning t m 4366) (meaning t m 4666) (meaning t m 4909) (meaning t m 5216) source

theorem rule39668 (p2027 p2122 p2177 p2753 p2774 p3379 p4366 p4442 p5216 p5559 : Prop) (h : (¬ p2177) ∨ (¬ p5559) ∨ (¬ p2122) ∨ (¬ p5216) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p4442)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p4442) ∨ (¬ p5216) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial39668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4442)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory28924 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 6) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule39668 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2753) (meaning t m 2774) (meaning t m 3379) (meaning t m 4366) (meaning t m 4442) (meaning t m 5216) (meaning t m 5559) source

theorem rule39669 (p2027 p2122 p2177 p2753 p2774 p3379 p3817 p4366 p4666 p5216 : Prop) (h : (¬ p2753) ∨ (¬ p3379) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p4666) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p2177) ∨ (¬ p3817)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3379) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4666) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28925 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39669 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2753) (meaning t m 2774) (meaning t m 3379) (meaning t m 3817) (meaning t m 4366) (meaning t m 4666) (meaning t m 5216) source

theorem rule39670 (p3453 p4257 p4436 : Prop) (h : (¬ p3453) ∨ (¬ p4257) ∨ p4436) : (¬ p3453) ∨ (¬ p4257) ∨ (p4436) := by
  classical
  tauto

theorem initial39670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3453)) ∨ (¬ (meaning t m 4257)) ∨ (meaning t m 4436) := by
  have source := ElevenTheory.theory28926 (m.theta 1 2) (m.theta 1 4) (m.theta 1 8)
  exact rule39670 (meaning t m 3453) (meaning t m 4257) (meaning t m 4436) source

theorem rule39676 (p1998 p2027 p2202 p2264 p2427 p3246 p3947 : Prop) (h : p2202 ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p1998) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p3947)) : (¬ p1998) ∨ (p2027) ∨ (p2202) ∨ (¬ p2264) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial39676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory28932 t (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39676 (meaning t m 1998) (meaning t m 2027) (meaning t m 2202) (meaning t m 2264) (meaning t m 2427) (meaning t m 3246) (meaning t m 3947) source

theorem rule39678 (p2027 p2177 p2295 p2331 p3333 p3346 p3874 p3905 p4438 p4786 : Prop) (h : (¬ p3905) ∨ (¬ p2331) ∨ (¬ p2177) ∨ (¬ p4438) ∨ (¬ p3874) ∨ (¬ p2295) ∨ (¬ p4786) ∨ (¬ p3346) ∨ (¬ p3333) ∨ p2027) : (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3333) ∨ (¬ p3346) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4438) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial39678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory28934 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 4 9) (m.theta 6 7) (m.theta 7 8)
  exact rule39678 (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 2331) (meaning t m 3333) (meaning t m 3346) (meaning t m 3874) (meaning t m 3905) (meaning t m 4438) (meaning t m 4786) source

theorem rule39680 (p2027 p2901 p2946 p3055 p4129 p4425 p4786 p4826 p5160 : Prop) (h : (¬ p4425) ∨ (¬ p4786) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p5160) ∨ (¬ p4826) ∨ (¬ p2946) ∨ (¬ p4129) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4786) ∨ (¬ p4826) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial39680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory28936 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule39680 (meaning t m 2027) (meaning t m 2901) (meaning t m 2946) (meaning t m 3055) (meaning t m 4129) (meaning t m 4425) (meaning t m 4786) (meaning t m 4826) (meaning t m 5160) source

theorem rule39697 (p2027 p2247 p2744 p3093 p3319 p3366 p3425 p3659 p4330 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p3093) ∨ (¬ p3425) ∨ (¬ p2247) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p3319) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4330) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial39697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory28953 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule39697 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3093) (meaning t m 3319) (meaning t m 3366) (meaning t m 3425) (meaning t m 3659) (meaning t m 4330) (meaning t m 4348) source

theorem rule39699 (p2027 p2192 p3105 p3266 p3346 p3347 p3371 p3758 p4425 p4450 p5216 : Prop) (h : (¬ p3371) ∨ (¬ p3758) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p2192) ∨ (¬ p4425) ∨ (¬ p3346) ∨ (¬ p4450) ∨ (¬ p3347) ∨ (¬ p3105)) : (p2027) ∨ (¬ p2192) ∨ (¬ p3105) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3347) ∨ (¬ p3371) ∨ (¬ p3758) ∨ (¬ p4425) ∨ (¬ p4450) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28955 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 5) (m.theta 4 9) (m.theta 5 6) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule39699 (meaning t m 2027) (meaning t m 2192) (meaning t m 3105) (meaning t m 3266) (meaning t m 3346) (meaning t m 3347) (meaning t m 3371) (meaning t m 3758) (meaning t m 4425) (meaning t m 4450) (meaning t m 5216) source

theorem rule39700 (p2027 p2696 p2753 p2797 p3323 p3379 p3860 p4261 p4330 p5216 : Prop) (h : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p3860) ∨ (¬ p3379) ∨ (¬ p5216) ∨ (¬ p3323) ∨ (¬ p4330) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4330) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28956 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 8 9)
  exact rule39700 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 2797) (meaning t m 3323) (meaning t m 3379) (meaning t m 3860) (meaning t m 4261) (meaning t m 4330) (meaning t m 5216) source

theorem rule39702 (p2027 p2331 p2753 p3379 p3506 p3860 p4117 p4191 p4261 p4330 p4421 p5216 : Prop) (h : (¬ p3860) ∨ (¬ p4421) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p4330) ∨ (¬ p4261) ∨ (¬ p4117) ∨ (¬ p3506) ∨ (¬ p5216) ∨ (¬ p2753) ∨ (¬ p3379)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3506) ∨ (¬ p3860) ∨ (¬ p4117) ∨ (¬ p4191) ∨ (¬ p4261) ∨ (¬ p4330) ∨ (¬ p4421) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28958 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule39702 (meaning t m 2027) (meaning t m 2331) (meaning t m 2753) (meaning t m 3379) (meaning t m 3506) (meaning t m 3860) (meaning t m 4117) (meaning t m 4191) (meaning t m 4261) (meaning t m 4330) (meaning t m 4421) (meaning t m 5216) source

theorem rule39706 (p2027 p2230 p2299 p2531 p3549 p3591 p3641 p3684 p4902 p5190 : Prop) (h : (¬ p2299) ∨ (¬ p3684) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3591) ∨ (¬ p5190) ∨ (¬ p3549) ∨ (¬ p4902) ∨ (¬ p2531) ∨ (¬ p3641)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2531) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4902) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial39706 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory28962 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule39706 (meaning t m 2027) (meaning t m 2230) (meaning t m 2299) (meaning t m 2531) (meaning t m 3549) (meaning t m 3591) (meaning t m 3641) (meaning t m 3684) (meaning t m 4902) (meaning t m 5190) source

theorem rule39707 (p2027 p2247 p2352 p2363 p2573 p3662 p4208 p5059 p5190 : Prop) (h : p2027 ∨ (¬ p2573) ∨ (¬ p2363) ∨ (¬ p5059) ∨ (¬ p5190) ∨ (¬ p2247) ∨ (¬ p2352) ∨ (¬ p3662) ∨ (¬ p4208)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p5059) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial39707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 5059)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory28963 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule39707 (meaning t m 2027) (meaning t m 2247) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 3662) (meaning t m 4208) (meaning t m 5059) (meaning t m 5190) source

theorem rule39711 (p2027 p2230 p2247 p2563 p3125 p3568 p4154 p4624 p5190 : Prop) (h : (¬ p2247) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p5190) ∨ (¬ p3568) ∨ (¬ p4624) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4624) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial39711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4624)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory28967 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule39711 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2563) (meaning t m 3125) (meaning t m 3568) (meaning t m 4154) (meaning t m 4624) (meaning t m 5190) source

theorem rule39715 (p2027 p2247 p2383 p2996 p3564 p3947 p3956 p4621 p5017 : Prop) (h : (¬ p3956) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p2247) ∨ (¬ p4621) ∨ (¬ p5017) ∨ (¬ p3564)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2383) ∨ (¬ p2996) ∨ (¬ p3564) ∨ (¬ p3947) ∨ (¬ p3956) ∨ (¬ p4621) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial39715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory28971 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule39715 (meaning t m 2027) (meaning t m 2247) (meaning t m 2383) (meaning t m 2996) (meaning t m 3564) (meaning t m 3947) (meaning t m 3956) (meaning t m 4621) (meaning t m 5017) source

theorem rule39716 (p2027 p2220 p2247 p2982 p2996 p3880 p3947 p4395 p4521 : Prop) (h : (¬ p3880) ∨ (¬ p3947) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p4395) ∨ (¬ p4521) ∨ (¬ p2220) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2247) ∨ (¬ p2982) ∨ (¬ p2996) ∨ (¬ p3880) ∨ (¬ p3947) ∨ (¬ p4395) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial39716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory28972 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 7 9)
  exact rule39716 (meaning t m 2027) (meaning t m 2220) (meaning t m 2247) (meaning t m 2982) (meaning t m 2996) (meaning t m 3880) (meaning t m 3947) (meaning t m 4395) (meaning t m 4521) source

theorem rule39717 (p1975 p2027 p2707 p2842 p3434 p3585 p4107 : Prop) (h : (¬ p1975) ∨ p2842 ∨ (¬ p4107) ∨ (¬ p3434) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2707)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2707) ∨ (p2842) ∨ (¬ p3434) ∨ (¬ p3585) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial39717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory28973 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 6 7) (m.theta 7 9)
  exact rule39717 (meaning t m 1975) (meaning t m 2027) (meaning t m 2707) (meaning t m 2842) (meaning t m 3434) (meaning t m 3585) (meaning t m 4107) source

theorem rule39718 (p2027 p2299 p2470 p2528 p3549 p3591 p3692 p4902 p5190 : Prop) (h : (¬ p3549) ∨ (¬ p2470) ∨ (¬ p4902) ∨ (¬ p3591) ∨ (¬ p2299) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p3692) ∨ (¬ p4902) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial39718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory28974 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule39718 (meaning t m 2027) (meaning t m 2299) (meaning t m 2470) (meaning t m 2528) (meaning t m 3549) (meaning t m 3591) (meaning t m 3692) (meaning t m 4902) (meaning t m 5190) source

theorem rule39719 (p1990 p2027 p2295 p2388 p2641 p3097 p3662 : Prop) (h : (¬ p2295) ∨ (¬ p2641) ∨ (¬ p1990) ∨ p2388 ∨ p2027 ∨ (¬ p3097) ∨ (¬ p3662)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2295) ∨ (p2388) ∨ (¬ p2641) ∨ (¬ p3097) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial39719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory28975 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule39719 (meaning t m 1990) (meaning t m 2027) (meaning t m 2295) (meaning t m 2388) (meaning t m 2641) (meaning t m 3097) (meaning t m 3662) source

theorem rule39726 (p2027 p2427 p3054 p3422 p4244 p4717 : Prop) (h : (¬ p4244) ∨ (¬ p3054) ∨ (¬ p2427) ∨ (¬ p4717) ∨ p2027 ∨ (¬ p3422)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3054) ∨ (¬ p3422) ∨ (¬ p4244) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial39726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory28982 t (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule39726 (meaning t m 2027) (meaning t m 2427) (meaning t m 3054) (meaning t m 3422) (meaning t m 4244) (meaning t m 4717) source

theorem rule39727 (p1982 p2027 p2352 p2363 p2573 p2633 p2737 p3365 p3553 p3588 p3873 p4777 p5190 : Prop) (h : p2027 ∨ p2633 ∨ (¬ p2573) ∨ (¬ p2363) ∨ (¬ p3553) ∨ (¬ p2352) ∨ (¬ p3588) ∨ (¬ p2737) ∨ (¬ p5190) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p1982) ∨ (¬ p4777)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (p2633) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4777) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial39727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4777)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory28983 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39727 (meaning t m 1982) (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 2633) (meaning t m 2737) (meaning t m 3365) (meaning t m 3553) (meaning t m 3588) (meaning t m 3873) (meaning t m 4777) (meaning t m 5190) source

theorem rule39729 (p2027 p2247 p2528 p2598 p2996 p3641 p3947 p4669 p4733 : Prop) (h : (¬ p2996) ∨ (¬ p2247) ∨ (¬ p4733) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p2528) ∨ (¬ p4669) ∨ (¬ p3641)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2996) ∨ (¬ p3641) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial39729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory28985 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule39729 (meaning t m 2027) (meaning t m 2247) (meaning t m 2528) (meaning t m 2598) (meaning t m 2996) (meaning t m 3641) (meaning t m 3947) (meaning t m 4669) (meaning t m 4733) source

theorem rule39730 (p2027 p2245 p2352 p2459 p2598 p3172 p3422 p4118 p4133 p4733 : Prop) (h : (¬ p4133) ∨ (¬ p3422) ∨ (¬ p2352) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p3172) ∨ (¬ p2598) ∨ (¬ p2245) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2598) ∨ (¬ p3172) ∨ (¬ p3422) ∨ (¬ p4118) ∨ (¬ p4133) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial39730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory28986 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39730 (meaning t m 2027) (meaning t m 2245) (meaning t m 2352) (meaning t m 2459) (meaning t m 2598) (meaning t m 3172) (meaning t m 3422) (meaning t m 4118) (meaning t m 4133) (meaning t m 4733) source

theorem rule39733 (p1990 p2388 p2860 p4906 : Prop) (h : p2388 ∨ (¬ p1990) ∨ (¬ p2860) ∨ p4906) : (¬ p1990) ∨ (p2388) ∨ (¬ p2860) ∨ (p4906) := by
  classical
  tauto

theorem initial39733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2860)) ∨ (meaning t m 4906) := by
  have source := ElevenTheory.theory28989 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule39733 (meaning t m 1990) (meaning t m 2388) (meaning t m 2860) (meaning t m 4906) source

theorem rule39734 (p1976 p2027 p2493 p2737 p2842 p3365 p3461 p3564 p3590 p4379 p4444 p5346 : Prop) (h : (¬ p2493) ∨ (¬ p3590) ∨ (¬ p3564) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p1976) ∨ (¬ p4444) ∨ (¬ p5346) ∨ (¬ p2737) ∨ (¬ p4379) ∨ (¬ p3461) ∨ p2842) : (¬ p1976) ∨ (p2027) ∨ (¬ p2493) ∨ (¬ p2737) ∨ (p2842) ∨ (¬ p3365) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3590) ∨ (¬ p4379) ∨ (¬ p4444) ∨ (¬ p5346) := by
  classical
  tauto

theorem initial39734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5346)) := by
  have source := ElevenTheory.theory28990 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule39734 (meaning t m 1976) (meaning t m 2027) (meaning t m 2493) (meaning t m 2737) (meaning t m 2842) (meaning t m 3365) (meaning t m 3461) (meaning t m 3564) (meaning t m 3590) (meaning t m 4379) (meaning t m 4444) (meaning t m 5346) source

theorem rule39736 (p2027 p3670 p4137 p4191 p4421 p4976 p5454 : Prop) (h : (¬ p4137) ∨ (¬ p4976) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p4421) ∨ (¬ p5454) ∨ (¬ p3670)) : (p2027) ∨ (¬ p3670) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4421) ∨ (¬ p4976) ∨ (¬ p5454) := by
  classical
  tauto

theorem initial39736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4976)) ∨ (¬ (meaning t m 5454)) := by
  have source := ElevenTheory.theory28992 t (m.theta 2 9) (m.theta 3 6) (m.theta 3 9) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule39736 (meaning t m 2027) (meaning t m 3670) (meaning t m 4137) (meaning t m 4191) (meaning t m 4421) (meaning t m 4976) (meaning t m 5454) source

theorem rule39738 (p2007 p2027 p2534 p2545 p3189 p3256 p4111 : Prop) (h : p2545 ∨ (¬ p4111) ∨ (¬ p3256) ∨ (¬ p2007) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p3189)) : (¬ p2007) ∨ (p2027) ∨ (¬ p2534) ∨ (p2545) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial39738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory28994 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule39738 (meaning t m 2007) (meaning t m 2027) (meaning t m 2534) (meaning t m 2545) (meaning t m 3189) (meaning t m 3256) (meaning t m 4111) source

theorem rule39739 (p2027 p2295 p3105 p3745 p3822 p4193 p5046 : Prop) (h : (¬ p3745) ∨ (¬ p4193) ∨ (¬ p5046) ∨ (¬ p3105) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p3822)) : (p2027) ∨ (¬ p2295) ∨ (¬ p3105) ∨ (¬ p3745) ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial39739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory28995 t (m.theta 2 5) (m.theta 2 6) (m.theta 3 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule39739 (meaning t m 2027) (meaning t m 2295) (meaning t m 3105) (meaning t m 3745) (meaning t m 3822) (meaning t m 4193) (meaning t m 5046) source

theorem rule39742 (p1982 p2027 p2363 p2383 p2779 p2829 p2842 p3585 : Prop) (h : (¬ p3585) ∨ p2842 ∨ (¬ p2779) ∨ p2027 ∨ (¬ p2383) ∨ (¬ p2363) ∨ (¬ p1982) ∨ (¬ p2829)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (p2842) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial39742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory28998 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule39742 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 2779) (meaning t m 2829) (meaning t m 2842) (meaning t m 3585) source

theorem rule39744 (p2027 p2247 p2996 p3276 p3355 p3947 p4444 p4669 p5190 : Prop) (h : (¬ p4444) ∨ (¬ p5190) ∨ (¬ p4669) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p3947) ∨ (¬ p3355) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3947) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial39744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory29000 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule39744 (meaning t m 2027) (meaning t m 2247) (meaning t m 2996) (meaning t m 3276) (meaning t m 3355) (meaning t m 3947) (meaning t m 4444) (meaning t m 4669) (meaning t m 5190) source

theorem rule39747 (p1982 p2027 p2230 p2528 p2611 p3362 p3641 p3684 : Prop) (h : p2611 ∨ (¬ p3641) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p3362) ∨ (¬ p2230) ∨ (¬ p2528) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2528) ∨ (p2611) ∨ (¬ p3362) ∨ (¬ p3641) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial39747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory29003 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule39747 (meaning t m 1982) (meaning t m 2027) (meaning t m 2230) (meaning t m 2528) (meaning t m 2611) (meaning t m 3362) (meaning t m 3641) (meaning t m 3684) source

theorem rule39748 (p1982 p2027 p2192 p2220 p2363 p2873 p3646 p4441 : Prop) (h : (¬ p2363) ∨ (¬ p1982) ∨ (¬ p2192) ∨ p2873 ∨ (¬ p2220) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p4441)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2220) ∨ (¬ p2363) ∨ (p2873) ∨ (¬ p3646) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial39748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory29004 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule39748 (meaning t m 1982) (meaning t m 2027) (meaning t m 2192) (meaning t m 2220) (meaning t m 2363) (meaning t m 2873) (meaning t m 3646) (meaning t m 4441) source

theorem rule39749 (p1982 p2027 p2233 p2363 p2573 p3584 p3641 p4157 : Prop) (h : (¬ p4157) ∨ (¬ p3641) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p1982) ∨ p2233 ∨ (¬ p2573) ∨ (¬ p3584)) : (¬ p1982) ∨ (p2027) ∨ (p2233) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p4157) := by
  classical
  tauto

theorem initial39749 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4157)) := by
  have source := ElevenTheory.theory29005 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule39749 (meaning t m 1982) (meaning t m 2027) (meaning t m 2233) (meaning t m 2363) (meaning t m 2573) (meaning t m 3584) (meaning t m 3641) (meaning t m 4157) source

theorem rule39751 (p2027 p2459 p2696 p3136 p3156 p3860 p4261 p4733 p4902 : Prop) (h : (¬ p4261) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3156) ∨ (¬ p3136) ∨ (¬ p4733) ∨ (¬ p3860) ∨ (¬ p2459) ∨ (¬ p4902)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4733) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial39751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory29007 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39751 (meaning t m 2027) (meaning t m 2459) (meaning t m 2696) (meaning t m 3136) (meaning t m 3156) (meaning t m 3860) (meaning t m 4261) (meaning t m 4733) (meaning t m 4902) source

theorem rule39752 (p2027 p2696 p2922 p3540 p3590 p3905 p4749 : Prop) (h : (¬ p3590) ∨ (¬ p3905) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p2922) ∨ (¬ p4749)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p3590) ∨ (¬ p3905) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial39752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory29008 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 7)
  exact rule39752 (meaning t m 2027) (meaning t m 2696) (meaning t m 2922) (meaning t m 3540) (meaning t m 3590) (meaning t m 3905) (meaning t m 4749) source

theorem rule39753 (p2027 p2598 p3641 p3817 p4149 p4366 p4381 p4733 p5119 : Prop) (h : (¬ p4149) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p5119) ∨ (¬ p4381) ∨ (¬ p3817) ∨ (¬ p4733) ∨ (¬ p4366)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p3817) ∨ (¬ p4149) ∨ (¬ p4366) ∨ (¬ p4381) ∨ (¬ p4733) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial39753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory29009 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule39753 (meaning t m 2027) (meaning t m 2598) (meaning t m 3641) (meaning t m 3817) (meaning t m 4149) (meaning t m 4366) (meaning t m 4381) (meaning t m 4733) (meaning t m 5119) source

theorem rule39761 (p2027 p2829 p3483 p3588 p4471 p4624 : Prop) (h : (¬ p3483) ∨ (¬ p4471) ∨ (¬ p3588) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p4624)) : (p2027) ∨ (¬ p2829) ∨ (¬ p3483) ∨ (¬ p3588) ∨ (¬ p4471) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial39761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4471)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory29017 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 9)
  exact rule39761 (meaning t m 2027) (meaning t m 2829) (meaning t m 3483) (meaning t m 3588) (meaning t m 4471) (meaning t m 4624) source

theorem rule39763 (p2027 p2341 p2528 p3266 p3688 p3954 p4329 p4383 p5207 p5254 : Prop) (h : (¬ p3954) ∨ (¬ p5207) ∨ (¬ p4383) ∨ p2027 ∨ (¬ p3688) ∨ (¬ p2341) ∨ (¬ p4329) ∨ (¬ p3266) ∨ (¬ p5254) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4329) ∨ (¬ p4383) ∨ (¬ p5207) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial39763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4329)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 5207)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory29019 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 2 6) (m.theta 4 8) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule39763 (meaning t m 2027) (meaning t m 2341) (meaning t m 2528) (meaning t m 3266) (meaning t m 3688) (meaning t m 3954) (meaning t m 4329) (meaning t m 4383) (meaning t m 5207) (meaning t m 5254) source

theorem rule39767 (p2027 p2696 p3319 p3366 p3461 p3585 p3918 p4444 p4697 p4842 p5160 : Prop) (h : p3366 ∨ (¬ p4697) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p3585) ∨ (¬ p3319) ∨ (¬ p2696) ∨ (¬ p4842) ∨ (¬ p3918) ∨ (¬ p4444) ∨ (¬ p5160)) : (p2027) ∨ (¬ p2696) ∨ (¬ p3319) ∨ (p3366) ∨ (¬ p3461) ∨ (¬ p3585) ∨ (¬ p3918) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p4842) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial39767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3319)) ∨ (meaning t m 3366) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4842)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory29023 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 4 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule39767 (meaning t m 2027) (meaning t m 2696) (meaning t m 3319) (meaning t m 3366) (meaning t m 3461) (meaning t m 3585) (meaning t m 3918) (meaning t m 4444) (meaning t m 4697) (meaning t m 4842) (meaning t m 5160) source

theorem rule39769 (p2027 p2481 p2881 p3201 p3874 p3960 p4277 : Prop) (h : (¬ p4277) ∨ (¬ p2481) ∨ (¬ p3874) ∨ (¬ p2881) ∨ (¬ p3960) ∨ (¬ p3201) ∨ p2027) : (p2027) ∨ (¬ p2481) ∨ (¬ p2881) ∨ (¬ p3201) ∨ (¬ p3874) ∨ (¬ p3960) ∨ (¬ p4277) := by
  classical
  tauto

theorem initial39769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4277)) := by
  have source := ElevenTheory.theory29025 t (m.theta 0 8) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule39769 (meaning t m 2027) (meaning t m 2481) (meaning t m 2881) (meaning t m 3201) (meaning t m 3874) (meaning t m 3960) (meaning t m 4277) source

theorem rule39770 (p2027 p2341 p2417 p2696 p2780 p3644 p3759 p3917 p4625 p4749 p5201 : Prop) (h : (¬ p2341) ∨ (¬ p3759) ∨ (¬ p5201) ∨ (¬ p4625) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2417) ∨ (¬ p4749) ∨ (¬ p2780) ∨ (¬ p3644) ∨ (¬ p3917)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2417) ∨ (¬ p2696) ∨ (¬ p2780) ∨ (¬ p3644) ∨ (¬ p3759) ∨ (¬ p3917) ∨ (¬ p4625) ∨ (¬ p4749) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial39770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory29026 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule39770 (meaning t m 2027) (meaning t m 2341) (meaning t m 2417) (meaning t m 2696) (meaning t m 2780) (meaning t m 3644) (meaning t m 3759) (meaning t m 3917) (meaning t m 4625) (meaning t m 4749) (meaning t m 5201) source

theorem rule39771 (p3564 p3917 p4390 : Prop) (h : (¬ p3564) ∨ (¬ p3917) ∨ (¬ p4390)) : (¬ p3564) ∨ (¬ p3917) ∨ (¬ p4390) := by
  classical
  tauto

theorem initial39771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4390)) := by
  have source := ElevenTheory.theory29027 (m.theta 2 6) (m.theta 4 6) (m.theta 6 9)
  exact rule39771 (meaning t m 3564) (meaning t m 3917) (meaning t m 4390) source

theorem rule39776 (p2027 p2192 p3371 p3585 p3758 p4392 p4749 : Prop) (h : (¬ p4392) ∨ (¬ p2192) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p4749) ∨ (¬ p3371)) : (p2027) ∨ (¬ p2192) ∨ (¬ p3371) ∨ (¬ p3585) ∨ (¬ p3758) ∨ (¬ p4392) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial39776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory29032 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6)
  exact rule39776 (meaning t m 2027) (meaning t m 2192) (meaning t m 3371) (meaning t m 3585) (meaning t m 3758) (meaning t m 4392) (meaning t m 4749) source

theorem rule39784 (p1994 p2027 p2114 p2132 p2440 p2737 p3365 p3695 : Prop) (h : p2027 ∨ (¬ p1994) ∨ p2114 ∨ (¬ p2440) ∨ (¬ p3695) ∨ (¬ p3365) ∨ (¬ p2132) ∨ (¬ p2737)) : (¬ p1994) ∨ (p2027) ∨ (p2114) ∨ (¬ p2132) ∨ (¬ p2440) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3695) := by
  classical
  tauto

theorem initial39784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3695)) := by
  have source := ElevenTheory.theory29040 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5)
  exact rule39784 (meaning t m 1994) (meaning t m 2027) (meaning t m 2114) (meaning t m 2132) (meaning t m 2440) (meaning t m 2737) (meaning t m 3365) (meaning t m 3695) source

theorem rule39786 (p2027 p2249 p2341 p2459 p2509 p2952 p3027 p4066 p4202 p4282 p4286 p5118 : Prop) (h : p2027 ∨ (¬ p5118) ∨ (¬ p2459) ∨ (¬ p4286) ∨ (¬ p3027) ∨ (¬ p2952) ∨ p4202 ∨ (¬ p2509) ∨ (¬ p4282) ∨ (¬ p2249) ∨ (¬ p2341) ∨ (¬ p4066)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2509) ∨ (¬ p2952) ∨ (¬ p3027) ∨ (¬ p4066) ∨ (p4202) ∨ (¬ p4282) ∨ (¬ p4286) ∨ (¬ p5118) := by
  classical
  tauto

theorem initial39786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4066)) ∨ (meaning t m 4202) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5118)) := by
  have source := ElevenTheory.theory29042 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 3 5) (m.theta 3 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule39786 (meaning t m 2027) (meaning t m 2249) (meaning t m 2341) (meaning t m 2459) (meaning t m 2509) (meaning t m 2952) (meaning t m 3027) (meaning t m 4066) (meaning t m 4202) (meaning t m 4282) (meaning t m 4286) (meaning t m 5118) source

theorem rule39789 (p2027 p2331 p3005 p3486 p3555 p3570 p4117 p4195 p4550 p4733 : Prop) (h : (¬ p3005) ∨ (¬ p4195) ∨ (¬ p4117) ∨ (¬ p4550) ∨ (¬ p3570) ∨ (¬ p3555) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p3486)) : (p2027) ∨ (¬ p2331) ∨ (¬ p3005) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4550) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial39789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory29045 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8)
  exact rule39789 (meaning t m 2027) (meaning t m 2331) (meaning t m 3005) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 4117) (meaning t m 4195) (meaning t m 4550) (meaning t m 4733) source

theorem rule39790 (p2027 p2651 p2957 p3276 p3333 p3556 p4315 p4343 p4790 p4831 p5660 : Prop) (h : (¬ p2651) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p3333) ∨ (¬ p4790) ∨ (¬ p2957) ∨ (¬ p4343) ∨ (¬ p4315) ∨ (¬ p4831) ∨ (¬ p3276) ∨ (¬ p5660)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2957) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3556) ∨ (¬ p4315) ∨ (¬ p4343) ∨ (¬ p4790) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial39790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory29046 t (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule39790 (meaning t m 2027) (meaning t m 2651) (meaning t m 2957) (meaning t m 3276) (meaning t m 3333) (meaning t m 3556) (meaning t m 4315) (meaning t m 4343) (meaning t m 4790) (meaning t m 4831) (meaning t m 5660) source

theorem rule39794 (p2027 p2088 p3553 p4348 p4590 p4854 : Prop) (h : p2027 ∨ (¬ p4590) ∨ (¬ p2088) ∨ (¬ p4348) ∨ (¬ p4854) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4590) ∨ (¬ p4854) := by
  classical
  tauto

theorem initial39794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 4854)) := by
  have source := ElevenTheory.theory29050 t (m.theta 0 7) (m.theta 0 8) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule39794 (meaning t m 2027) (meaning t m 2088) (meaning t m 3553) (meaning t m 4348) (meaning t m 4590) (meaning t m 4854) source

theorem rule39795 (p1975 p2027 p2299 p2341 p2764 p3821 p4381 : Prop) (h : (¬ p4381) ∨ p2764 ∨ (¬ p2299) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2341) ∨ (¬ p3821)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (p2764) ∨ (¬ p3821) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial39795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory29051 t (m.theta 0 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule39795 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 2764) (meaning t m 3821) (meaning t m 4381) source

theorem rule39796 (p2027 p2246 p2651 p2717 p2744 p3016 p3366 p3551 p3564 p3820 p4324 p4621 : Prop) (h : (¬ p3366) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p4621) ∨ (¬ p2717) ∨ (¬ p4324) ∨ (¬ p3564)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2717) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3366) ∨ (¬ p3551) ∨ (¬ p3564) ∨ (¬ p3820) ∨ (¬ p4324) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial39796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory29052 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule39796 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2717) (meaning t m 2744) (meaning t m 3016) (meaning t m 3366) (meaning t m 3551) (meaning t m 3564) (meaning t m 3820) (meaning t m 4324) (meaning t m 4621) source

theorem rule39797 (p1999 p2027 p2247 p2688 p3707 p3830 p4191 : Prop) (h : (¬ p1999) ∨ (¬ p3830) ∨ (¬ p2247) ∨ p2688 ∨ (¬ p3707) ∨ p2027 ∨ (¬ p4191)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial39797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory29053 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 6 9) (m.theta 9 10)
  exact rule39797 (meaning t m 1999) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3707) (meaning t m 3830) (meaning t m 4191) source

theorem rule39800 (p1975 p2027 p2247 p2553 p2688 p3830 p4137 p5152 : Prop) (h : (¬ p2553) ∨ (¬ p1975) ∨ (¬ p4137) ∨ (¬ p2247) ∨ p2688 ∨ (¬ p3830) ∨ p2027 ∨ (¬ p5152)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2553) ∨ (p2688) ∨ (¬ p3830) ∨ (¬ p4137) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial39800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory29056 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule39800 (meaning t m 1975) (meaning t m 2027) (meaning t m 2247) (meaning t m 2553) (meaning t m 2688) (meaning t m 3830) (meaning t m 4137) (meaning t m 5152) source

theorem rule39801 (p1988 p2027 p2233 p2573 p3343 p3461 p3574 p4331 : Prop) (h : p2027 ∨ (¬ p1988) ∨ p2233 ∨ (¬ p3343) ∨ (¬ p2573) ∨ (¬ p3461) ∨ (¬ p4331) ∨ (¬ p3574)) : (¬ p1988) ∨ (p2027) ∨ (p2233) ∨ (¬ p2573) ∨ (¬ p3343) ∨ (¬ p3461) ∨ (¬ p3574) ∨ (¬ p4331) := by
  classical
  tauto

theorem initial39801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4331)) := by
  have source := ElevenTheory.theory29057 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule39801 (meaning t m 1988) (meaning t m 2027) (meaning t m 2233) (meaning t m 2573) (meaning t m 3343) (meaning t m 3461) (meaning t m 3574) (meaning t m 4331) source

theorem rule39803 (p2027 p2156 p2608 p3115 p3370 p3860 p3952 p4261 p4377 p4450 : Prop) (h : (¬ p4261) ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p2608) ∨ (¬ p3860) ∨ (¬ p2156) ∨ (¬ p4450) ∨ (¬ p3370) ∨ p2027 ∨ (¬ p4377)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2608) ∨ (¬ p3115) ∨ (¬ p3370) ∨ (¬ p3860) ∨ (¬ p3952) ∨ (¬ p4261) ∨ (¬ p4377) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial39803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory29059 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 8 9)
  exact rule39803 (meaning t m 2027) (meaning t m 2156) (meaning t m 2608) (meaning t m 3115) (meaning t m 3370) (meaning t m 3860) (meaning t m 3952) (meaning t m 4261) (meaning t m 4377) (meaning t m 4450) source

theorem rule39805 (p2027 p2166 p3486 p3659 p3696 p4403 p4895 : Prop) (h : (¬ p4895) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p3486) ∨ (¬ p4403) ∨ (¬ p3696) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3486) ∨ (¬ p3659) ∨ (¬ p3696) ∨ (¬ p4403) ∨ (¬ p4895) := by
  classical
  tauto

theorem initial39805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 4403)) ∨ (¬ (meaning t m 4895)) := by
  have source := ElevenTheory.theory29061 t (m.theta 0 8) (m.theta 1 5) (m.theta 2 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule39805 (meaning t m 2027) (meaning t m 2166) (meaning t m 3486) (meaning t m 3659) (meaning t m 3696) (meaning t m 4403) (meaning t m 4895) source

end SunPrize.SMT
