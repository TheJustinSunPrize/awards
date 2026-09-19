import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory053
import SunPrize.Certificate.Theory054
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule30437 (p2027 p2248 p2499 p2946 p3115 p3452 p3680 p5254 p5514 : Prop) (h : p2027 ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p2248) ∨ (¬ p5514) ∨ (¬ p3452) ∨ (¬ p2499) ∨ (¬ p3680) ∨ (¬ p5254)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3452) ∨ (¬ p3680) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial30437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory19693 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 10) (m.theta 9 10)
  exact rule30437 (meaning t m 2027) (meaning t m 2248) (meaning t m 2499) (meaning t m 2946) (meaning t m 3115) (meaning t m 3452) (meaning t m 3680) (meaning t m 5254) (meaning t m 5514) source

theorem rule30438 (p2027 p2499 p2657 p3422 p3475 p3487 p4787 : Prop) (h : (¬ p2657) ∨ p2027 ∨ (¬ p4787) ∨ (¬ p3422) ∨ (¬ p2499) ∨ (¬ p3475) ∨ (¬ p3487)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p3487) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial30438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory19694 t (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule30438 (meaning t m 2027) (meaning t m 2499) (meaning t m 2657) (meaning t m 3422) (meaning t m 3475) (meaning t m 3487) (meaning t m 4787) source

theorem rule30439 (p1983 p2027 p2622 p2707 p2743 p3670 p4381 p5234 : Prop) (h : (¬ p2707) ∨ (¬ p1983) ∨ (¬ p2743) ∨ (¬ p4381) ∨ p2622 ∨ p2027 ∨ (¬ p3670) ∨ (¬ p5234)) : (¬ p1983) ∨ (p2027) ∨ (p2622) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3670) ∨ (¬ p4381) ∨ (¬ p5234) := by
  classical
  tauto

theorem initial30439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5234)) := by
  have source := ElevenTheory.theory19695 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 2 9) (m.theta 7 9) (m.theta 9 10)
  exact rule30439 (meaning t m 1983) (meaning t m 2027) (meaning t m 2622) (meaning t m 2707) (meaning t m 2743) (meaning t m 3670) (meaning t m 4381) (meaning t m 5234) source

theorem rule30440 (p2027 p2264 p2476 p2534 p2685 p2696 p3146 p4108 p4733 p4905 : Prop) (h : (¬ p2264) ∨ (¬ p4905) ∨ (¬ p2696) ∨ (¬ p4733) ∨ (¬ p2476) ∨ (¬ p2685) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p4108)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3146) ∨ (¬ p4108) ∨ (¬ p4733) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial30440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory19696 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule30440 (meaning t m 2027) (meaning t m 2264) (meaning t m 2476) (meaning t m 2534) (meaning t m 2685) (meaning t m 2696) (meaning t m 3146) (meaning t m 4108) (meaning t m 4733) (meaning t m 4905) source

theorem rule30441 (p2352 p3096 p3989 : Prop) (h : (¬ p3096) ∨ (¬ p2352) ∨ (¬ p3989)) : (¬ p2352) ∨ (¬ p3096) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial30441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory19697 (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule30441 (meaning t m 2352) (meaning t m 3096) (meaning t m 3989) source

theorem rule30445 (p2027 p2210 p2579 p2891 p3246 p3461 p3746 p4425 p4625 p5193 : Prop) (h : p2027 ∨ (¬ p5193) ∨ (¬ p3246) ∨ (¬ p2210) ∨ (¬ p2579) ∨ (¬ p2891) ∨ (¬ p4625) ∨ (¬ p4425) ∨ (¬ p3461) ∨ (¬ p3746)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2579) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3461) ∨ (¬ p3746) ∨ (¬ p4425) ∨ (¬ p4625) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial30445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3746)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory19701 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 4 6) (m.theta 4 9) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule30445 (meaning t m 2027) (meaning t m 2210) (meaning t m 2579) (meaning t m 2891) (meaning t m 3246) (meaning t m 3461) (meaning t m 3746) (meaning t m 4425) (meaning t m 4625) (meaning t m 5193) source

theorem rule30447 (p2027 p2459 p2911 p3857 p3961 p5199 : Prop) (h : (¬ p3961) ∨ (¬ p2459) ∨ (¬ p3857) ∨ (¬ p2911) ∨ (¬ p5199) ∨ p2027) : (p2027) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p5199) := by
  classical
  tauto

theorem initial30447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 5199)) := by
  have source := ElevenTheory.theory19703 t (m.theta 0 7) (m.theta 0 8) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule30447 (meaning t m 2027) (meaning t m 2459) (meaning t m 2911) (meaning t m 3857) (meaning t m 3961) (meaning t m 5199) source

theorem rule30452 (p2027 p2509 p2534 p2737 p2807 p2811 p3055 p3246 p3950 p4030 p4333 p4734 : Prop) (h : p2027 ∨ (¬ p2807) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3246) ∨ (¬ p4030) ∨ (¬ p4333) ∨ (¬ p3950) ∨ (¬ p2509) ∨ (¬ p4734) ∨ (¬ p2534) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4030) ∨ (¬ p4333) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial30452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory19708 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule30452 (meaning t m 2027) (meaning t m 2509) (meaning t m 2534) (meaning t m 2737) (meaning t m 2807) (meaning t m 2811) (meaning t m 3055) (meaning t m 3246) (meaning t m 3950) (meaning t m 4030) (meaning t m 4333) (meaning t m 4734) source

theorem rule30454 (p1999 p2027 p2295 p2313 p2622 p2797 p3654 : Prop) (h : (¬ p2295) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p3654) ∨ (¬ p1999) ∨ p2622 ∨ (¬ p2797)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p3654) := by
  classical
  tauto

theorem initial30454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3654)) := by
  have source := ElevenTheory.theory19710 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule30454 (meaning t m 1999) (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2622) (meaning t m 2797) (meaning t m 3654) source

theorem rule30461 (p2027 p2533 p3680 p3857 p4444 p4529 : Prop) (h : p2027 ∨ (¬ p4444) ∨ (¬ p2533) ∨ (¬ p4529) ∨ (¬ p3857) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2533) ∨ (¬ p3680) ∨ (¬ p3857) ∨ (¬ p4444) ∨ (¬ p4529) := by
  classical
  tauto

theorem initial30461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4529)) := by
  have source := ElevenTheory.theory19717 t (m.theta 0 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30461 (meaning t m 2027) (meaning t m 2533) (meaning t m 3680) (meaning t m 3857) (meaning t m 4444) (meaning t m 4529) source

theorem rule30465 (p1987 p2027 p2138 p2696 p2997 p3097 p3758 : Prop) (h : (¬ p1987) ∨ p2997 ∨ (¬ p2696) ∨ (¬ p2138) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p3758)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2696) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial30465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory19721 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7)
  exact rule30465 (meaning t m 1987) (meaning t m 2027) (meaning t m 2138) (meaning t m 2696) (meaning t m 2997) (meaning t m 3097) (meaning t m 3758) source

theorem rule30470 (p1976 p2027 p2138 p2191 p2192 p3578 p3758 : Prop) (h : (¬ p2192) ∨ p3578 ∨ (¬ p3758) ∨ (¬ p2191) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p1976)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (p3578) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial30470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory19726 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8)
  exact rule30470 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2191) (meaning t m 2192) (meaning t m 3578) (meaning t m 3758) source

theorem rule30475 (p2027 p2284 p2417 p2922 p3379 p3646 p3951 p4208 p4524 : Prop) (h : (¬ p3951) ∨ (¬ p4524) ∨ (¬ p2284) ∨ (¬ p4208) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3379)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3646) ∨ (¬ p3951) ∨ (¬ p4208) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial30475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory19731 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 9) (m.theta 7 9)
  exact rule30475 (meaning t m 2027) (meaning t m 2284) (meaning t m 2417) (meaning t m 2922) (meaning t m 3379) (meaning t m 3646) (meaning t m 3951) (meaning t m 4208) (meaning t m 4524) source

theorem rule30476 (p2027 p2295 p2417 p4037 p4396 p4712 : Prop) (h : (¬ p2417) ∨ (¬ p4396) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p4712) ∨ (¬ p4037)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2417) ∨ (¬ p4037) ∨ (¬ p4396) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial30476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory19732 t (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule30476 (meaning t m 2027) (meaning t m 2295) (meaning t m 2417) (meaning t m 4037) (meaning t m 4396) (meaning t m 4712) source

theorem rule30477 (p1986 p2027 p2764 p3367 p3588 p3821 p3959 p4381 : Prop) (h : (¬ p3367) ∨ (¬ p1986) ∨ p2764 ∨ (¬ p3588) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p3959)) : (¬ p1986) ∨ (p2027) ∨ (p2764) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3821) ∨ (¬ p3959) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial30477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory19733 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 7 9) (m.theta 9 10)
  exact rule30477 (meaning t m 1986) (meaning t m 2027) (meaning t m 2764) (meaning t m 3367) (meaning t m 3588) (meaning t m 3821) (meaning t m 3959) (meaning t m 4381) source

theorem rule30480 (p1998 p2027 p2177 p2319 p2764 p2797 p2952 p3567 p4063 p4208 p4260 p4322 p4787 : Prop) (h : (¬ p2319) ∨ (¬ p2797) ∨ (¬ p4063) ∨ p2027 ∨ (¬ p4260) ∨ p2764 ∨ (¬ p1998) ∨ (¬ p3567) ∨ (¬ p2952) ∨ (¬ p4322) ∨ (¬ p4208) ∨ (¬ p4787) ∨ (¬ p2177)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2319) ∨ (p2764) ∨ (¬ p2797) ∨ (¬ p2952) ∨ (¬ p3567) ∨ (¬ p4063) ∨ (¬ p4208) ∨ (¬ p4260) ∨ (¬ p4322) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial30480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2319)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4063)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory19736 t (m.theta 0 3) (m.theta 0 6) (m.theta 0 7) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8) (m.theta 9 10)
  exact rule30480 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2319) (meaning t m 2764) (meaning t m 2797) (meaning t m 2952) (meaning t m 3567) (meaning t m 4063) (meaning t m 4208) (meaning t m 4260) (meaning t m 4322) (meaning t m 4787) source

theorem rule30481 (p3399 p3834 p5363 : Prop) (h : (¬ p3399) ∨ (¬ p5363) ∨ (¬ p3834)) : (¬ p3399) ∨ (¬ p3834) ∨ (¬ p5363) := by
  classical
  tauto

theorem initial30481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 5363)) := by
  have source := ElevenTheory.theory19737 (m.theta 0 1) (m.theta 1 7) (m.theta 1 9)
  exact rule30481 (meaning t m 3399) (meaning t m 3834) (meaning t m 5363) source

theorem rule30484 (p2027 p2246 p2542 p2651 p2982 p3093 p3860 p4261 p4450 p4760 : Prop) (h : (¬ p2982) ∨ (¬ p2651) ∨ (¬ p4450) ∨ (¬ p4760) ∨ (¬ p2246) ∨ (¬ p3860) ∨ (¬ p2542) ∨ (¬ p4261) ∨ p2027 ∨ (¬ p3093)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2982) ∨ (¬ p3093) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4450) ∨ (¬ p4760) := by
  classical
  tauto

theorem initial30484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4760)) := by
  have source := ElevenTheory.theory19740 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 1 8) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 8 9)
  exact rule30484 (meaning t m 2027) (meaning t m 2246) (meaning t m 2542) (meaning t m 2651) (meaning t m 2982) (meaning t m 3093) (meaning t m 3860) (meaning t m 4261) (meaning t m 4450) (meaning t m 4760) source

theorem rule30490 (p3941 p4348 p5116 : Prop) (h : (¬ p4348) ∨ (¬ p5116) ∨ (¬ p3941)) : (¬ p3941) ∨ (¬ p4348) ∨ (¬ p5116) := by
  classical
  tauto

theorem initial30490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5116)) := by
  have source := ElevenTheory.theory19746 (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule30490 (meaning t m 3941) (meaning t m 4348) (meaning t m 5116) source

theorem rule30491 (p2156 p3872 p4109 p4235 : Prop) (h : (¬ p4235) ∨ (¬ p2156) ∨ (¬ p4109) ∨ (¬ p3872)) : (¬ p2156) ∨ (¬ p3872) ∨ (¬ p4109) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial30491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory19747 (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule30491 (meaning t m 2156) (meaning t m 3872) (meaning t m 4109) (meaning t m 4235) source

theorem rule30492 (p2027 p2138 p2156 p3819 p4316 p4320 p4555 p4984 : Prop) (h : (¬ p4984) ∨ (¬ p3819) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p4320) ∨ (¬ p4555) ∨ (¬ p4316) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2156) ∨ (¬ p3819) ∨ (¬ p4316) ∨ (¬ p4320) ∨ (¬ p4555) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial30492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4555)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory19748 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 7) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule30492 (meaning t m 2027) (meaning t m 2138) (meaning t m 2156) (meaning t m 3819) (meaning t m 4316) (meaning t m 4320) (meaning t m 4555) (meaning t m 4984) source

theorem rule30495 (p1982 p2027 p2437 p2459 p2518 p2545 p2928 p4404 : Prop) (h : (¬ p4404) ∨ p2027 ∨ p2545 ∨ (¬ p2459) ∨ (¬ p2437) ∨ (¬ p1982) ∨ (¬ p2928) ∨ (¬ p2518)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2437) ∨ (¬ p2459) ∨ (¬ p2518) ∨ (p2545) ∨ (¬ p2928) ∨ (¬ p4404) := by
  classical
  tauto

theorem initial30495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2518)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4404)) := by
  have source := ElevenTheory.theory19751 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule30495 (meaning t m 1982) (meaning t m 2027) (meaning t m 2437) (meaning t m 2459) (meaning t m 2518) (meaning t m 2545) (meaning t m 2928) (meaning t m 4404) source

theorem rule30497 (p1997 p2027 p2287 p2295 p2406 p2499 p2588 : Prop) (h : (¬ p1997) ∨ (¬ p2406) ∨ (¬ p2499) ∨ p2287 ∨ (¬ p2295) ∨ p2027 ∨ (¬ p2588)) : (¬ p1997) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2588) := by
  classical
  tauto

theorem initial30497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) := by
  have source := ElevenTheory.theory19753 t (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule30497 (meaning t m 1997) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 2406) (meaning t m 2499) (meaning t m 2588) source

theorem rule30501 (p1982 p2027 p2307 p2363 p2668 p2765 p3238 p3452 p3568 p4110 p5017 : Prop) (h : (¬ p2363) ∨ (¬ p1982) ∨ p2765 ∨ (¬ p4110) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p5017) ∨ (¬ p3452) ∨ (¬ p3238) ∨ (¬ p2307) ∨ (¬ p3568)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (p2765) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3568) ∨ (¬ p4110) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial30501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory19757 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule30501 (meaning t m 1982) (meaning t m 2027) (meaning t m 2307) (meaning t m 2363) (meaning t m 2668) (meaning t m 2765) (meaning t m 3238) (meaning t m 3452) (meaning t m 3568) (meaning t m 4110) (meaning t m 5017) source

theorem rule30502 (p2284 p2957 p3556 p3872 : Prop) (h : (¬ p2957) ∨ (¬ p3872) ∨ (¬ p3556) ∨ (¬ p2284)) : (¬ p2284) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial30502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory19758 (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule30502 (meaning t m 2284) (meaning t m 2957) (meaning t m 3556) (meaning t m 3872) source

theorem rule30504 (p3872 p4110 p4235 : Prop) (h : (¬ p3872) ∨ (¬ p4235) ∨ p4110) : (¬ p3872) ∨ (p4110) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial30504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3872)) ∨ (meaning t m 4110) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory19760 (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule30504 (meaning t m 3872) (meaning t m 4110) (meaning t m 4235) source

theorem rule30505 (p1995 p2027 p2499 p2534 p2766 p3422 p3874 : Prop) (h : (¬ p2534) ∨ p2766 ∨ (¬ p1995) ∨ (¬ p3874) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p3422)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p3422) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial30505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory19761 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule30505 (meaning t m 1995) (meaning t m 2027) (meaning t m 2499) (meaning t m 2534) (meaning t m 2766) (meaning t m 3422) (meaning t m 3874) source

theorem rule30509 (p2027 p2252 p2750 p2950 p3097 p3222 p3379 p3646 p3954 p4107 p4638 : Prop) (h : (¬ p3379) ∨ (¬ p4638) ∨ (¬ p3097) ∨ (¬ p4107) ∨ (¬ p3222) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p2950) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2950) ∨ (¬ p3097) ∨ (¬ p3222) ∨ (¬ p3379) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4638) := by
  classical
  tauto

theorem initial30509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4638)) := by
  have source := ElevenTheory.theory19765 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule30509 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2950) (meaning t m 3097) (meaning t m 3222) (meaning t m 3379) (meaning t m 3646) (meaning t m 3954) (meaning t m 4107) (meaning t m 4638) source

theorem rule30510 (p2247 p3452 p4281 : Prop) (h : (¬ p3452) ∨ (¬ p4281) ∨ p2247) : (p2247) ∨ (¬ p3452) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial30510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2247) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory19766 (m.theta 0 1) (m.theta 1 3) (m.theta 1 4)
  exact rule30510 (meaning t m 2247) (meaning t m 3452) (meaning t m 4281) source

theorem rule30514 (p1998 p2027 p2220 p2688 p2951 p2992 p3146 p4348 : Prop) (h : (¬ p2220) ∨ (¬ p2992) ∨ p2688 ∨ (¬ p4348) ∨ p2027 ∨ (¬ p2951) ∨ (¬ p1998) ∨ (¬ p3146)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2220) ∨ (p2688) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial30514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory19770 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule30514 (meaning t m 1998) (meaning t m 2027) (meaning t m 2220) (meaning t m 2688) (meaning t m 2951) (meaning t m 2992) (meaning t m 3146) (meaning t m 4348) source

theorem rule30518 (p1975 p2027 p2114 p2295 p3707 p3830 p3954 p5274 p5282 p5283 : Prop) (h : p2027 ∨ p2114 ∨ (¬ p2295) ∨ (¬ p1975) ∨ (¬ p3954) ∨ (¬ p3707) ∨ (¬ p5283) ∨ (¬ p5282) ∨ (¬ p5274) ∨ (¬ p3830)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2295) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p5274) ∨ (¬ p5282) ∨ (¬ p5283) := by
  classical
  tauto

theorem initial30518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5274)) ∨ (¬ (meaning t m 5282)) ∨ (¬ (meaning t m 5283)) := by
  have source := ElevenTheory.theory19774 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 9) (m.theta 3 10) (m.theta 3 6) (m.theta 3 9) (m.theta 6 7) (m.theta 9 10)
  exact rule30518 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2295) (meaning t m 3707) (meaning t m 3830) (meaning t m 3954) (meaning t m 5274) (meaning t m 5282) (meaning t m 5283) source

theorem rule30520 (p2027 p2563 p3125 p3880 p4506 p4603 : Prop) (h : (¬ p2563) ∨ (¬ p4506) ∨ p2027 ∨ (¬ p4603) ∨ (¬ p3880) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3880) ∨ (¬ p4506) ∨ (¬ p4603) := by
  classical
  tauto

theorem initial30520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4506)) ∨ (¬ (meaning t m 4603)) := by
  have source := ElevenTheory.theory19776 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9)
  exact rule30520 (meaning t m 2027) (meaning t m 2563) (meaning t m 3125) (meaning t m 3880) (meaning t m 4506) (meaning t m 4603) source

theorem rule30524 (p2027 p3516 p3540 p3947 p4327 p5201 : Prop) (h : (¬ p4327) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p5201) ∨ (¬ p3947) ∨ (¬ p3516)) : (p2027) ∨ (¬ p3516) ∨ (¬ p3540) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial30524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4327)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory19780 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule30524 (meaning t m 2027) (meaning t m 3516) (meaning t m 3540) (meaning t m 3947) (meaning t m 4327) (meaning t m 5201) source

theorem rule30528 (p2027 p2104 p2132 p2860 p4507 p4740 : Prop) (h : (¬ p2132) ∨ (¬ p2860) ∨ p2027 ∨ (¬ p4740) ∨ (¬ p4507) ∨ (¬ p2104)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p4507) ∨ (¬ p4740) := by
  classical
  tauto

theorem initial30528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 4740)) := by
  have source := ElevenTheory.theory19784 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 8) (m.theta 5 6) (m.theta 5 8)
  exact rule30528 (meaning t m 2027) (meaning t m 2104) (meaning t m 2132) (meaning t m 2860) (meaning t m 4507) (meaning t m 4740) source

theorem rule30532 (p3569 p4276 p4556 : Prop) (h : (¬ p4556) ∨ (¬ p3569) ∨ p4276) : (¬ p3569) ∨ (p4276) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial30532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3569)) ∨ (meaning t m 4276) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory19788 t (m.theta 4 7) (m.theta 5 7) (m.theta 6 7)
  exact rule30532 (meaning t m 3569) (meaning t m 4276) (meaning t m 4556) source

theorem rule30534 (p2027 p2299 p2655 p2780 p2946 p3156 p3367 p3759 p3822 p4734 p4902 : Prop) (h : (¬ p2655) ∨ (¬ p4734) ∨ (¬ p2946) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p2780) ∨ (¬ p2299) ∨ (¬ p4902) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2655) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3822) ∨ (¬ p4734) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial30534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory19790 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule30534 (meaning t m 2027) (meaning t m 2299) (meaning t m 2655) (meaning t m 2780) (meaning t m 2946) (meaning t m 3156) (meaning t m 3367) (meaning t m 3759) (meaning t m 3822) (meaning t m 4734) (meaning t m 4902) source

theorem rule30537 (p2027 p2166 p2274 p3549 p4509 p4512 : Prop) (h : (¬ p4512) ∨ (¬ p2274) ∨ (¬ p3549) ∨ p2027 ∨ (¬ p4509) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2274) ∨ (¬ p3549) ∨ (¬ p4509) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial30537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4509)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory19793 t (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule30537 (meaning t m 2027) (meaning t m 2166) (meaning t m 2274) (meaning t m 3549) (meaning t m 4509) (meaning t m 4512) source

theorem rule30539 (p2811 p2946 p3136 : Prop) (h : (¬ p2811) ∨ (¬ p2946) ∨ p3136) : (¬ p2811) ∨ (¬ p2946) ∨ (p3136) := by
  classical
  tauto

theorem initial30539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2946)) ∨ (meaning t m 3136) := by
  have source := ElevenTheory.theory19795 (m.theta 0 3) (m.theta 2 3) (m.theta 3 5)
  exact rule30539 (meaning t m 2811) (meaning t m 2946) (meaning t m 3136) source

theorem rule30541 (p2027 p3506 p3692 p4043 p4444 p5111 : Prop) (h : (¬ p3506) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p5111) ∨ (¬ p4043) ∨ (¬ p4444)) : (p2027) ∨ (¬ p3506) ∨ (¬ p3692) ∨ (¬ p4043) ∨ (¬ p4444) ∨ (¬ p5111) := by
  classical
  tauto

theorem initial30541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4043)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5111)) := by
  have source := ElevenTheory.theory19797 t (m.theta 3 8) (m.theta 3 9) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule30541 (meaning t m 2027) (meaning t m 3506) (meaning t m 3692) (meaning t m 4043) (meaning t m 4444) (meaning t m 5111) source

theorem rule30544 (p2027 p2870 p2946 p3414 p3699 p5053 : Prop) (h : (¬ p2870) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p3699) ∨ (¬ p2946) ∨ (¬ p5053)) : (p2027) ∨ (¬ p2870) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial30544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory19800 t (m.theta 0 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule30544 (meaning t m 2027) (meaning t m 2870) (meaning t m 2946) (meaning t m 3414) (meaning t m 3699) (meaning t m 5053) source

theorem rule30546 (p2299 p3644 p4710 : Prop) (h : (¬ p3644) ∨ (¬ p4710) ∨ p2299) : (p2299) ∨ (¬ p3644) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial30546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2299) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory19802 (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule30546 (meaning t m 2299) (meaning t m 3644) (meaning t m 4710) source

theorem rule30547 (p2027 p3537 p3583 p3880 p4188 p4885 : Prop) (h : (¬ p4885) ∨ p2027 ∨ (¬ p3537) ∨ (¬ p3583) ∨ (¬ p3880) ∨ (¬ p4188)) : (p2027) ∨ (¬ p3537) ∨ (¬ p3583) ∨ (¬ p3880) ∨ (¬ p4188) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial30547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory19803 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 4 5) (m.theta 5 8)
  exact rule30547 (meaning t m 2027) (meaning t m 3537) (meaning t m 3583) (meaning t m 3880) (meaning t m 4188) (meaning t m 4885) source

theorem rule30549 (p2027 p2870 p3212 p4235 p4385 p4539 : Prop) (h : (¬ p3212) ∨ (¬ p4385) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p2870) ∨ (¬ p4539)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3212) ∨ (¬ p4235) ∨ (¬ p4385) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial30549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory19805 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9)
  exact rule30549 (meaning t m 2027) (meaning t m 2870) (meaning t m 3212) (meaning t m 4235) (meaning t m 4385) (meaning t m 4539) source

theorem rule30555 (p2027 p2696 p3115 p3136 p3548 p4348 p4366 p4450 p4733 : Prop) (h : (¬ p4348) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p4450) ∨ (¬ p4366) ∨ (¬ p4733) ∨ (¬ p3136) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2696) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4450) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial30555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory19811 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule30555 (meaning t m 2027) (meaning t m 2696) (meaning t m 3115) (meaning t m 3136) (meaning t m 3548) (meaning t m 4348) (meaning t m 4366) (meaning t m 4450) (meaning t m 4733) source

theorem rule30560 (p1979 p2027 p2252 p2860 p2938 p2963 p2992 p3745 p4244 : Prop) (h : (¬ p3745) ∨ (¬ p2860) ∨ (¬ p2963) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p2252) ∨ p2938 ∨ (¬ p4244) ∨ (¬ p1979)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2860) ∨ (p2938) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial30560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2860)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory19816 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7)
  exact rule30560 (meaning t m 1979) (meaning t m 2027) (meaning t m 2252) (meaning t m 2860) (meaning t m 2938) (meaning t m 2963) (meaning t m 2992) (meaning t m 3745) (meaning t m 4244) source

theorem rule30561 (p2007 p2027 p2088 p2437 p2482 p2534 p2545 p3540 : Prop) (h : p2027 ∨ (¬ p2007) ∨ (¬ p2482) ∨ (¬ p3540) ∨ (¬ p2534) ∨ (¬ p2088) ∨ (¬ p2437) ∨ p2545) : (¬ p2007) ∨ (p2027) ∨ (¬ p2088) ∨ (¬ p2437) ∨ (¬ p2482) ∨ (¬ p2534) ∨ (p2545) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial30561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory19817 t (m.theta 0 4) (m.theta 0 8) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 8 9)
  exact rule30561 (meaning t m 2007) (meaning t m 2027) (meaning t m 2088) (meaning t m 2437) (meaning t m 2482) (meaning t m 2534) (meaning t m 2545) (meaning t m 3540) source

theorem rule30562 (p2027 p2254 p2608 p2819 p2829 p3146 p3172 p4118 p4134 : Prop) (h : (¬ p3146) ∨ p2027 ∨ (¬ p2819) ∨ (¬ p2254) ∨ (¬ p4118) ∨ (¬ p4134) ∨ (¬ p3172) ∨ (¬ p2608) ∨ (¬ p2829)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3146) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4134) := by
  classical
  tauto

theorem initial30562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4134)) := by
  have source := ElevenTheory.theory19818 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule30562 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2819) (meaning t m 2829) (meaning t m 3146) (meaning t m 3172) (meaning t m 4118) (meaning t m 4134) source

theorem rule30564 (p2027 p2220 p2901 p3370 p3497 p4235 p4632 : Prop) (h : (¬ p4235) ∨ (¬ p4632) ∨ (¬ p3370) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p2901) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2901) ∨ (¬ p3370) ∨ (¬ p3497) ∨ (¬ p4235) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial30564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory19820 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule30564 (meaning t m 2027) (meaning t m 2220) (meaning t m 2901) (meaning t m 3370) (meaning t m 3497) (meaning t m 4235) (meaning t m 4632) source

theorem rule30565 (p2027 p2143 p2641 p2668 p2696 p2742 p3146 p3583 p3697 p3857 p4134 p4737 : Prop) (h : (¬ p3697) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p2696) ∨ (¬ p3857) ∨ (¬ p2742) ∨ (¬ p3146) ∨ (¬ p4134) ∨ (¬ p2143) ∨ (¬ p2641) ∨ (¬ p3583) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3146) ∨ (¬ p3583) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4134) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial30565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3697)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory19821 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule30565 (meaning t m 2027) (meaning t m 2143) (meaning t m 2641) (meaning t m 2668) (meaning t m 2696) (meaning t m 2742) (meaning t m 3146) (meaning t m 3583) (meaning t m 3697) (meaning t m 3857) (meaning t m 4134) (meaning t m 4737) source

theorem rule30567 (p1990 p2027 p2284 p2323 p2992 p3166 p4360 : Prop) (h : (¬ p1990) ∨ p2027 ∨ (¬ p4360) ∨ (¬ p2284) ∨ (¬ p2992) ∨ p2323 ∨ (¬ p3166)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (p2323) ∨ (¬ p2992) ∨ (¬ p3166) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial30567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory19823 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6)
  exact rule30567 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2323) (meaning t m 2992) (meaning t m 3166) (meaning t m 4360) source

theorem rule30571 (p2027 p2352 p2493 p2608 p3834 p3979 p4321 p4376 p5119 : Prop) (h : (¬ p5119) ∨ (¬ p4321) ∨ (¬ p2608) ∨ (¬ p3834) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p3979) ∨ (¬ p4376) ∨ (¬ p2493)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2608) ∨ (¬ p3834) ∨ (¬ p3979) ∨ (¬ p4321) ∨ (¬ p4376) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial30571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory19827 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule30571 (meaning t m 2027) (meaning t m 2352) (meaning t m 2493) (meaning t m 2608) (meaning t m 3834) (meaning t m 3979) (meaning t m 4321) (meaning t m 4376) (meaning t m 5119) source

theorem rule30572 (p1975 p2027 p2717 p3437 p3516 p3551 p4107 : Prop) (h : p2027 ∨ (¬ p3516) ∨ p3437 ∨ (¬ p2717) ∨ (¬ p4107) ∨ (¬ p1975) ∨ (¬ p3551)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2717) ∨ (p3437) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial30572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory19828 t (m.theta 0 7) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule30572 (meaning t m 1975) (meaning t m 2027) (meaning t m 2717) (meaning t m 3437) (meaning t m 3516) (meaning t m 3551) (meaning t m 4107) source

theorem rule30575 (p2533 p3497 p4208 : Prop) (h : (¬ p4208) ∨ (¬ p2533) ∨ p3497) : (¬ p2533) ∨ (p3497) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial30575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2533)) ∨ (meaning t m 3497) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory19831 (m.theta 3 5) (m.theta 5 8) (m.theta 5 9)
  exact rule30575 (meaning t m 2533) (meaning t m 3497) (meaning t m 4208) source

theorem rule30579 (p3324 p4337 p4358 : Prop) (h : (¬ p4337) ∨ (¬ p3324) ∨ p4358) : (¬ p3324) ∨ (¬ p4337) ∨ (p4358) := by
  classical
  tauto

theorem initial30579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4337)) ∨ (meaning t m 4358) := by
  have source := ElevenTheory.theory19835 (m.theta 2 6) (m.theta 3 6) (m.theta 6 8)
  exact rule30579 (meaning t m 3324) (meaning t m 4337) (meaning t m 4358) source

theorem rule30583 (p2027 p3115 p3879 p3917 p4110 p4889 p5045 : Prop) (h : (¬ p3917) ∨ (¬ p4889) ∨ (¬ p3879) ∨ p2027 ∨ (¬ p5045) ∨ (¬ p4110) ∨ (¬ p3115)) : (p2027) ∨ (¬ p3115) ∨ (¬ p3879) ∨ (¬ p3917) ∨ (¬ p4110) ∨ (¬ p4889) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial30583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4889)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory19839 t (m.theta 2 6) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule30583 (meaning t m 2027) (meaning t m 3115) (meaning t m 3879) (meaning t m 3917) (meaning t m 4110) (meaning t m 4889) (meaning t m 5045) source

theorem rule30584 (p2027 p2427 p2449 p4362 p4382 p4948 : Prop) (h : (¬ p4382) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p4948) ∨ (¬ p4362) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2449) ∨ (¬ p4362) ∨ (¬ p4382) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial30584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 4362)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory19840 t (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule30584 (meaning t m 2027) (meaning t m 2427) (meaning t m 2449) (meaning t m 4362) (meaning t m 4382) (meaning t m 4948) source

theorem rule30587 (p2027 p2132 p2241 p2619 p2750 p2753 p3032 p3246 p3553 p4119 p4366 p4668 : Prop) (h : (¬ p4668) ∨ (¬ p2619) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2241) ∨ (¬ p3032) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p4366) ∨ (¬ p3553) ∨ (¬ p4119)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3032) ∨ (¬ p3246) ∨ (¬ p3553) ∨ (¬ p4119) ∨ (¬ p4366) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial30587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory19843 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9)
  exact rule30587 (meaning t m 2027) (meaning t m 2132) (meaning t m 2241) (meaning t m 2619) (meaning t m 2750) (meaning t m 2753) (meaning t m 3032) (meaning t m 3246) (meaning t m 3553) (meaning t m 4119) (meaning t m 4366) (meaning t m 4668) source

theorem rule30588 (p2870 p3105 p4402 : Prop) (h : (¬ p4402) ∨ (¬ p3105) ∨ p2870) : (p2870) ∨ (¬ p3105) ∨ (¬ p4402) := by
  classical
  tauto

theorem initial30588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2870) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4402)) := by
  have source := ElevenTheory.theory19844 (m.theta 2 5) (m.theta 5 7) (m.theta 5 9)
  exact rule30588 (meaning t m 2870) (meaning t m 3105) (meaning t m 4402) source

theorem rule30591 (p2027 p3115 p3497 p4134 p4347 p4695 p4947 : Prop) (h : (¬ p4134) ∨ (¬ p3497) ∨ (¬ p4347) ∨ (¬ p4695) ∨ (¬ p4947) ∨ p2027 ∨ (¬ p3115)) : (p2027) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4695) ∨ (¬ p4947) := by
  classical
  tauto

theorem initial30591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4695)) ∨ (¬ (meaning t m 4947)) := by
  have source := ElevenTheory.theory19847 t (m.theta 3 5) (m.theta 4 9) (m.theta 5 8) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule30591 (meaning t m 2027) (meaning t m 3115) (meaning t m 3497) (meaning t m 4134) (meaning t m 4347) (meaning t m 4695) (meaning t m 4947) source

theorem rule30593 (p2027 p2619 p2952 p3497 p4313 p4787 : Prop) (h : (¬ p2952) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p4787) ∨ (¬ p4313) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2619) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p4313) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial30593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory19849 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 8)
  exact rule30593 (meaning t m 2027) (meaning t m 2619) (meaning t m 2952) (meaning t m 3497) (meaning t m 4313) (meaning t m 4787) source

theorem rule30594 (p2027 p2630 p2657 p2745 p2807 p2996 : Prop) (h : (¬ p2807) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2745) ∨ (¬ p2657) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2745) ∨ (¬ p2807) ∨ (¬ p2996) := by
  classical
  tauto

theorem initial30594 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) := by
  have source := ElevenTheory.theory19850 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule30594 (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 2745) (meaning t m 2807) (meaning t m 2996) source

theorem rule30597 (p2027 p2573 p3083 p3486 p3555 p3570 p3574 p4420 p5190 : Prop) (h : (¬ p3486) ∨ (¬ p5190) ∨ p2027 ∨ (¬ p3083) ∨ (¬ p2573) ∨ (¬ p3574) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4420)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3083) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p3574) ∨ (¬ p4420) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial30597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory19853 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule30597 (meaning t m 2027) (meaning t m 2573) (meaning t m 3083) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 3574) (meaning t m 4420) (meaning t m 5190) source

theorem rule30599 (p1992 p2027 p2553 p2743 p2963 p3008 p3361 p3568 : Prop) (h : (¬ p2553) ∨ p3008 ∨ (¬ p2743) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p1992) ∨ (¬ p3568)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (p3008) ∨ (¬ p3361) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial30599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory19855 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule30599 (meaning t m 1992) (meaning t m 2027) (meaning t m 2553) (meaning t m 2743) (meaning t m 2963) (meaning t m 3008) (meaning t m 3361) (meaning t m 3568) source

theorem rule30600 (p2027 p2363 p2383 p2589 p2781 p2850 p3693 p3874 p3905 p4348 p4905 : Prop) (h : (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3874) ∨ (¬ p2850) ∨ (¬ p2589) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4905) ∨ (¬ p3693) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2589) ∨ (¬ p2781) ∨ (¬ p2850) ∨ (¬ p3693) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4348) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial30600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory19856 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule30600 (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 2589) (meaning t m 2781) (meaning t m 2850) (meaning t m 3693) (meaning t m 3874) (meaning t m 3905) (meaning t m 4348) (meaning t m 4905) source

theorem rule30602 (p3941 p4149 p4383 : Prop) (h : (¬ p4149) ∨ (¬ p4383) ∨ p3941) : (p3941) ∨ (¬ p4149) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial30602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3941) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory19858 (m.theta 4 8) (m.theta 7 8) (m.theta 8 10)
  exact rule30602 (meaning t m 3941) (meaning t m 4149) (meaning t m 4383) source

theorem rule30606 (p1976 p2027 p2169 p2553 p2780 p3822 p3956 : Prop) (h : p2169 ∨ (¬ p3822) ∨ p2027 ∨ (¬ p2780) ∨ (¬ p2553) ∨ (¬ p1976) ∨ (¬ p3956)) : (¬ p1976) ∨ (p2027) ∨ (p2169) ∨ (¬ p2553) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial30606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory19862 t (m.theta 0 2) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30606 (meaning t m 1976) (meaning t m 2027) (meaning t m 2169) (meaning t m 2553) (meaning t m 2780) (meaning t m 3822) (meaning t m 3956) source

theorem rule30612 (p2027 p2911 p3546 p3551 p3631 p4107 p4712 : Prop) (h : (¬ p3551) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p2911) ∨ (¬ p3546) ∨ (¬ p4712) ∨ (¬ p3631)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3546) ∨ (¬ p3551) ∨ (¬ p3631) ∨ (¬ p4107) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial30612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory19868 t (m.theta 0 7) (m.theta 1 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule30612 (meaning t m 2027) (meaning t m 2911) (meaning t m 3546) (meaning t m 3551) (meaning t m 3631) (meaning t m 4107) (meaning t m 4712) source

theorem rule30613 (p1982 p2027 p2331 p2363 p2545 p2657 p2668 : Prop) (h : p2545 ∨ (¬ p2331) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p1982) ∨ (¬ p2363)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2668) := by
  classical
  tauto

theorem initial30613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2668)) := by
  have source := ElevenTheory.theory19869 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule30613 (meaning t m 1982) (meaning t m 2027) (meaning t m 2331) (meaning t m 2363) (meaning t m 2545) (meaning t m 2657) (meaning t m 2668) source

theorem rule30614 (p2027 p2230 p2373 p2797 p2963 p3146 p3366 p3519 p4035 p4236 p4376 p5113 : Prop) (h : (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4035) ∨ (¬ p5113) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p3519) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p2230) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5113) := by
  classical
  tauto

theorem initial30614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5113)) := by
  have source := ElevenTheory.theory19870 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule30614 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 2797) (meaning t m 2963) (meaning t m 3146) (meaning t m 3366) (meaning t m 3519) (meaning t m 4035) (meaning t m 4236) (meaning t m 4376) (meaning t m 5113) source

theorem rule30616 (p2027 p3093 p3319 p3365 p3461 p3572 p4391 p4736 p4831 : Prop) (h : (¬ p4736) ∨ (¬ p3319) ∨ (¬ p3572) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p4831) ∨ (¬ p3461) ∨ (¬ p3093) ∨ (¬ p4391)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3365) ∨ (¬ p3461) ∨ (¬ p3572) ∨ (¬ p4391) ∨ (¬ p4736) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial30616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory19872 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule30616 (meaning t m 2027) (meaning t m 3093) (meaning t m 3319) (meaning t m 3365) (meaning t m 3461) (meaning t m 3572) (meaning t m 4391) (meaning t m 4736) (meaning t m 4831) source

theorem rule30618 (p2027 p2166 p2210 p2459 p3172 p3366 p3452 p4118 p4236 p4376 p4902 : Prop) (h : (¬ p2210) ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p2166) ∨ p2027 ∨ (¬ p4902) ∨ (¬ p2459) ∨ (¬ p3452) ∨ (¬ p3172) ∨ (¬ p4236) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2459) ∨ (¬ p3172) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p4118) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial30618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory19874 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 3 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule30618 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2459) (meaning t m 3172) (meaning t m 3366) (meaning t m 3452) (meaning t m 4118) (meaning t m 4236) (meaning t m 4376) (meaning t m 4902) source

theorem rule30619 (p2027 p3483 p3744 p3952 p3985 p5053 : Prop) (h : (¬ p3985) ∨ (¬ p3744) ∨ (¬ p5053) ∨ (¬ p3952) ∨ (¬ p3483) ∨ p2027) : (p2027) ∨ (¬ p3483) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p3985) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial30619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory19875 t (m.theta 2 5) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9)
  exact rule30619 (meaning t m 2027) (meaning t m 3483) (meaning t m 3744) (meaning t m 3952) (meaning t m 3985) (meaning t m 5053) source

theorem rule30622 (p2027 p2138 p2331 p3323 p3461 p3694 p4786 p5123 p5568 : Prop) (h : (¬ p3323) ∨ (¬ p5568) ∨ (¬ p3694) ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p4786) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p5123)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3694) ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial30622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory19878 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule30622 (meaning t m 2027) (meaning t m 2138) (meaning t m 2331) (meaning t m 3323) (meaning t m 3461) (meaning t m 3694) (meaning t m 4786) (meaning t m 5123) (meaning t m 5568) source

theorem rule30625 (p2027 p2138 p2247 p2744 p3366 p3449 p4181 p4322 p4385 p5119 : Prop) (h : (¬ p2247) ∨ (¬ p4322) ∨ (¬ p4181) ∨ (¬ p4385) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p2744) ∨ (¬ p3449) ∨ (¬ p2138) ∨ (¬ p3366)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p4181) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial30625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory19881 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 5) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule30625 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3449) (meaning t m 4181) (meaning t m 4322) (meaning t m 4385) (meaning t m 5119) source

theorem rule30628 (p1999 p2027 p2406 p2409 p2982 p3680 p4191 : Prop) (h : p2409 ∨ (¬ p1999) ∨ (¬ p4191) ∨ (¬ p2406) ∨ (¬ p3680) ∨ p2027 ∨ (¬ p2982)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial30628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory19884 t (m.theta 1 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule30628 (meaning t m 1999) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2982) (meaning t m 3680) (meaning t m 4191) source

theorem rule30629 (p2088 p3177 p3256 : Prop) (h : (¬ p3256) ∨ (¬ p3177) ∨ p2088) : (p2088) ∨ (¬ p3177) ∨ (¬ p3256) := by
  classical
  tauto

theorem initial30629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2088) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3256)) := by
  have source := ElevenTheory.theory19885 (m.theta 0 8) (m.theta 3 8) (m.theta 8 9)
  exact rule30629 (meaning t m 2088) (meaning t m 3177) (meaning t m 3256) source

theorem rule30630 (p2027 p2440 p3016 p4203 p5433 p5440 : Prop) (h : (¬ p5433) ∨ (¬ p4203) ∨ (¬ p5440) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p2440)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4203) ∨ (¬ p5433) ∨ (¬ p5440) := by
  classical
  tauto

theorem initial30630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 5433)) ∨ (¬ (meaning t m 5440)) := by
  have source := ElevenTheory.theory19886 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 10) (m.theta 5 6)
  exact rule30630 (meaning t m 2027) (meaning t m 2440) (meaning t m 3016) (meaning t m 4203) (meaning t m 5433) (meaning t m 5440) source

theorem rule30631 (p2005 p2027 p2997 p3016 p3359 p3483 p3822 p4264 p5379 : Prop) (h : (¬ p3822) ∨ (¬ p3359) ∨ (¬ p3016) ∨ p2997 ∨ (¬ p2005) ∨ p2027 ∨ (¬ p4264) ∨ (¬ p3483) ∨ (¬ p5379)) : (¬ p2005) ∨ (p2027) ∨ (p2997) ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4264) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial30631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4264)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory19887 t (m.theta 0 9) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 9)
  exact rule30631 (meaning t m 2005) (meaning t m 2027) (meaning t m 2997) (meaning t m 3016) (meaning t m 3359) (meaning t m 3483) (meaning t m 3822) (meaning t m 4264) (meaning t m 5379) source

theorem rule30632 (p1984 p2027 p2579 p2997 p3483 p3822 p4108 p4137 : Prop) (h : p2997 ∨ (¬ p1984) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p4137) ∨ (¬ p3483) ∨ (¬ p4108)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2579) ∨ (p2997) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4108) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial30632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory19888 t (m.theta 0 1) (m.theta 0 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule30632 (meaning t m 1984) (meaning t m 2027) (meaning t m 2579) (meaning t m 2997) (meaning t m 3483) (meaning t m 3822) (meaning t m 4108) (meaning t m 4137) source

theorem rule30634 (p1994 p2027 p2630 p3360 p3516 p3572 p3947 : Prop) (h : (¬ p3572) ∨ (¬ p1994) ∨ (¬ p2630) ∨ p3360 ∨ p2027 ∨ (¬ p3947) ∨ (¬ p3516)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p3360) ∨ (¬ p3516) ∨ (¬ p3572) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial30634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory19890 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule30634 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 3360) (meaning t m 3516) (meaning t m 3572) (meaning t m 3947) source

theorem rule30636 (p2027 p2246 p2589 p2749 p2807 p3005 p3347 p3572 p3692 p3880 p4009 p5122 p5216 : Prop) (h : p2027 ∨ (¬ p2246) ∨ (¬ p5216) ∨ (¬ p3347) ∨ (¬ p3880) ∨ (¬ p2749) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p2589) ∨ (¬ p3692) ∨ (¬ p5122) ∨ (¬ p3005) ∨ (¬ p4009)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2589) ∨ (¬ p2749) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3347) ∨ (¬ p3572) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4009) ∨ (¬ p5122) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial30636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 5122)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory19892 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule30636 (meaning t m 2027) (meaning t m 2246) (meaning t m 2589) (meaning t m 2749) (meaning t m 2807) (meaning t m 3005) (meaning t m 3347) (meaning t m 3572) (meaning t m 3692) (meaning t m 3880) (meaning t m 4009) (meaning t m 5122) (meaning t m 5216) source

theorem rule30637 (p2027 p2630 p3016 p3572 p3740 p4708 : Prop) (h : (¬ p3572) ∨ (¬ p2630) ∨ (¬ p3740) ∨ (¬ p4708) ∨ p2027 ∨ (¬ p3016)) : (p2027) ∨ (¬ p2630) ∨ (¬ p3016) ∨ (¬ p3572) ∨ (¬ p3740) ∨ (¬ p4708) := by
  classical
  tauto

theorem initial30637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4708)) := by
  have source := ElevenTheory.theory19893 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7)
  exact rule30637 (meaning t m 2027) (meaning t m 2630) (meaning t m 3016) (meaning t m 3572) (meaning t m 3740) (meaning t m 4708) source

theorem rule30638 (p2027 p2264 p2579 p2807 p3941 p4117 p4137 p4191 p4729 p5119 : Prop) (h : p2027 ∨ (¬ p4191) ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p3941) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p2579) ∨ (¬ p5119) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2579) ∨ (¬ p2807) ∨ (¬ p3941) ∨ (¬ p4117) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4729) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial30638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory19894 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule30638 (meaning t m 2027) (meaning t m 2264) (meaning t m 2579) (meaning t m 2807) (meaning t m 3941) (meaning t m 4117) (meaning t m 4137) (meaning t m 4191) (meaning t m 4729) (meaning t m 5119) source

theorem rule30640 (p2027 p2246 p2449 p2744 p2761 p2807 p3055 p3366 p3874 p4286 p5123 : Prop) (h : (¬ p5123) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2449) ∨ (¬ p2246) ∨ (¬ p3874) ∨ (¬ p2807) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p4286)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2449) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial30640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory19896 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule30640 (meaning t m 2027) (meaning t m 2246) (meaning t m 2449) (meaning t m 2744) (meaning t m 2761) (meaning t m 2807) (meaning t m 3055) (meaning t m 3366) (meaning t m 3874) (meaning t m 4286) (meaning t m 5123) source

theorem rule30641 (p2027 p2579 p2608 p2707 p3434 p3950 p3956 p4347 p5193 : Prop) (h : p2027 ∨ (¬ p3434) ∨ (¬ p5193) ∨ (¬ p2579) ∨ (¬ p2707) ∨ (¬ p2608) ∨ (¬ p4347) ∨ (¬ p3950) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3950) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial30641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory19897 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule30641 (meaning t m 2027) (meaning t m 2579) (meaning t m 2608) (meaning t m 2707) (meaning t m 3434) (meaning t m 3950) (meaning t m 3956) (meaning t m 4347) (meaning t m 5193) source

theorem rule30649 (p2005 p2027 p2764 p3016 p3399 p3692 p4075 p4112 p4120 p4391 p4444 p4524 : Prop) (h : (¬ p2005) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4524) ∨ p2764 ∨ (¬ p3016) ∨ (¬ p4112) ∨ (¬ p3399) ∨ (¬ p4075) ∨ (¬ p4391)) : (¬ p2005) ∨ (p2027) ∨ (p2764) ∨ (¬ p3016) ∨ (¬ p3399) ∨ (¬ p3692) ∨ (¬ p4075) ∨ (¬ p4112) ∨ (¬ p4120) ∨ (¬ p4391) ∨ (¬ p4444) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial30649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory19905 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule30649 (meaning t m 2005) (meaning t m 2027) (meaning t m 2764) (meaning t m 3016) (meaning t m 3399) (meaning t m 3692) (meaning t m 4075) (meaning t m 4112) (meaning t m 4120) (meaning t m 4391) (meaning t m 4444) (meaning t m 4524) source

theorem rule30651 (p1985 p2027 p2202 p2589 p2911 p3389 p3570 : Prop) (h : (¬ p3389) ∨ p2202 ∨ (¬ p1985) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p2911)) : (¬ p1985) ∨ (p2027) ∨ (p2202) ∨ (¬ p2589) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial30651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory19907 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule30651 (meaning t m 1985) (meaning t m 2027) (meaning t m 2202) (meaning t m 2589) (meaning t m 2911) (meaning t m 3389) (meaning t m 3570) source

theorem rule30654 (p2027 p2187 p2246 p2284 p2608 p2744 p2946 p3549 p3591 p4405 : Prop) (h : (¬ p3549) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2744) ∨ (¬ p2608) ∨ (¬ p3591) ∨ (¬ p2246) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p4405)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial30654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory19910 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30654 (meaning t m 2027) (meaning t m 2187) (meaning t m 2246) (meaning t m 2284) (meaning t m 2608) (meaning t m 2744) (meaning t m 2946) (meaning t m 3549) (meaning t m 3591) (meaning t m 4405) source

theorem rule30658 (p2027 p2177 p2295 p2331 p2589 p2850 p3693 p3874 p3905 p4786 p4905 : Prop) (h : (¬ p2850) ∨ (¬ p2589) ∨ (¬ p3905) ∨ (¬ p2295) ∨ (¬ p4905) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2331) ∨ (¬ p3874) ∨ (¬ p4786) ∨ (¬ p3693)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3693) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4786) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial30658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory19914 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule30658 (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 2331) (meaning t m 2589) (meaning t m 2850) (meaning t m 3693) (meaning t m 3874) (meaning t m 3905) (meaning t m 4786) (meaning t m 4905) source

theorem rule30669 (p1991 p2027 p2202 p2563 p2952 p2992 p3745 p4154 : Prop) (h : p2027 ∨ (¬ p2992) ∨ (¬ p2952) ∨ (¬ p1991) ∨ (¬ p4154) ∨ (¬ p3745) ∨ (¬ p2563) ∨ p2202) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial30669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory19925 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6)
  exact rule30669 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2952) (meaning t m 2992) (meaning t m 3745) (meaning t m 4154) source

theorem rule30671 (p2027 p2264 p2995 p3570 p3952 p4558 : Prop) (h : p2027 ∨ (¬ p2264) ∨ (¬ p3952) ∨ (¬ p3570) ∨ (¬ p4558) ∨ (¬ p2995)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2995) ∨ (¬ p3570) ∨ (¬ p3952) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial30671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory19927 t (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule30671 (meaning t m 2027) (meaning t m 2264) (meaning t m 2995) (meaning t m 3570) (meaning t m 3952) (meaning t m 4558) source

theorem rule30672 (p2027 p2132 p2187 p2241 p2750 p2753 p2860 p3549 p3591 p4405 : Prop) (h : (¬ p4405) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2860) ∨ (¬ p2187) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial30672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory19928 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30672 (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 2860) (meaning t m 3549) (meaning t m 3591) (meaning t m 4405) source

theorem rule30673 (p2027 p2608 p3425 p3537 p3873 p4806 : Prop) (h : (¬ p3873) ∨ (¬ p4806) ∨ (¬ p3425) ∨ (¬ p3537) ∨ p2027 ∨ (¬ p2608)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3425) ∨ (¬ p3537) ∨ (¬ p3873) ∨ (¬ p4806) := by
  classical
  tauto

theorem initial30673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4806)) := by
  have source := ElevenTheory.theory19929 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8)
  exact rule30673 (meaning t m 2027) (meaning t m 2608) (meaning t m 3425) (meaning t m 3537) (meaning t m 3873) (meaning t m 4806) source

theorem rule30675 (p2027 p2341 p3276 p3688 p3945 p3954 p3985 p4385 p4444 p4636 p5059 p5207 : Prop) (h : (¬ p3954) ∨ (¬ p5207) ∨ (¬ p3985) ∨ p2027 ∨ (¬ p3276) ∨ (¬ p2341) ∨ (¬ p3945) ∨ (¬ p4636) ∨ (¬ p4444) ∨ (¬ p4385) ∨ (¬ p5059) ∨ (¬ p3688)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3276) ∨ (¬ p3688) ∨ (¬ p3945) ∨ (¬ p3954) ∨ (¬ p3985) ∨ (¬ p4385) ∨ (¬ p4444) ∨ (¬ p4636) ∨ (¬ p5059) ∨ (¬ p5207) := by
  classical
  tauto

theorem initial30675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4636)) ∨ (¬ (meaning t m 5059)) ∨ (¬ (meaning t m 5207)) := by
  have source := ElevenTheory.theory19931 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 4 9) (m.theta 5 9) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30675 (meaning t m 2027) (meaning t m 2341) (meaning t m 3276) (meaning t m 3688) (meaning t m 3945) (meaning t m 3954) (meaning t m 3985) (meaning t m 4385) (meaning t m 4444) (meaning t m 4636) (meaning t m 5059) (meaning t m 5207) source

theorem rule30677 (p2027 p2417 p2598 p3201 p3292 p3461 p4625 p4789 p5284 : Prop) (h : (¬ p3292) ∨ (¬ p4625) ∨ (¬ p3201) ∨ (¬ p5284) ∨ p2027 ∨ (¬ p4789) ∨ (¬ p2417) ∨ (¬ p3461) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3292) ∨ (¬ p3461) ∨ (¬ p4625) ∨ (¬ p4789) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial30677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory19933 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 9) (m.theta 4 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule30677 (meaning t m 2027) (meaning t m 2417) (meaning t m 2598) (meaning t m 3201) (meaning t m 3292) (meaning t m 3461) (meaning t m 4625) (meaning t m 4789) (meaning t m 5284) source

theorem rule30681 (p2839 p3599 p5031 : Prop) (h : (¬ p5031) ∨ (¬ p2839) ∨ p3599) : (¬ p2839) ∨ (p3599) ∨ (¬ p5031) := by
  classical
  tauto

theorem initial30681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2839)) ∨ (meaning t m 3599) ∨ (¬ (meaning t m 5031)) := by
  have source := ElevenTheory.theory19937 (m.theta 1 2) (m.theta 2 5) (m.theta 2 9)
  exact rule30681 (meaning t m 2839) (meaning t m 3599) (meaning t m 5031) source

theorem rule30683 (p2027 p2341 p3031 p3545 p3548 p3555 p4448 : Prop) (h : (¬ p3548) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p4448) ∨ (¬ p3545) ∨ (¬ p3031) ∨ (¬ p3555)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3031) ∨ (¬ p3545) ∨ (¬ p3548) ∨ (¬ p3555) ∨ (¬ p4448) := by
  classical
  tauto

theorem initial30683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4448)) := by
  have source := ElevenTheory.theory19939 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 3) (m.theta 1 5) (m.theta 1 7) (m.theta 7 8)
  exact rule30683 (meaning t m 2027) (meaning t m 2341) (meaning t m 3031) (meaning t m 3545) (meaning t m 3548) (meaning t m 3555) (meaning t m 4448) source

theorem rule30685 (p2000 p2027 p2534 p2579 p2766 p3422 p3874 : Prop) (h : p2027 ∨ (¬ p2000) ∨ (¬ p3422) ∨ (¬ p2579) ∨ (¬ p2534) ∨ (¬ p3874) ∨ p2766) : (¬ p2000) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2579) ∨ (p2766) ∨ (¬ p3422) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial30685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory19941 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule30685 (meaning t m 2000) (meaning t m 2027) (meaning t m 2534) (meaning t m 2579) (meaning t m 2766) (meaning t m 3422) (meaning t m 3874) source

theorem rule30692 (p2027 p2241 p2727 p3343 p3556 p3570 p4332 p4348 p4524 : Prop) (h : (¬ p2241) ∨ (¬ p4524) ∨ (¬ p3556) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p4332) ∨ (¬ p3343) ∨ (¬ p3570) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial30692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory19948 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule30692 (meaning t m 2027) (meaning t m 2241) (meaning t m 2727) (meaning t m 3343) (meaning t m 3556) (meaning t m 3570) (meaning t m 4332) (meaning t m 4348) (meaning t m 4524) source

theorem rule30693 (p2245 p3987 p5020 : Prop) (h : (¬ p2245) ∨ (¬ p5020) ∨ p3987) : (¬ p2245) ∨ (p3987) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial30693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2245)) ∨ (meaning t m 3987) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory19949 (m.theta 0 1) (m.theta 0 3) (m.theta 0 6)
  exact rule30693 (meaning t m 2245) (meaning t m 3987) (meaning t m 5020) source

theorem rule30696 (p2027 p2745 p3105 p4111 p4208 p4313 p4700 : Prop) (h : (¬ p4208) ∨ (¬ p4111) ∨ (¬ p2745) ∨ p2027 ∨ (¬ p3105) ∨ (¬ p4700) ∨ (¬ p4313)) : (p2027) ∨ (¬ p2745) ∨ (¬ p3105) ∨ (¬ p4111) ∨ (¬ p4208) ∨ (¬ p4313) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial30696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory19952 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 9)
  exact rule30696 (meaning t m 2027) (meaning t m 2745) (meaning t m 3105) (meaning t m 4111) (meaning t m 4208) (meaning t m 4313) (meaning t m 4700) source

theorem rule30699 (p2027 p2449 p3919 p3969 p4132 p4668 p5600 : Prop) (h : (¬ p3969) ∨ p2027 ∨ (¬ p3919) ∨ (¬ p4132) ∨ (¬ p5600) ∨ (¬ p4668) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p3919) ∨ (¬ p3969) ∨ (¬ p4132) ∨ (¬ p4668) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial30699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory19955 t (m.theta 3 7) (m.theta 3 8) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule30699 (meaning t m 2027) (meaning t m 2449) (meaning t m 3919) (meaning t m 3969) (meaning t m 4132) (meaning t m 4668) (meaning t m 5600) source

theorem rule30702 (p1979 p2027 p2459 p2633 p2992 p3177 p3857 p4360 : Prop) (h : (¬ p1979) ∨ (¬ p4360) ∨ (¬ p3177) ∨ p2027 ∨ (¬ p2459) ∨ p2633 ∨ (¬ p2992) ∨ (¬ p3857)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2992) ∨ (¬ p3177) ∨ (¬ p3857) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial30702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory19958 t (m.theta 0 8) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule30702 (meaning t m 1979) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 2992) (meaning t m 3177) (meaning t m 3857) (meaning t m 4360) source

theorem rule30707 (p2655 p2950 p3904 : Prop) (h : (¬ p3904) ∨ (¬ p2655) ∨ p2950) : (¬ p2655) ∨ (p2950) ∨ (¬ p3904) := by
  classical
  tauto

theorem initial30707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2655)) ∨ (meaning t m 2950) ∨ (¬ (meaning t m 3904)) := by
  have source := ElevenTheory.theory19963 (m.theta 0 3) (m.theta 0 4) (m.theta 0 5)
  exact rule30707 (meaning t m 2655) (meaning t m 2950) (meaning t m 3904) source

theorem rule30708 (p2027 p2528 p3266 p3322 p3693 p4134 p4191 : Prop) (h : (¬ p3266) ∨ (¬ p3322) ∨ (¬ p4191) ∨ (¬ p4134) ∨ (¬ p3693) ∨ (¬ p2528) ∨ p2027) : (p2027) ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3693) ∨ (¬ p4134) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial30708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory19964 t (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30708 (meaning t m 2027) (meaning t m 2528) (meaning t m 3266) (meaning t m 3322) (meaning t m 3693) (meaning t m 4134) (meaning t m 4191) source

theorem rule30711 (p1980 p2027 p2169 p3319 p3979 p4037 p4371 p5693 : Prop) (h : p2169 ∨ (¬ p4037) ∨ (¬ p3979) ∨ (¬ p1980) ∨ (¬ p3319) ∨ p2027 ∨ (¬ p4371) ∨ (¬ p5693)) : (¬ p1980) ∨ (p2027) ∨ (p2169) ∨ (¬ p3319) ∨ (¬ p3979) ∨ (¬ p4037) ∨ (¬ p4371) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial30711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory19967 t (m.theta 1 6) (m.theta 1 8) (m.theta 3 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10)
  exact rule30711 (meaning t m 1980) (meaning t m 2027) (meaning t m 2169) (meaning t m 3319) (meaning t m 3979) (meaning t m 4037) (meaning t m 4371) (meaning t m 5693) source

theorem rule30712 (p1983 p2027 p2169 p2498 p3319 p3461 p3956 p4381 : Prop) (h : p2169 ∨ (¬ p3956) ∨ (¬ p2498) ∨ (¬ p3319) ∨ (¬ p1983) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p3461)) : (¬ p1983) ∨ (p2027) ∨ (p2169) ∨ (¬ p2498) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3956) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial30712 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory19968 t (m.theta 1 6) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule30712 (meaning t m 1983) (meaning t m 2027) (meaning t m 2169) (meaning t m 2498) (meaning t m 3319) (meaning t m 3461) (meaning t m 3956) (meaning t m 4381) source

theorem rule30714 (p2027 p2373 p3136 p3177 p3696 p4195 p4196 p4702 : Prop) (h : (¬ p3177) ∨ (¬ p4196) ∨ (¬ p3696) ∨ p2027 ∨ (¬ p2373) ∨ (¬ p4195) ∨ (¬ p3136) ∨ (¬ p4702)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3136) ∨ (¬ p3177) ∨ (¬ p3696) ∨ (¬ p4195) ∨ (¬ p4196) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial30714 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory19970 t (m.theta 0 8) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8)
  exact rule30714 (meaning t m 2027) (meaning t m 2373) (meaning t m 3136) (meaning t m 3177) (meaning t m 3696) (meaning t m 4195) (meaning t m 4196) (meaning t m 4702) source

theorem rule30715 (p1988 p2027 p2688 p2952 p2992 p3286 p3680 p4039 : Prop) (h : (¬ p1988) ∨ (¬ p3680) ∨ p2027 ∨ p2688 ∨ (¬ p2992) ∨ (¬ p2952) ∨ (¬ p3286) ∨ (¬ p4039)) : (¬ p1988) ∨ (p2027) ∨ (p2688) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3286) ∨ (¬ p3680) ∨ (¬ p4039) := by
  classical
  tauto

theorem initial30715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4039)) := by
  have source := ElevenTheory.theory19971 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule30715 (meaning t m 1988) (meaning t m 2027) (meaning t m 2688) (meaning t m 2952) (meaning t m 2992) (meaning t m 3286) (meaning t m 3680) (meaning t m 4039) source

theorem rule30721 (p1987 p2027 p2169 p2589 p2662 p2810 p3989 p4110 : Prop) (h : p2027 ∨ (¬ p4110) ∨ (¬ p3989) ∨ (¬ p2589) ∨ (¬ p1987) ∨ (¬ p2662) ∨ p2169 ∨ (¬ p2810)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3989) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial30721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory19977 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule30721 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2589) (meaning t m 2662) (meaning t m 2810) (meaning t m 3989) (meaning t m 4110) source

theorem rule30730 (p1992 p2027 p2202 p2437 p2440 p2608 p2927 p4366 : Prop) (h : (¬ p4366) ∨ p2202 ∨ (¬ p2927) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2440) ∨ (¬ p2437)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2608) ∨ (¬ p2927) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial30730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory19986 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule30730 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2437) (meaning t m 2440) (meaning t m 2608) (meaning t m 2927) (meaning t m 4366) source

theorem rule30731 (p1983 p2027 p2611 p2685 p2946 p3246 p4117 p4315 p4333 : Prop) (h : (¬ p2946) ∨ p2611 ∨ p2027 ∨ (¬ p4315) ∨ (¬ p1983) ∨ (¬ p2685) ∨ (¬ p4117) ∨ (¬ p3246) ∨ (¬ p4333)) : (¬ p1983) ∨ (p2027) ∨ (p2611) ∨ (¬ p2685) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4333) := by
  classical
  tauto

theorem initial30731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4333)) := by
  have source := ElevenTheory.theory19987 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule30731 (meaning t m 1983) (meaning t m 2027) (meaning t m 2611) (meaning t m 2685) (meaning t m 2946) (meaning t m 3246) (meaning t m 4117) (meaning t m 4315) (meaning t m 4333) source

theorem rule30733 (p2027 p2247 p2459 p2881 p3051 p3359 p4111 p4521 p4697 : Prop) (h : (¬ p2247) ∨ (¬ p2459) ∨ (¬ p4111) ∨ (¬ p2881) ∨ (¬ p4697) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4521) ∨ (¬ p3359)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p4521) ∨ (¬ p4697) := by
  classical
  tauto

theorem initial30733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4697)) := by
  have source := ElevenTheory.theory19989 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule30733 (meaning t m 2027) (meaning t m 2247) (meaning t m 2459) (meaning t m 2881) (meaning t m 3051) (meaning t m 3359) (meaning t m 4111) (meaning t m 4521) (meaning t m 4697) source

theorem rule30734 (p2264 p2341 p3032 p3543 : Prop) (h : (¬ p2341) ∨ (¬ p3543) ∨ (¬ p3032) ∨ p2264) : (p2264) ∨ (¬ p2341) ∨ (¬ p3032) ∨ (¬ p3543) := by
  classical
  tauto

theorem initial30734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2264) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3543)) := by
  have source := ElevenTheory.theory19990 (m.theta 0 7) (m.theta 1 7) (m.theta 3 7) (m.theta 7 8)
  exact rule30734 (meaning t m 2264) (meaning t m 2341) (meaning t m 3032) (meaning t m 3543) source

theorem rule30739 (p2027 p2132 p2657 p2870 p3246 p3644 p3742 p4668 p4789 : Prop) (h : (¬ p2657) ∨ (¬ p3246) ∨ (¬ p2870) ∨ (¬ p3742) ∨ (¬ p4789) ∨ p2027 ∨ (¬ p4668) ∨ (¬ p3644) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2657) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4668) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial30739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory19995 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule30739 (meaning t m 2027) (meaning t m 2132) (meaning t m 2657) (meaning t m 2870) (meaning t m 3246) (meaning t m 3644) (meaning t m 3742) (meaning t m 4668) (meaning t m 4789) source

theorem rule30741 (p2027 p2751 p2951 p2992 p3051 p3246 p3266 p3440 p3877 p3950 p4288 p4321 : Prop) (h : (¬ p3950) ∨ (¬ p2751) ∨ (¬ p3246) ∨ (¬ p3877) ∨ (¬ p4288) ∨ (¬ p4321) ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p3266) ∨ (¬ p2951) ∨ p2027 ∨ (¬ p3440)) : (p2027) ∨ (¬ p2751) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3266) ∨ (¬ p3440) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4288) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial30741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3440)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4288)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory19997 t (m.theta 0 5) (m.theta 1 3) (m.theta 1 8) (m.theta 1 9) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30741 (meaning t m 2027) (meaning t m 2751) (meaning t m 2951) (meaning t m 2992) (meaning t m 3051) (meaning t m 3246) (meaning t m 3266) (meaning t m 3440) (meaning t m 3877) (meaning t m 3950) (meaning t m 4288) (meaning t m 4321) source

theorem rule30746 (p2245 p3037 p3414 p4366 : Prop) (h : (¬ p3037) ∨ (¬ p2245) ∨ (¬ p3414) ∨ p4366) : (¬ p2245) ∨ (¬ p3037) ∨ (¬ p3414) ∨ (p4366) := by
  classical
  tauto

theorem initial30746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3414)) ∨ (meaning t m 4366) := by
  have source := ElevenTheory.theory20002 (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 3 7)
  exact rule30746 (meaning t m 2245) (meaning t m 3037) (meaning t m 3414) (meaning t m 4366) source

theorem rule30747 (p2027 p2656 p3136 p3516 p4324 p4357 p4704 p5201 : Prop) (h : p2027 ∨ (¬ p3136) ∨ (¬ p4357) ∨ (¬ p5201) ∨ (¬ p2656) ∨ (¬ p3516) ∨ (¬ p4324) ∨ (¬ p4704)) : (p2027) ∨ (¬ p2656) ∨ (¬ p3136) ∨ (¬ p3516) ∨ (¬ p4324) ∨ (¬ p4357) ∨ (¬ p4704) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial30747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4357)) ∨ (¬ (meaning t m 4704)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory20003 t (m.theta 0 4) (m.theta 0 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 5) (m.theta 7 9)
  exact rule30747 (meaning t m 2027) (meaning t m 2656) (meaning t m 3136) (meaning t m 3516) (meaning t m 4324) (meaning t m 4357) (meaning t m 4704) (meaning t m 5201) source

theorem rule30749 (p2027 p2598 p2717 p3097 p3555 p3644 p4173 p4276 p4733 p5085 : Prop) (h : p2027 ∨ (¬ p3555) ∨ (¬ p4276) ∨ (¬ p3097) ∨ (¬ p2598) ∨ (¬ p3644) ∨ (¬ p4173) ∨ (¬ p5085) ∨ (¬ p2717) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2717) ∨ (¬ p3097) ∨ (¬ p3555) ∨ (¬ p3644) ∨ (¬ p4173) ∨ (¬ p4276) ∨ (¬ p4733) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial30749 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory20005 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule30749 (meaning t m 2027) (meaning t m 2598) (meaning t m 2717) (meaning t m 3097) (meaning t m 3555) (meaning t m 3644) (meaning t m 4173) (meaning t m 4276) (meaning t m 4733) (meaning t m 5085) source

theorem rule30753 (p2027 p2807 p2881 p3172 p4280 p4548 : Prop) (h : p2027 ∨ (¬ p4280) ∨ (¬ p2881) ∨ (¬ p2807) ∨ (¬ p4548) ∨ (¬ p3172)) : (p2027) ∨ (¬ p2807) ∨ (¬ p2881) ∨ (¬ p3172) ∨ (¬ p4280) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial30753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4280)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory20009 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8)
  exact rule30753 (meaning t m 2027) (meaning t m 2807) (meaning t m 2881) (meaning t m 3172) (meaning t m 4280) (meaning t m 4548) source

theorem rule30756 (p2027 p2248 p2396 p2651 p2685 p2810 p3817 p4366 p4570 : Prop) (h : (¬ p2685) ∨ p2027 ∨ (¬ p3817) ∨ (¬ p4570) ∨ (¬ p2248) ∨ (¬ p4366) ∨ (¬ p2396) ∨ (¬ p2651) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2396) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial30756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory20012 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule30756 (meaning t m 2027) (meaning t m 2248) (meaning t m 2396) (meaning t m 2651) (meaning t m 2685) (meaning t m 2810) (meaning t m 3817) (meaning t m 4366) (meaning t m 4570) source

theorem rule30761 (p2027 p2341 p3588 p3659 p4104 p4117 p4737 : Prop) (h : (¬ p2341) ∨ (¬ p4104) ∨ (¬ p4737) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p4117) ∨ p2027) : (p2027) ∨ (¬ p2341) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p4104) ∨ (¬ p4117) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial30761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory20017 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 2 7) (m.theta 7 8)
  exact rule30761 (meaning t m 2027) (meaning t m 2341) (meaning t m 3588) (meaning t m 3659) (meaning t m 4104) (meaning t m 4117) (meaning t m 4737) source

theorem rule30765 (p1986 p2699 p3093 p3367 p4866 : Prop) (h : (¬ p3367) ∨ (¬ p1986) ∨ p2699 ∨ (¬ p3093) ∨ p4866) : (¬ p1986) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3367) ∨ (p4866) := by
  classical
  tauto

theorem initial30765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3367)) ∨ (meaning t m 4866) := by
  have source := ElevenTheory.theory20021 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4)
  exact rule30765 (meaning t m 1986) (meaning t m 2699) (meaning t m 3093) (meaning t m 3367) (meaning t m 4866) source

theorem rule30766 (p1983 p2027 p2323 p2331 p2449 p3027 p4154 : Prop) (h : p2323 ∨ (¬ p2449) ∨ (¬ p2331) ∨ (¬ p3027) ∨ (¬ p1983) ∨ p2027 ∨ (¬ p4154)) : (¬ p1983) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial30766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory20022 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 9)
  exact rule30766 (meaning t m 1983) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 2449) (meaning t m 3027) (meaning t m 4154) source

theorem rule30767 (p1992 p2027 p2202 p2563 p2598 p2780 p3585 p4428 : Prop) (h : (¬ p3585) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p2563) ∨ (¬ p4428) ∨ p2202 ∨ (¬ p2598)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3585) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial30767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory20023 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6)
  exact rule30767 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2598) (meaning t m 2780) (meaning t m 3585) (meaning t m 4428) source

theorem rule30769 (p1982 p2027 p2470 p2528 p2545 p2579 p3016 : Prop) (h : (¬ p1982) ∨ (¬ p2528) ∨ p2545 ∨ (¬ p2579) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p3016)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (p2545) ∨ (¬ p2579) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial30769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory20025 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule30769 (meaning t m 1982) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2545) (meaning t m 2579) (meaning t m 3016) source

theorem rule30771 (p1991 p2027 p2765 p2952 p3105 p3758 p4208 : Prop) (h : (¬ p3758) ∨ (¬ p4208) ∨ (¬ p3105) ∨ (¬ p2952) ∨ p2027 ∨ p2765 ∨ (¬ p1991)) : (¬ p1991) ∨ (p2027) ∨ (p2765) ∨ (¬ p2952) ∨ (¬ p3105) ∨ (¬ p3758) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial30771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory20027 t (m.theta 0 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9)
  exact rule30771 (meaning t m 1991) (meaning t m 2027) (meaning t m 2765) (meaning t m 2952) (meaning t m 3105) (meaning t m 3758) (meaning t m 4208) source

theorem rule30772 (p2027 p3550 p3609 p4347 p4423 p4805 p5559 : Prop) (h : (¬ p5559) ∨ (¬ p4347) ∨ (¬ p4423) ∨ (¬ p4805) ∨ (¬ p3550) ∨ p2027 ∨ (¬ p3609)) : (p2027) ∨ (¬ p3550) ∨ (¬ p3609) ∨ (¬ p4347) ∨ (¬ p4423) ∨ (¬ p4805) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial30772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4423)) ∨ (¬ (meaning t m 4805)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory20028 t (m.theta 2 7) (m.theta 2 8) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule30772 (meaning t m 2027) (meaning t m 3550) (meaning t m 3609) (meaning t m 4347) (meaning t m 4423) (meaning t m 4805) (meaning t m 5559) source

theorem rule30773 (p1997 p2027 p2230 p2881 p2933 p2938 p3540 p3548 : Prop) (h : (¬ p2881) ∨ p2938 ∨ p2027 ∨ (¬ p3540) ∨ (¬ p3548) ∨ (¬ p1997) ∨ (¬ p2933) ∨ (¬ p2230)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2881) ∨ (¬ p2933) ∨ (p2938) ∨ (¬ p3540) ∨ (¬ p3548) := by
  classical
  tauto

theorem initial30773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2933)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3548)) := by
  have source := ElevenTheory.theory20029 t (m.theta 0 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule30773 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2881) (meaning t m 2933) (meaning t m 2938) (meaning t m 3540) (meaning t m 3548) source

theorem rule30776 (p2027 p3266 p3333 p3379 p3954 p4030 p4322 p4332 p4363 p4877 : Prop) (h : (¬ p3266) ∨ (¬ p4332) ∨ (¬ p4877) ∨ (¬ p4363) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p3333) ∨ (¬ p3379) ∨ (¬ p4030) ∨ (¬ p3954)) : (p2027) ∨ (¬ p3266) ∨ (¬ p3333) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4322) ∨ (¬ p4332) ∨ (¬ p4363) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial30776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory20032 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 9) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30776 (meaning t m 2027) (meaning t m 3266) (meaning t m 3333) (meaning t m 3379) (meaning t m 3954) (meaning t m 4030) (meaning t m 4322) (meaning t m 4332) (meaning t m 4363) (meaning t m 4877) source

theorem rule30778 (p1987 p2027 p2406 p2611 p2774 p3364 p3541 p3684 p3688 : Prop) (h : (¬ p2774) ∨ (¬ p3688) ∨ p2027 ∨ (¬ p1987) ∨ p2611 ∨ (¬ p3364) ∨ (¬ p3684) ∨ (¬ p3541) ∨ (¬ p2406)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2406) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p3364) ∨ (¬ p3541) ∨ (¬ p3684) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial30778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory20034 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5)
  exact rule30778 (meaning t m 1987) (meaning t m 2027) (meaning t m 2406) (meaning t m 2611) (meaning t m 2774) (meaning t m 3364) (meaning t m 3541) (meaning t m 3684) (meaning t m 3688) source

theorem rule30780 (p2027 p2088 p3646 p3692 p4238 p4509 : Prop) (h : (¬ p4509) ∨ (¬ p3646) ∨ (¬ p2088) ∨ (¬ p3692) ∨ (¬ p4238) ∨ p2027) : (p2027) ∨ (¬ p2088) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p4238) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial30780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4238)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory20036 t (m.theta 0 5) (m.theta 0 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule30780 (meaning t m 2027) (meaning t m 2088) (meaning t m 3646) (meaning t m 3692) (meaning t m 4238) (meaning t m 4509) source

theorem rule30785 (p2027 p2248 p2295 p2331 p3193 p3452 p3791 p4425 p4826 : Prop) (h : (¬ p3452) ∨ (¬ p3193) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p4425) ∨ (¬ p2295) ∨ (¬ p2248) ∨ (¬ p4826) ∨ (¬ p3791)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p3791) ∨ (¬ p4425) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial30785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory20041 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule30785 (meaning t m 2027) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 3193) (meaning t m 3452) (meaning t m 3791) (meaning t m 4425) (meaning t m 4826) source

theorem rule30786 (p1994 p2027 p2427 p2651 p2765 p2950 p3556 p4110 : Prop) (h : (¬ p2950) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p2651) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p4110) ∨ p2765) : (¬ p1994) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2651) ∨ (p2765) ∨ (¬ p2950) ∨ (¬ p3556) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial30786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory20042 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule30786 (meaning t m 1994) (meaning t m 2027) (meaning t m 2427) (meaning t m 2651) (meaning t m 2765) (meaning t m 2950) (meaning t m 3556) (meaning t m 4110) source

theorem rule30793 (p2027 p2187 p2192 p2210 p3365 p3568 p4195 p4405 p4736 : Prop) (h : (¬ p3568) ∨ (¬ p2210) ∨ (¬ p4195) ∨ (¬ p4405) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p2192) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4405) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial30793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory20049 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30793 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2210) (meaning t m 3365) (meaning t m 3568) (meaning t m 4195) (meaning t m 4405) (meaning t m 4736) source

theorem rule30800 (p2810 p3572 p4112 : Prop) (h : (¬ p4112) ∨ (¬ p2810) ∨ p3572) : (¬ p2810) ∨ (p3572) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial30800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2810)) ∨ (meaning t m 3572) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory20056 (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule30800 (meaning t m 2810) (meaning t m 3572) (meaning t m 4112) source

theorem rule30802 (p1982 p2027 p2363 p2383 p2779 p2829 p3474 p3583 : Prop) (h : (¬ p2363) ∨ (¬ p1982) ∨ p2027 ∨ p3474 ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p2779) ∨ (¬ p2383)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (p3474) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial30802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory20058 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule30802 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 2779) (meaning t m 2829) (meaning t m 3474) (meaning t m 3583) source

theorem rule30807 (p2027 p2132 p2245 p2870 p2963 p3246 p3324 p3950 p4347 p4733 : Prop) (h : (¬ p3324) ∨ (¬ p4347) ∨ (¬ p2963) ∨ (¬ p3950) ∨ (¬ p2245) ∨ (¬ p4733) ∨ (¬ p2870) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2870) ∨ (¬ p2963) ∨ (¬ p3246) ∨ (¬ p3324) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial30807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory20063 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule30807 (meaning t m 2027) (meaning t m 2132) (meaning t m 2245) (meaning t m 2870) (meaning t m 2963) (meaning t m 3246) (meaning t m 3324) (meaning t m 3950) (meaning t m 4347) (meaning t m 4733) source

theorem rule30810 (p2027 p2138 p2573 p3367 p3564 p3690 p3759 p4244 p4621 p4734 : Prop) (h : (¬ p2138) ∨ (¬ p3759) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p4621) ∨ (¬ p4734) ∨ (¬ p4244) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p3564)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3564) ∨ (¬ p3690) ∨ (¬ p3759) ∨ (¬ p4244) ∨ (¬ p4621) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial30810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory20066 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule30810 (meaning t m 2027) (meaning t m 2138) (meaning t m 2573) (meaning t m 3367) (meaning t m 3564) (meaning t m 3690) (meaning t m 3759) (meaning t m 4244) (meaning t m 4621) (meaning t m 4734) source

theorem rule30811 (p2027 p2996 p3644 p3842 p4349 p4378 p4653 : Prop) (h : (¬ p4349) ∨ (¬ p3842) ∨ (¬ p4653) ∨ (¬ p4378) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2996) ∨ (¬ p3644) ∨ (¬ p3842) ∨ (¬ p4349) ∨ (¬ p4378) ∨ (¬ p4653) := by
  classical
  tauto

theorem initial30811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4349)) ∨ (¬ (meaning t m 4378)) ∨ (¬ (meaning t m 4653)) := by
  have source := ElevenTheory.theory20067 t (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 3 9) (m.theta 4 7) (m.theta 7 8)
  exact rule30811 (meaning t m 2027) (meaning t m 2996) (meaning t m 3644) (meaning t m 3842) (meaning t m 4349) (meaning t m 4378) (meaning t m 4653) source

theorem rule30812 (p1975 p2027 p2114 p2383 p2553 p2584 p3367 p3759 p3956 : Prop) (h : p2114 ∨ p2027 ∨ (¬ p3759) ∨ (¬ p2553) ∨ (¬ p3367) ∨ (¬ p1975) ∨ (¬ p2584) ∨ (¬ p3956) ∨ (¬ p2383)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2383) ∨ (¬ p2553) ∨ (¬ p2584) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial30812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory20068 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30812 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2383) (meaning t m 2553) (meaning t m 2584) (meaning t m 3367) (meaning t m 3759) (meaning t m 3956) source

theorem rule30814 (p2010 p2027 p2177 p2233 p2553 p2573 p3644 : Prop) (h : p2233 ∨ (¬ p2573) ∨ (¬ p2177) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p2010) ∨ (¬ p3644)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2177) ∨ (p2233) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial30814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory20070 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule30814 (meaning t m 2010) (meaning t m 2027) (meaning t m 2177) (meaning t m 2233) (meaning t m 2553) (meaning t m 2573) (meaning t m 3644) source

theorem rule30815 (p2027 p2299 p2573 p2737 p2911 p3365 p3588 p3873 p3920 p4477 p5190 : Prop) (h : (¬ p3588) ∨ (¬ p5190) ∨ (¬ p2911) ∨ (¬ p2573) ∨ (¬ p4477) ∨ p2027 ∨ (¬ p3920) ∨ (¬ p2299) ∨ (¬ p2737) ∨ (¬ p3873) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2573) ∨ (¬ p2737) ∨ (¬ p2911) ∨ (¬ p3365) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p3920) ∨ (¬ p4477) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial30815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4477)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory20071 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule30815 (meaning t m 2027) (meaning t m 2299) (meaning t m 2573) (meaning t m 2737) (meaning t m 2911) (meaning t m 3365) (meaning t m 3588) (meaning t m 3873) (meaning t m 3920) (meaning t m 4477) (meaning t m 5190) source

theorem rule30825 (p2027 p2331 p2589 p3692 p3755 p3880 p4117 p4195 p4729 p5109 : Prop) (h : (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4729) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p5109) ∨ (¬ p4195)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3692) ∨ (¬ p3755) ∨ (¬ p3880) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4729) ∨ (¬ p5109) := by
  classical
  tauto

theorem initial30825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5109)) := by
  have source := ElevenTheory.theory20081 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule30825 (meaning t m 2027) (meaning t m 2331) (meaning t m 2589) (meaning t m 3692) (meaning t m 3755) (meaning t m 3880) (meaning t m 4117) (meaning t m 4195) (meaning t m 4729) (meaning t m 5109) source

theorem rule30826 (p2027 p2589 p3166 p3256 p3570 p4117 p4133 p4235 p4347 p4729 : Prop) (h : (¬ p4133) ∨ (¬ p3256) ∨ (¬ p4235) ∨ (¬ p4729) ∨ (¬ p3570) ∨ (¬ p4347) ∨ (¬ p2589) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p3166)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3570) ∨ (¬ p4117) ∨ (¬ p4133) ∨ (¬ p4235) ∨ (¬ p4347) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial30826 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory20082 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule30826 (meaning t m 2027) (meaning t m 2589) (meaning t m 3166) (meaning t m 3256) (meaning t m 3570) (meaning t m 4117) (meaning t m 4133) (meaning t m 4235) (meaning t m 4347) (meaning t m 4729) source

theorem rule30827 (p1998 p2027 p2177 p2323 p2331 p2685 p3552 p4195 : Prop) (h : (¬ p3552) ∨ p2323 ∨ (¬ p4195) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2685) ∨ (¬ p2331) ∨ (¬ p2177)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2685) ∨ (¬ p3552) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial30827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory20083 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule30827 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2323) (meaning t m 2331) (meaning t m 2685) (meaning t m 3552) (meaning t m 4195) source

theorem rule30829 (p2027 p2210 p2972 p3266 p3346 p3347 p3954 p4425 p4450 p5216 : Prop) (h : (¬ p2972) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p3347) ∨ (¬ p5216) ∨ (¬ p4425) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3954) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2972) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p4425) ∨ (¬ p4450) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial30829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory20085 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 9) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30829 (meaning t m 2027) (meaning t m 2210) (meaning t m 2972) (meaning t m 3266) (meaning t m 3346) (meaning t m 3347) (meaning t m 3954) (meaning t m 4425) (meaning t m 4450) (meaning t m 5216) source

theorem rule30830 (p1991 p2027 p2169 p2363 p2952 p3497 p3692 : Prop) (h : p2169 ∨ (¬ p1991) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p3692)) : (¬ p1991) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial30830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory20086 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule30830 (meaning t m 1991) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2952) (meaning t m 3497) (meaning t m 3692) source

theorem rule30834 (p2027 p2246 p2437 p2608 p2651 p2744 p3834 p3868 p4321 p4826 : Prop) (h : (¬ p3868) ∨ (¬ p4826) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2608) ∨ (¬ p3834) ∨ (¬ p4321) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3834) ∨ (¬ p3868) ∨ (¬ p4321) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial30834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory20090 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 3 4) (m.theta 4 7) (m.theta 7 10) (m.theta 9 10)
  exact rule30834 (meaning t m 2027) (meaning t m 2246) (meaning t m 2437) (meaning t m 2608) (meaning t m 2651) (meaning t m 2744) (meaning t m 3834) (meaning t m 3868) (meaning t m 4321) (meaning t m 4826) source

theorem rule30835 (p2027 p2630 p2657 p2745 p2946 p3662 : Prop) (h : p2027 ∨ (¬ p2657) ∨ (¬ p2630) ∨ (¬ p2946) ∨ (¬ p2745) ∨ (¬ p3662)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2745) ∨ (¬ p2946) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial30835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory20091 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule30835 (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 2745) (meaning t m 2946) (meaning t m 3662) source

theorem rule30836 (p1981 p2027 p2274 p2313 p2765 p3998 p4114 p5580 : Prop) (h : p2765 ∨ p2027 ∨ (¬ p2313) ∨ (¬ p3998) ∨ (¬ p4114) ∨ (¬ p2274) ∨ (¬ p1981) ∨ (¬ p5580)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (p2765) ∨ (¬ p3998) ∨ (¬ p4114) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial30836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory20092 t (m.theta 0 6) (m.theta 0 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule30836 (meaning t m 1981) (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2765) (meaning t m 3998) (meaning t m 4114) (meaning t m 5580) source

theorem rule30838 (p3093 p3449 p4371 : Prop) (h : (¬ p3449) ∨ (¬ p4371) ∨ p3093) : (p3093) ∨ (¬ p3449) ∨ (¬ p4371) := by
  classical
  tauto

theorem initial30838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3093) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4371)) := by
  have source := ElevenTheory.theory20094 (m.theta 0 1) (m.theta 1 6) (m.theta 1 8)
  exact rule30838 (meaning t m 3093) (meaning t m 3449) (meaning t m 4371) source

theorem rule30839 (p2027 p2132 p2313 p2753 p3105 p3204 p3644 p3680 p4710 p4870 p5123 p5558 : Prop) (h : (¬ p3680) ∨ (¬ p5558) ∨ (¬ p4870) ∨ (¬ p3204) ∨ (¬ p5123) ∨ (¬ p4710) ∨ (¬ p3644) ∨ (¬ p2753) ∨ (¬ p2313) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p3105)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2313) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p3204) ∨ (¬ p3644) ∨ (¬ p3680) ∨ (¬ p4710) ∨ (¬ p4870) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial30839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory20095 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 5) (m.theta 4 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule30839 (meaning t m 2027) (meaning t m 2132) (meaning t m 2313) (meaning t m 2753) (meaning t m 3105) (meaning t m 3204) (meaning t m 3644) (meaning t m 3680) (meaning t m 4710) (meaning t m 4870) (meaning t m 5123) (meaning t m 5558) source

theorem rule30840 (p2027 p3073 p3365 p3366 p3449 p3452 p4037 p4195 p4376 p4604 : Prop) (h : (¬ p4037) ∨ (¬ p3073) ∨ (¬ p4604) ∨ (¬ p3452) ∨ (¬ p3449) ∨ (¬ p4195) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p4376)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4376) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial30840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory20096 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 8 9)
  exact rule30840 (meaning t m 2027) (meaning t m 3073) (meaning t m 3365) (meaning t m 3366) (meaning t m 3449) (meaning t m 3452) (meaning t m 4037) (meaning t m 4195) (meaning t m 4376) (meaning t m 4604) source

theorem rule30841 (p1997 p2027 p2169 p2295 p2313 p3324 p4110 p4356 : Prop) (h : (¬ p4356) ∨ (¬ p4110) ∨ (¬ p3324) ∨ (¬ p1997) ∨ (¬ p2313) ∨ p2169 ∨ p2027 ∨ (¬ p2295)) : (¬ p1997) ∨ (p2027) ∨ (p2169) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3324) ∨ (¬ p4110) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial30841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory20097 t (m.theta 0 6) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30841 (meaning t m 1997) (meaning t m 2027) (meaning t m 2169) (meaning t m 2295) (meaning t m 2313) (meaning t m 3324) (meaning t m 4110) (meaning t m 4356) source

theorem rule30845 (p3475 p3572 p3759 p4155 p5201 : Prop) (h : (¬ p4155) ∨ (¬ p3759) ∨ (¬ p3572) ∨ (¬ p5201) ∨ (¬ p3475)) : (¬ p3475) ∨ (¬ p3572) ∨ (¬ p3759) ∨ (¬ p4155) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial30845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory20101 (m.theta 0 4) (m.theta 0 7) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7)
  exact rule30845 (meaning t m 3475) (meaning t m 3572) (meaning t m 3759) (meaning t m 4155) (meaning t m 5201) source

theorem rule30852 (p2027 p2542 p2589 p2928 p3389 p4811 : Prop) (h : (¬ p4811) ∨ (¬ p2542) ∨ (¬ p2928) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p3389)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial30852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory20108 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule30852 (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 2928) (meaning t m 3389) (meaning t m 4811) source

theorem rule30853 (p2027 p2363 p2542 p2589 p2655 p2774 p2819 p3359 p4697 p4789 : Prop) (h : (¬ p2655) ∨ (¬ p2589) ∨ (¬ p4697) ∨ (¬ p3359) ∨ (¬ p2542) ∨ (¬ p2819) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p4789) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3359) ∨ (¬ p4697) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial30853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory20109 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule30853 (meaning t m 2027) (meaning t m 2363) (meaning t m 2542) (meaning t m 2589) (meaning t m 2655) (meaning t m 2774) (meaning t m 2819) (meaning t m 3359) (meaning t m 4697) (meaning t m 4789) source

theorem rule30854 (p2027 p2254 p2608 p2829 p2952 p3483 p3497 p3692 p4330 : Prop) (h : (¬ p2952) ∨ (¬ p3692) ∨ (¬ p2254) ∨ (¬ p4330) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3497) ∨ (¬ p3483)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p2952) ∨ (¬ p3483) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial30854 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory20110 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule30854 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2829) (meaning t m 2952) (meaning t m 3483) (meaning t m 3497) (meaning t m 3692) (meaning t m 4330) source

theorem rule30856 (p2027 p2254 p2363 p2589 p2655 p3063 p3093 p3690 p4241 p4320 p4669 : Prop) (h : (¬ p4669) ∨ (¬ p3690) ∨ (¬ p2589) ∨ (¬ p4320) ∨ (¬ p3063) ∨ (¬ p4241) ∨ p2027 ∨ (¬ p2655) ∨ (¬ p2363) ∨ (¬ p2254) ∨ (¬ p3093)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3690) ∨ (¬ p4241) ∨ (¬ p4320) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial30856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory20112 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 6) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule30856 (meaning t m 2027) (meaning t m 2254) (meaning t m 2363) (meaning t m 2589) (meaning t m 2655) (meaning t m 3063) (meaning t m 3093) (meaning t m 3690) (meaning t m 4241) (meaning t m 4320) (meaning t m 4669) source

theorem rule30857 (p2027 p2499 p2573 p2870 p3222 p3556 p4079 p4385 p4524 p4950 : Prop) (h : (¬ p2499) ∨ (¬ p4950) ∨ (¬ p4385) ∨ (¬ p3556) ∨ (¬ p2870) ∨ (¬ p3222) ∨ (¬ p2573) ∨ (¬ p4524) ∨ p2027 ∨ (¬ p4079)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2870) ∨ (¬ p3222) ∨ (¬ p3556) ∨ (¬ p4079) ∨ (¬ p4385) ∨ (¬ p4524) ∨ (¬ p4950) := by
  classical
  tauto

theorem initial30857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4950)) := by
  have source := ElevenTheory.theory20113 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 4 9) (m.theta 5 7) (m.theta 5 9)
  exact rule30857 (meaning t m 2027) (meaning t m 2499) (meaning t m 2573) (meaning t m 2870) (meaning t m 3222) (meaning t m 3556) (meaning t m 4079) (meaning t m 4385) (meaning t m 4524) (meaning t m 4950) source

theorem rule30858 (p2027 p2254 p2608 p2829 p3172 p3914 p4118 p4444 p5250 : Prop) (h : (¬ p2254) ∨ (¬ p5250) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p4444) ∨ (¬ p3172) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3914)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3172) ∨ (¬ p3914) ∨ (¬ p4118) ∨ (¬ p4444) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial30858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory20114 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 8) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule30858 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2829) (meaning t m 3172) (meaning t m 3914) (meaning t m 4118) (meaning t m 4444) (meaning t m 5250) source

theorem rule30859 (p1975 p2027 p2233 p2274 p2470 p2493 p2509 p4203 : Prop) (h : (¬ p1975) ∨ (¬ p2470) ∨ (¬ p2493) ∨ p2027 ∨ (¬ p2274) ∨ p2233 ∨ (¬ p4203) ∨ (¬ p2509)) : (¬ p1975) ∨ (p2027) ∨ (p2233) ∨ (¬ p2274) ∨ (¬ p2470) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial30859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory20115 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7)
  exact rule30859 (meaning t m 1975) (meaning t m 2027) (meaning t m 2233) (meaning t m 2274) (meaning t m 2470) (meaning t m 2493) (meaning t m 2509) (meaning t m 4203) source

theorem rule30862 (p2027 p2132 p2743 p2963 p3073 p3324 p3361 p3692 p4418 p4433 p4496 p4737 : Prop) (h : (¬ p3692) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p4433) ∨ (¬ p4496) ∨ (¬ p3073) ∨ (¬ p2743) ∨ (¬ p4737) ∨ (¬ p4418) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3073) ∨ (¬ p3324) ∨ (¬ p3361) ∨ (¬ p3692) ∨ (¬ p4418) ∨ (¬ p4433) ∨ (¬ p4496) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial30862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4496)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory20118 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule30862 (meaning t m 2027) (meaning t m 2132) (meaning t m 2743) (meaning t m 2963) (meaning t m 3073) (meaning t m 3324) (meaning t m 3361) (meaning t m 3692) (meaning t m 4418) (meaning t m 4433) (meaning t m 4496) (meaning t m 4737) source

theorem rule30865 (p2027 p2254 p2588 p2608 p2657 p2819 p2829 p3574 p4405 : Prop) (h : (¬ p3574) ∨ (¬ p2829) ∨ (¬ p2657) ∨ (¬ p2819) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p2254) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2588) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3574) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial30865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory20121 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30865 (meaning t m 2027) (meaning t m 2254) (meaning t m 2588) (meaning t m 2608) (meaning t m 2657) (meaning t m 2819) (meaning t m 2829) (meaning t m 3574) (meaning t m 4405) source

theorem rule30868 (p1995 p2027 p2881 p2927 p2938 p3379 p3644 p4366 : Prop) (h : p2938 ∨ (¬ p2881) ∨ (¬ p2927) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p3379) ∨ (¬ p1995) ∨ (¬ p3644)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2881) ∨ (¬ p2927) ∨ (p2938) ∨ (¬ p3379) ∨ (¬ p3644) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial30868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2927)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory20124 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule30868 (meaning t m 1995) (meaning t m 2027) (meaning t m 2881) (meaning t m 2927) (meaning t m 2938) (meaning t m 3379) (meaning t m 3644) (meaning t m 4366) source

theorem rule30872 (p2027 p2363 p3063 p3692 p3988 p4518 : Prop) (h : (¬ p4518) ∨ (¬ p3692) ∨ (¬ p2363) ∨ (¬ p3988) ∨ (¬ p3063) ∨ p2027) : (p2027) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4518) := by
  classical
  tauto

theorem initial30872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4518)) := by
  have source := ElevenTheory.theory20128 t (m.theta 1 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule30872 (meaning t m 2027) (meaning t m 2363) (meaning t m 3063) (meaning t m 3692) (meaning t m 3988) (meaning t m 4518) source

theorem rule30873 (p2027 p2707 p3585 p3658 p3684 p4646 : Prop) (h : p2027 ∨ (¬ p3585) ∨ (¬ p4646) ∨ (¬ p3684) ∨ (¬ p3658) ∨ (¬ p2707)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p3684) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial30873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory20129 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7)
  exact rule30873 (meaning t m 2027) (meaning t m 2707) (meaning t m 3585) (meaning t m 3658) (meaning t m 3684) (meaning t m 4646) source

theorem rule30874 (p2027 p2284 p2946 p3055 p3125 p3876 p4278 p4621 p4786 : Prop) (h : (¬ p3055) ∨ (¬ p3125) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p4621) ∨ (¬ p2946) ∨ (¬ p4786) ∨ (¬ p3876) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3125) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial30874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory20130 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule30874 (meaning t m 2027) (meaning t m 2284) (meaning t m 2946) (meaning t m 3055) (meaning t m 3125) (meaning t m 3876) (meaning t m 4278) (meaning t m 4621) (meaning t m 4786) source

theorem rule30876 (p2027 p2187 p2284 p2946 p3055 p3644 p3876 p4133 p4786 : Prop) (h : (¬ p3876) ∨ (¬ p4133) ∨ (¬ p3644) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p4786) ∨ (¬ p2946) ∨ (¬ p2284)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial30876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory20132 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule30876 (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 2946) (meaning t m 3055) (meaning t m 3644) (meaning t m 3876) (meaning t m 4133) (meaning t m 4786) source

theorem rule30879 (p2027 p2363 p3919 p3931 p4118 p4138 p5564 : Prop) (h : (¬ p3931) ∨ (¬ p4138) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p5564) ∨ (¬ p3919) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3919) ∨ (¬ p3931) ∨ (¬ p4118) ∨ (¬ p4138) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial30879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory20135 t (m.theta 3 7) (m.theta 3 8) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule30879 (meaning t m 2027) (meaning t m 2363) (meaning t m 3919) (meaning t m 3931) (meaning t m 4118) (meaning t m 4138) (meaning t m 5564) source

theorem rule30881 (p2027 p2230 p2247 p2373 p2608 p2742 p3146 p3519 p4035 p4376 p5113 : Prop) (h : (¬ p3146) ∨ (¬ p4035) ∨ (¬ p5113) ∨ (¬ p4376) ∨ (¬ p3519) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2742) ∨ (¬ p2608) ∨ (¬ p2373) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2373) ∨ (¬ p2608) ∨ (¬ p2742) ∨ (¬ p3146) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4376) ∨ (¬ p5113) := by
  classical
  tauto

theorem initial30881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5113)) := by
  have source := ElevenTheory.theory20137 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 9) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule30881 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2373) (meaning t m 2608) (meaning t m 2742) (meaning t m 3146) (meaning t m 3519) (meaning t m 4035) (meaning t m 4376) (meaning t m 5113) source

theorem rule30882 (p2027 p3093 p3319 p3365 p3366 p3452 p3572 p3947 p4376 p4621 : Prop) (h : (¬ p3093) ∨ (¬ p3572) ∨ (¬ p3319) ∨ (¬ p4621) ∨ (¬ p3366) ∨ (¬ p3947) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p4376) ∨ (¬ p3365)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4376) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial30882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory20138 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 6 9) (m.theta 7 9)
  exact rule30882 (meaning t m 2027) (meaning t m 3093) (meaning t m 3319) (meaning t m 3365) (meaning t m 3366) (meaning t m 3452) (meaning t m 3572) (meaning t m 3947) (meaning t m 4376) (meaning t m 4621) source

theorem rule30883 (p2027 p2995 p3931 p3952 p4558 p5660 : Prop) (h : (¬ p2995) ∨ (¬ p3931) ∨ (¬ p5660) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p3952)) : (p2027) ∨ (¬ p2995) ∨ (¬ p3931) ∨ (¬ p3952) ∨ (¬ p4558) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial30883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4558)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory20139 t (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 10)
  exact rule30883 (meaning t m 2027) (meaning t m 2995) (meaning t m 3931) (meaning t m 3952) (meaning t m 4558) (meaning t m 5660) source

theorem rule30884 (p2027 p2449 p3347 p3540 p3580 p3658 p4324 p4811 : Prop) (h : (¬ p2449) ∨ (¬ p3540) ∨ (¬ p3580) ∨ (¬ p4324) ∨ (¬ p3658) ∨ p2027 ∨ (¬ p4811) ∨ (¬ p3347)) : (p2027) ∨ (¬ p2449) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3580) ∨ (¬ p3658) ∨ (¬ p4324) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial30884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory20140 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule30884 (meaning t m 2027) (meaning t m 2449) (meaning t m 3347) (meaning t m 3540) (meaning t m 3580) (meaning t m 3658) (meaning t m 4324) (meaning t m 4811) source

theorem rule30886 (p1981 p2027 p2388 p3005 p3256 p4315 p4347 : Prop) (h : (¬ p1981) ∨ p2388 ∨ (¬ p4315) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3256) ∨ (¬ p3005)) : (¬ p1981) ∨ (p2027) ∨ (p2388) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p4315) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial30886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory20142 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule30886 (meaning t m 1981) (meaning t m 2027) (meaning t m 2388) (meaning t m 3005) (meaning t m 3256) (meaning t m 4315) (meaning t m 4347) source

theorem rule30891 (p1990 p2027 p2307 p2387 p3063 p3097 p3818 : Prop) (h : (¬ p1990) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p3097) ∨ p3818 ∨ (¬ p3063)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3063) ∨ (¬ p3097) ∨ (p3818) := by
  classical
  tauto

theorem initial30891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3097)) ∨ (meaning t m 3818) := by
  have source := ElevenTheory.theory20147 t (m.theta 0 6) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule30891 (meaning t m 1990) (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 3063) (meaning t m 3097) (meaning t m 3818) source

theorem rule30895 (p2027 p2331 p2668 p3425 p3979 p4324 p4381 p4786 p5119 : Prop) (h : (¬ p3979) ∨ (¬ p2668) ∨ (¬ p3425) ∨ (¬ p5119) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p2331) ∨ (¬ p4786) ∨ p2027) : (p2027) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3425) ∨ (¬ p3979) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4786) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial30895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory20151 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule30895 (meaning t m 2027) (meaning t m 2331) (meaning t m 2668) (meaning t m 3425) (meaning t m 3979) (meaning t m 4324) (meaning t m 4381) (meaning t m 4786) (meaning t m 5119) source

theorem rule30896 (p2027 p2331 p3425 p3506 p3659 p4421 p4786 p5117 p5558 : Prop) (h : (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4786) ∨ (¬ p4421) ∨ p2027 ∨ (¬ p3506) ∨ (¬ p2331) ∨ (¬ p5558) ∨ (¬ p5117)) : (p2027) ∨ (¬ p2331) ∨ (¬ p3425) ∨ (¬ p3506) ∨ (¬ p3659) ∨ (¬ p4421) ∨ (¬ p4786) ∨ (¬ p5117) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial30896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5117)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory20152 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 6) (m.theta 3 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule30896 (meaning t m 2027) (meaning t m 2331) (meaning t m 3425) (meaning t m 3506) (meaning t m 3659) (meaning t m 4421) (meaning t m 4786) (meaning t m 5117) (meaning t m 5558) source

theorem rule30897 (p2027 p2136 p2573 p3266 p3343 p3366 p3519 p3574 p4120 p4322 p4332 p4335 p4376 : Prop) (h : p2027 ∨ (¬ p4335) ∨ (¬ p4120) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p2573) ∨ (¬ p2136) ∨ (¬ p4322) ∨ (¬ p4332)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2573) ∨ (¬ p3266) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3574) ∨ (¬ p4120) ∨ (¬ p4322) ∨ (¬ p4332) ∨ (¬ p4335) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial30897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory20153 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30897 (meaning t m 2027) (meaning t m 2136) (meaning t m 2573) (meaning t m 3266) (meaning t m 3343) (meaning t m 3366) (meaning t m 3519) (meaning t m 3574) (meaning t m 4120) (meaning t m 4322) (meaning t m 4332) (meaning t m 4335) (meaning t m 4376) source

theorem rule30900 (p2027 p2253 p2274 p2641 p2780 p3166 p3822 p4360 p4564 p4736 : Prop) (h : p2027 ∨ (¬ p4736) ∨ (¬ p2253) ∨ (¬ p3166) ∨ (¬ p2274) ∨ (¬ p4360) ∨ (¬ p4564) ∨ (¬ p2641) ∨ (¬ p3822) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2274) ∨ (¬ p2641) ∨ (¬ p2780) ∨ (¬ p3166) ∨ (¬ p3822) ∨ (¬ p4360) ∨ (¬ p4564) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial30900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4564)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory20156 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 6) (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7)
  exact rule30900 (meaning t m 2027) (meaning t m 2253) (meaning t m 2274) (meaning t m 2641) (meaning t m 2780) (meaning t m 3166) (meaning t m 3822) (meaning t m 4360) (meaning t m 4564) (meaning t m 4736) source

theorem rule30901 (p1984 p2027 p2901 p3043 p3486 p3555 p4208 : Prop) (h : (¬ p3486) ∨ (¬ p2901) ∨ p2027 ∨ p3043 ∨ (¬ p3555) ∨ (¬ p1984) ∨ (¬ p4208)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2901) ∨ (p3043) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial30901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory20157 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 9)
  exact rule30901 (meaning t m 1984) (meaning t m 2027) (meaning t m 2901) (meaning t m 3043) (meaning t m 3486) (meaning t m 3555) (meaning t m 4208) source

theorem rule30902 (p1983 p2027 p2341 p2417 p2622 p2630 p3519 p3644 p4116 p5201 : Prop) (h : (¬ p1983) ∨ (¬ p5201) ∨ (¬ p4116) ∨ p2027 ∨ (¬ p3519) ∨ p2622 ∨ (¬ p2630) ∨ (¬ p2341) ∨ (¬ p2417) ∨ (¬ p3644)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2417) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p3519) ∨ (¬ p3644) ∨ (¬ p4116) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial30902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory20158 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule30902 (meaning t m 1983) (meaning t m 2027) (meaning t m 2341) (meaning t m 2417) (meaning t m 2622) (meaning t m 2630) (meaning t m 3519) (meaning t m 3644) (meaning t m 4116) (meaning t m 5201) source

theorem rule30903 (p2027 p3037 p3414 p3434 p3817 p4781 p4787 : Prop) (h : (¬ p3817) ∨ (¬ p4787) ∨ (¬ p3414) ∨ (¬ p3037) ∨ p2027 ∨ (¬ p4781) ∨ (¬ p3434)) : (p2027) ∨ (¬ p3037) ∨ (¬ p3414) ∨ (¬ p3434) ∨ (¬ p3817) ∨ (¬ p4781) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial30903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4781)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory20159 t (m.theta 0 3) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 9)
  exact rule30903 (meaning t m 2027) (meaning t m 3037) (meaning t m 3414) (meaning t m 3434) (meaning t m 3817) (meaning t m 4781) (meaning t m 4787) source

theorem rule30905 (p2027 p3276 p3552 p3956 p4422 p4429 p4501 p5284 : Prop) (h : (¬ p4422) ∨ p2027 ∨ (¬ p3552) ∨ (¬ p4501) ∨ (¬ p3276) ∨ (¬ p4429) ∨ (¬ p5284) ∨ (¬ p3956)) : (p2027) ∨ (¬ p3276) ∨ (¬ p3552) ∨ (¬ p3956) ∨ (¬ p4422) ∨ (¬ p4429) ∨ (¬ p4501) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial30905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4422)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory20161 t (m.theta 3 7) (m.theta 3 9) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 8) (m.theta 9 10)
  exact rule30905 (meaning t m 2027) (meaning t m 3276) (meaning t m 3552) (meaning t m 3956) (meaning t m 4422) (meaning t m 4429) (meaning t m 4501) (meaning t m 5284) source

theorem rule30910 (p1987 p2027 p2957 p2997 p3097 p3370 p3737 p4315 p4435 p4512 : Prop) (h : p2027 ∨ (¬ p3737) ∨ (¬ p1987) ∨ (¬ p2957) ∨ (¬ p4315) ∨ (¬ p3370) ∨ (¬ p3097) ∨ p2997 ∨ (¬ p4435) ∨ (¬ p4512)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2957) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3370) ∨ (¬ p3737) ∨ (¬ p4315) ∨ (¬ p4435) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial30910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2957)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory20166 t (m.theta 0 5) (m.theta 1 5) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 10) (m.theta 6 7)
  exact rule30910 (meaning t m 1987) (meaning t m 2027) (meaning t m 2957) (meaning t m 2997) (meaning t m 3097) (meaning t m 3370) (meaning t m 3737) (meaning t m 4315) (meaning t m 4435) (meaning t m 4512) source

theorem rule30911 (p1983 p2027 p2210 p2449 p2685 p2696 p2753 p2764 p3591 p4026 p4191 p4877 : Prop) (h : (¬ p4026) ∨ (¬ p4191) ∨ p2027 ∨ p2764 ∨ (¬ p3591) ∨ (¬ p2210) ∨ (¬ p2753) ∨ (¬ p2696) ∨ (¬ p4877) ∨ (¬ p1983) ∨ (¬ p2449) ∨ (¬ p2685)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (p2764) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4191) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial30911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory20167 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule30911 (meaning t m 1983) (meaning t m 2027) (meaning t m 2210) (meaning t m 2449) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 2764) (meaning t m 3591) (meaning t m 4026) (meaning t m 4191) (meaning t m 4877) source

theorem rule30912 (p2005 p2027 p2114 p2341 p2737 p2811 p3016 p3553 p4104 p4112 : Prop) (h : p2114 ∨ (¬ p2737) ∨ p2027 ∨ (¬ p2811) ∨ (¬ p2341) ∨ (¬ p3016) ∨ (¬ p2005) ∨ (¬ p3553) ∨ (¬ p4104) ∨ (¬ p4112)) : (¬ p2005) ∨ (p2027) ∨ (p2114) ∨ (¬ p2341) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3016) ∨ (¬ p3553) ∨ (¬ p4104) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial30912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory20168 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 7 8)
  exact rule30912 (meaning t m 2005) (meaning t m 2027) (meaning t m 2114) (meaning t m 2341) (meaning t m 2737) (meaning t m 2811) (meaning t m 3016) (meaning t m 3553) (meaning t m 4104) (meaning t m 4112) source

theorem rule30913 (p2027 p2341 p3016 p3553 p4109 p4112 p4717 p4988 : Prop) (h : p2027 ∨ (¬ p2341) ∨ (¬ p4109) ∨ (¬ p4717) ∨ (¬ p3016) ∨ (¬ p4112) ∨ (¬ p3553) ∨ (¬ p4988)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3016) ∨ (¬ p3553) ∨ (¬ p4109) ∨ (¬ p4112) ∨ (¬ p4717) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial30913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4717)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory20169 t (m.theta 0 5) (m.theta 0 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 6) (m.theta 7 8)
  exact rule30913 (meaning t m 2027) (meaning t m 2341) (meaning t m 3016) (meaning t m 3553) (meaning t m 4109) (meaning t m 4112) (meaning t m 4717) (meaning t m 4988) source

theorem rule30915 (p4378 p5558 p5600 : Prop) (h : (¬ p4378) ∨ (¬ p5600) ∨ p5558) : (¬ p4378) ∨ (p5558) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial30915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4378)) ∨ (meaning t m 5558) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory20171 (m.theta 3 8) (m.theta 7 8) (m.theta 8 10)
  exact rule30915 (meaning t m 4378) (meaning t m 5558) (meaning t m 5600) source

theorem rule30918 (p2027 p2417 p3016 p3741 p3947 p4112 p4717 : Prop) (h : (¬ p4112) ∨ (¬ p2417) ∨ (¬ p3741) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p4717) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3016) ∨ (¬ p3741) ∨ (¬ p3947) ∨ (¬ p4112) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial30918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory20174 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule30918 (meaning t m 2027) (meaning t m 2417) (meaning t m 3016) (meaning t m 3741) (meaning t m 3947) (meaning t m 4112) (meaning t m 4717) source

theorem rule30921 (p1990 p2027 p2563 p2598 p2611 p2839 p3585 p3695 : Prop) (h : (¬ p3695) ∨ (¬ p2563) ∨ (¬ p1990) ∨ (¬ p3585) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p2598) ∨ p2611) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3695) := by
  classical
  tauto

theorem initial30921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3695)) := by
  have source := ElevenTheory.theory20177 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule30921 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2598) (meaning t m 2611) (meaning t m 2839) (meaning t m 3585) (meaning t m 3695) source

theorem rule30922 (p1977 p2027 p2169 p2363 p2534 p2579 p2662 p3573 p4111 : Prop) (h : (¬ p1977) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p3573) ∨ (¬ p4111) ∨ (¬ p2662) ∨ (¬ p2363) ∨ p2169 ∨ (¬ p2579)) : (¬ p1977) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p3573) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial30922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory20178 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule30922 (meaning t m 1977) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2534) (meaning t m 2579) (meaning t m 2662) (meaning t m 3573) (meaning t m 4111) source

theorem rule30930 (p1987 p2027 p2662 p2764 p2810 p3540 p4278 p4381 : Prop) (h : (¬ p4278) ∨ (¬ p1987) ∨ (¬ p2662) ∨ (¬ p3540) ∨ p2027 ∨ p2764 ∨ (¬ p2810) ∨ (¬ p4381)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2662) ∨ (p2764) ∨ (¬ p2810) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial30930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory20186 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule30930 (meaning t m 1987) (meaning t m 2027) (meaning t m 2662) (meaning t m 2764) (meaning t m 2810) (meaning t m 3540) (meaning t m 4278) (meaning t m 4381) source

theorem rule30931 (p1987 p2027 p2476 p2534 p2662 p2764 p2810 p4444 : Prop) (h : p2764 ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p1987) ∨ (¬ p2476) ∨ p2027 ∨ (¬ p4444)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (p2764) ∨ (¬ p2810) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial30931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory20187 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule30931 (meaning t m 1987) (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 2662) (meaning t m 2764) (meaning t m 2810) (meaning t m 4444) source

theorem rule30936 (p2027 p2331 p2753 p3323 p3379 p3461 p3860 p4117 p5123 p5216 p5693 : Prop) (h : (¬ p3379) ∨ (¬ p5693) ∨ (¬ p4117) ∨ (¬ p2753) ∨ (¬ p3323) ∨ p2027 ∨ (¬ p3860) ∨ (¬ p2331) ∨ (¬ p5123) ∨ (¬ p5216) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2753) ∨ (¬ p3323) ∨ (¬ p3379) ∨ (¬ p3461) ∨ (¬ p3860) ∨ (¬ p4117) ∨ (¬ p5123) ∨ (¬ p5216) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial30936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory20192 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 3 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule30936 (meaning t m 2027) (meaning t m 2331) (meaning t m 2753) (meaning t m 3323) (meaning t m 3379) (meaning t m 3461) (meaning t m 3860) (meaning t m 4117) (meaning t m 5123) (meaning t m 5216) (meaning t m 5693) source

theorem rule30939 (p2470 p3083 p3519 p4116 : Prop) (h : (¬ p4116) ∨ (¬ p2470) ∨ (¬ p3519) ∨ p3083) : (¬ p2470) ∨ (p3083) ∨ (¬ p3519) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial30939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (meaning t m 3083) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory20195 (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 8)
  exact rule30939 (meaning t m 2470) (meaning t m 3083) (meaning t m 3519) (meaning t m 4116) source

theorem rule30940 (p2027 p2245 p2299 p2657 p2717 p2727 p2996 p3471 p4361 p4733 : Prop) (h : (¬ p2299) ∨ (¬ p2657) ∨ (¬ p2245) ∨ (¬ p2727) ∨ (¬ p2717) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p4361) ∨ (¬ p4733) ∨ (¬ p3471)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2299) ∨ (¬ p2657) ∨ (¬ p2717) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3471) ∨ (¬ p4361) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial30940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory20196 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule30940 (meaning t m 2027) (meaning t m 2245) (meaning t m 2299) (meaning t m 2657) (meaning t m 2717) (meaning t m 2727) (meaning t m 2996) (meaning t m 3471) (meaning t m 4361) (meaning t m 4733) source

theorem rule30945 (p2027 p2192 p2210 p2274 p3365 p4037 p4195 p4620 p4736 : Prop) (h : (¬ p2192) ∨ (¬ p2274) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p4195) ∨ (¬ p2210) ∨ (¬ p4620) ∨ (¬ p4736) ∨ (¬ p4037)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (¬ p3365) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4620) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial30945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory20201 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule30945 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2274) (meaning t m 3365) (meaning t m 4037) (meaning t m 4195) (meaning t m 4620) (meaning t m 4736) source

theorem rule30946 (p1975 p2027 p2156 p2542 p2545 p3246 p3872 p4107 p4109 : Prop) (h : (¬ p2156) ∨ (¬ p2542) ∨ p2545 ∨ p2027 ∨ (¬ p4109) ∨ (¬ p3872) ∨ (¬ p4107) ∨ (¬ p1975) ∨ (¬ p3246)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p3246) ∨ (¬ p3872) ∨ (¬ p4107) ∨ (¬ p4109) := by
  classical
  tauto

theorem initial30946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4109)) := by
  have source := ElevenTheory.theory20202 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule30946 (meaning t m 1975) (meaning t m 2027) (meaning t m 2156) (meaning t m 2542) (meaning t m 2545) (meaning t m 3246) (meaning t m 3872) (meaning t m 4107) (meaning t m 4109) source

end SunPrize.SMT
