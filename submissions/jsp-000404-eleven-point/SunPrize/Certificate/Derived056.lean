import SunPrize.Certificate.Derived055
import SunPrize.Certificate.Logic056
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived105701 (p : Nat → Prop) (h : Inputs p) :
    (p 4559) :=
  ElevenRUP.step105701 (p 2274) (p 2553) (p 2563) (p 3051) (p 3096) (p 3660) (p 4533) (p 4559) (p 4718) (derived105690 p h) (derived105694 p h) (derived77999 p h) (derived93347 p h) (derived77959 p h) (derived105394 p h) (derived105425 p h) (derived98259 p h) (derived76977 p h)

theorem derived105702 (p : Nat → Prop) (h : Inputs p) :
    (p 4420) ∨ (¬ p 4157) :=
  ElevenRUP.step105702 (p 2177) (p 4133) (p 4157) (p 4420) (derived47523 p h) (derived102536 p h) (h 6821)

theorem derived105705 (p : Nat → Prop) (h : Inputs p) :
    (p 4420) ∨ (¬ p 3921) :=
  ElevenRUP.step105705 (p 2177) (p 2911) (p 3921) (p 4420) (derived101284 p h) (derived47523 p h) (derived82414 p h)

theorem derived105707 (p : Nat → Prop) (h : Inputs p) :
    (p 4420) :=
  ElevenRUP.step105707 (p 2177) (p 2352) (p 2553) (p 2911) (p 3920) (p 3921) (p 4138) (p 4157) (p 4420) (derived105705 p h) (derived98256 p h) (derived94485 p h) (derived101284 p h) (derived105702 p h) (derived80723 p h) (derived47523 p h) (derived87334 p h) (derived99544 p h)

theorem derived105709 (p : Nat → Prop) (h : Inputs p) :
    (p 4133) ∨ (¬ p 4140) :=
  ElevenRUP.step105709 (p 2177) (p 2881) (p 4133) (p 4140) (derived62052 p h) (derived98510 p h) (h 6620)

theorem derived105710 (p : Nat → Prop) (h : Inputs p) :
    (p 4133) ∨ (¬ p 2295) :=
  ElevenRUP.step105710 (p 2177) (p 2274) (p 2295) (p 2881) (p 4133) (p 4140) (p 4204) (derived62052 p h) (derived98510 p h) (derived105709 p h) (derived77956 p h) (derived100361 p h) (derived79315 p h)

theorem derived105711 (p : Nat → Prop) (h : Inputs p) :
    (p 4133) ∨ (¬ p 3547) :=
  ElevenRUP.step105711 (p 2177) (p 3527) (p 3547) (p 4133) (derived44445 p h) (derived98510 p h) (derived91697 p h)

theorem derived105712 (p : Nat → Prop) (h : Inputs p) :
    (p 4133) :=
  ElevenRUP.step105712 (p 2177) (p 2295) (p 2668) (p 3309) (p 3527) (p 3547) (p 3550) (p 4133) (p 5142) (derived44445 p h) (derived105710 p h) (derived98510 p h) (derived96472 p h) (derived98532 p h) (derived105711 p h) (derived85142 p h) (derived102560 p h) (derived95884 p h)

theorem derived105714 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 2811) :=
  ElevenRUP.step105714 (p 2630) (p 2651) (p 2659) (p 2811) (derived98004 p h) (derived44310 p h) (derived81859 p h)

theorem derived105715 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (p 2132) :=
  ElevenRUP.step105715 (p 2132) (p 2630) (p 2651) (p 2659) (p 2696) (p 2811) (p 4117) (derived98004 p h) (derived44310 p h) (derived105714 p h) (derived81801 p h) (derived84448 p h) (derived99702 p h)

theorem derived105716 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (p 2737) :=
  ElevenRUP.step105716 (p 2630) (p 2651) (p 2659) (p 2696) (p 2737) (p 2811) (p 4117) (derived98004 p h) (derived44310 p h) (derived105714 p h) (derived81801 p h) (derived84448 p h) (derived100565 p h)

theorem derived105721 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (p 2946) :=
  ElevenRUP.step105721 (p 2440) (p 2651) (p 2659) (p 2946) (p 3413) (derived98004 p h) (derived45878 p h) (derived96414 p h) (derived83112 p h)

theorem derived105723 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 3660) :=
  ElevenRUP.step105723 (p 2230) (p 2573) (p 2659) (p 3660) (derived103040 p h) (derived45436 p h) (derived87393 p h)

theorem derived105725 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 2284) :=
  ElevenRUP.step105725 (p 2230) (p 2284) (p 2440) (p 2563) (p 2573) (p 2659) (p 3096) (p 3660) (p 4705) (derived103040 p h) (derived45878 p h) (derived96415 p h) (derived105723 p h) (derived93346 p h) (derived96409 p h) (derived45436 p h) (derived87407 p h)

theorem derived105727 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 3051) :=
  ElevenRUP.step105727 (p 2230) (p 2563) (p 2573) (p 2659) (p 3051) (p 3660) (p 4558) (derived103040 p h) (derived105400 p h) (derived45436 p h) (derived105723 p h) (derived93346 p h) (derived103147 p h)

theorem derived105729 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 2373) :=
  ElevenRUP.step105729 (p 2230) (p 2373) (p 2563) (p 2573) (p 2659) (p 3096) (p 3660) (p 4509) (derived103040 p h) (derived105392 p h) (derived105723 p h) (derived93346 p h) (derived96409 p h) (derived45436 p h) (derived87404 p h)

theorem derived105731 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (p 3367) :=
  ElevenRUP.step105731 (p 2630) (p 2651) (p 2659) (p 2696) (p 2737) (p 2811) (p 3367) (p 4343) (p 4790) (derived44310 p h) (derived91164 p h) (derived105716 p h) (derived105714 p h) (derived81801 p h) (derived100669 p h) (derived98004 p h) (derived84446 p h)

theorem derived105732 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 3136) :=
  ElevenRUP.step105732 (p 2440) (p 2573) (p 2630) (p 2651) (p 2659) (p 2662) (p 3136) (p 4241) (p 4715) (derived98004 p h) (derived96928 p h) (derived105423 p h) (derived45436 p h) (derived44310 p h) (derived45878 p h) (derived96413 p h) (derived79168 p h)

theorem derived105733 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 3016) :=
  ElevenRUP.step105733 (p 2573) (p 2651) (p 2659) (p 2662) (p 3016) (derived98004 p h) (derived96928 p h) (derived45436 p h) (derived101056 p h)

theorem derived105735 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 3156) :=
  ElevenRUP.step105735 (p 2373) (p 2440) (p 2659) (p 3016) (p 3156) (p 3413) (p 4715) (derived45878 p h) (derived96414 p h) (derived105423 p h) (derived105729 p h) (derived105733 p h) (derived78994 p h)

theorem derived105736 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 2901) :=
  ElevenRUP.step105736 (p 2230) (p 2440) (p 2659) (p 2901) (p 3016) (p 3051) (p 3413) (p 4031) (p 4715) (derived103040 p h) (derived96016 p h) (derived105733 p h) (derived105727 p h) (derived45878 p h) (derived96414 p h) (derived105423 p h) (derived92912 p h)

theorem derived105737 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 2220) :=
  ElevenRUP.step105737 (p 2220) (p 2230) (p 2373) (p 2573) (p 2659) (p 4399) (p 4715) (derived103040 p h) (derived96017 p h) (derived105423 p h) (derived105729 p h) (derived45436 p h) (derived78956 p h)

theorem derived105739 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 2870) :=
  ElevenRUP.step105739 (p 2659) (p 2696) (p 2811) (p 2870) (p 3051) (derived105714 p h) (derived81801 p h) (derived105727 p h) (derived100671 p h)

theorem derived105742 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 2619) :=
  ElevenRUP.step105742 (p 2132) (p 2143) (p 2220) (p 2619) (p 2659) (derived105715 p h) (derived96981 p h) (derived105737 p h) (h 6704)

theorem derived105743 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (p 2839) :=
  ElevenRUP.step105743 (p 2659) (p 2696) (p 2737) (p 2811) (p 2839) (p 2946) (p 3136) (p 4316) (p 4790) (derived105716 p h) (derived105714 p h) (derived81801 p h) (derived100669 p h) (derived105721 p h) (derived105732 p h) (derived84419 p h) (derived100390 p h)

theorem derived105754 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (¬ p 3005) :=
  ElevenRUP.step105754 (p 2659) (p 3005) (p 3136) (p 3156) (p 3661) (derived105732 p h) (derived105735 p h) (derived96198 p h) (h 21815)

theorem derived105755 (p : Nat → Prop) (h : Inputs p) :
    (p 2659) ∨ (p 2807) :=
  ElevenRUP.step105755 (p 2440) (p 2651) (p 2659) (p 2807) (p 2901) (derived105736 p h) (derived98004 p h) (derived45878 p h) (derived78233 p h)

theorem derived105766 (p : Nat → Prop) (h : Inputs p) :
    (p 5682) :=
  ElevenRUP.step105766 (p 4166) (p 5678) (p 5682) (p 5684) (derived48877 p h) (h 10189) (derived66495 p h) (h 10194)

theorem derived105768 (p : Nat → Prop) (h : Inputs p) :
    (p 5222) ∨ (¬ p 3096) :=
  ElevenRUP.step105768 (p 2860) (p 3096) (p 4185) (p 4718) (p 4889) (p 5222) (derived105425 p h) (h 29385) (derived100456 p h) (derived95794 p h) (h 36855)

theorem derived105769 (p : Nat → Prop) (h : Inputs p) :
    (p 5222) ∨ (¬ p 3367) :=
  ElevenRUP.step105769 (p 3367) (p 3422) (p 5222) (derived97810 p h) (derived42751 p h)

theorem derived105774 (p : Nat → Prop) (h : Inputs p) :
    (p 5222) ∨ (¬ p 3695) :=
  ElevenRUP.step105774 (p 2563) (p 2860) (p 3096) (p 3695) (p 4185) (p 4718) (p 5222) (derived105768 p h) (derived77999 p h) (derived105425 p h) (h 29385) (derived100456 p h) (h 6693)

theorem derived105776 (p : Nat → Prop) (h : Inputs p) :
    (p 5222) ∨ (¬ p 2839) :=
  ElevenRUP.step105776 (p 2839) (p 2850) (p 3054) (p 3367) (p 3695) (p 5222) (derived105769 p h) (derived105774 p h) (derived81317 p h) (derived102320 p h) (derived81223 p h)

theorem derived105779 (p : Nat → Prop) (h : Inputs p) :
    (p 5222) ∨ (¬ p 2406) :=
  ElevenRUP.step105779 (p 2406) (p 2850) (p 3367) (p 3590) (p 3695) (p 5222) (derived105769 p h) (derived90607 p h) (derived105774 p h) (derived81317 p h) (derived76123 p h)

theorem derived105786 (p : Nat → Prop) (h : Inputs p) :
    (p 5222) ∨ (p 2192) :=
  ElevenRUP.step105786 (p 2192) (p 2406) (p 2850) (p 3096) (p 3422) (p 3695) (p 4203) (p 4629) (p 5222) (derived105774 p h) (derived81317 p h) (derived105768 p h) (h 38209) (derived97810 p h) (derived105779 p h) (derived102391 p h) (derived77711 p h)

theorem derived105793 (p : Nat → Prop) (h : Inputs p) :
    (p 5222) :=
  ElevenRUP.step105793 (p 2192) (p 2839) (p 2860) (p 4185) (p 4418) (p 4718) (p 5222) (derived105776 p h) (derived99611 p h) (derived105786 p h) (derived105425 p h) (h 29385) (derived100456 p h) (derived83186 p h)

theorem derived105796 (p : Nat → Prop) (h : Inputs p) :
    (p 5221) :=
  ElevenRUP.step105796 (p 2598) (p 2774) (p 3422) (p 4375) (p 5221) (derived43613 p h) (derived80978 p h) (derived97809 p h) (derived96275 p h) (derived86341 p h)

theorem derived105798 (p : Nat → Prop) (h : Inputs p) :
    (p 5142) ∨ (¬ p 2696) :=
  ElevenRUP.step105798 (p 2696) (p 3309) (p 3547) (p 5142) (derived101051 p h) (derived96286 p h) (derived48327 p h)

theorem derived105799 (p : Nat → Prop) (h : Inputs p) :
    (p 5142) ∨ (¬ p 2177) :=
  ElevenRUP.step105799 (p 2177) (p 3309) (p 3527) (p 3547) (p 5142) (derived101051 p h) (derived96286 p h) (derived61260 p h) (derived91697 p h)

theorem derived105800 (p : Nat → Prop) (h : Inputs p) :
    (p 5142) ∨ (¬ p 2396) :=
  ElevenRUP.step105800 (p 2396) (p 3309) (p 3547) (p 3631) (p 5142) (derived101051 p h) (derived96286 p h) (derived44484 p h) (derived91710 p h)

theorem derived105802 (p : Nat → Prop) (h : Inputs p) :
    (p 5021) ∨ (¬ p 4759) :=
  ElevenRUP.step105802 (p 2241) (p 3093) (p 4759) (p 5021) (derived80772 p h) (derived100615 p h) (derived80422 p h)

theorem derived105803 (p : Nat → Prop) (h : Inputs p) :
    (p 5021) ∨ (¬ p 2331) :=
  ElevenRUP.step105803 (p 2241) (p 2253) (p 2331) (p 2641) (p 3093) (p 4319) (p 4759) (p 5021) (derived80772 p h) (derived82153 p h) (derived105802 p h) (derived85986 p h) (derived85599 p h) (derived100615 p h) (derived100021 p h)

theorem derived105804 (p : Nat → Prop) (h : Inputs p) :
    (p 5021) ∨ (¬ p 4079) :=
  ElevenRUP.step105804 (p 2577) (p 3093) (p 4079) (p 5015) (p 5021) (p 5193) (derived105488 p h) (h 24506) (derived100615 p h) (derived95391 p h) (h 34194)

theorem derived105806 (p : Nat → Prop) (h : Inputs p) :
    (p 5021) ∨ (¬ p 2651) :=
  ElevenRUP.step105806 (p 2331) (p 2573) (p 2577) (p 2651) (p 5021) (p 5193) (derived105803 p h) (derived105488 p h) (h 24506) (derived98473 p h) (derived103776 p h)

theorem derived105808 (p : Nat → Prop) (h : Inputs p) :
    (p 5021) ∨ (¬ p 4281) :=
  ElevenRUP.step105808 (p 2241) (p 3379) (p 4079) (p 4281) (p 5021) (derived105804 p h) (derived87992 p h) (derived80772 p h) (h 6473)

theorem derived105809 (p : Nat → Prop) (h : Inputs p) :
    (p 5021) ∨ (¬ p 2992) :=
  ElevenRUP.step105809 (p 2241) (p 2727) (p 2992) (p 3379) (p 4079) (p 4116) (p 4281) (p 5021) (derived105804 p h) (derived87992 p h) (derived80772 p h) (derived105808 p h) (derived82176 p h) (derived87265 p h) (derived79748 p h)

theorem derived105810 (p : Nat → Prop) (h : Inputs p) :
    (p 5021) ∨ (p 3016) :=
  ElevenRUP.step105810 (p 2573) (p 2577) (p 2651) (p 2656) (p 3016) (p 5021) (p 5193) (derived105806 p h) (derived87995 p h) (derived105488 p h) (h 24506) (derived98473 p h) (derived83923 p h)

theorem derived105811 (p : Nat → Prop) (h : Inputs p) :
    (p 5021) ∨ (p 2996) :=
  ElevenRUP.step105811 (p 2241) (p 2727) (p 2996) (p 3379) (p 4079) (p 4116) (p 4281) (p 4652) (p 5021) (derived105808 p h) (derived82176 p h) (derived87265 p h) (derived80772 p h) (derived105413 p h) (derived105804 p h) (derived87992 p h) (derived79732 p h)

theorem derived105812 (p : Nat → Prop) (h : Inputs p) :
    (p 5021) ∨ (¬ p 2630) :=
  ElevenRUP.step105812 (p 2241) (p 2630) (p 2727) (p 2745) (p 3379) (p 4079) (p 4116) (p 4281) (p 5021) (derived105808 p h) (derived82176 p h) (derived87265 p h) (derived80772 p h) (derived105523 p h) (derived105804 p h) (derived87992 p h) (derived79743 p h)

theorem derived105815 (p : Nat → Prop) (h : Inputs p) :
    (p 4973) ∨ (¬ p 2662) :=
  ElevenRUP.step105815 (p 2573) (p 2662) (p 3016) (p 4973) (derived79489 p h) (derived43928 p h) (derived101056 p h)

theorem derived105820 (p : Nat → Prop) (h : Inputs p) :
    (p 4973) ∨ (¬ p 3983) :=
  ElevenRUP.step105820 (p 2331) (p 2573) (p 2578) (p 3016) (p 3983) (p 3984) (p 4973) (derived79489 p h) (derived101809 p h) (derived43928 p h) (derived78528 p h) (derived98810 p h) (h 5915)

theorem derived105835 (p : Nat → Prop) (h : Inputs p) :
    (p 4973) :=
  ElevenRUP.step105835 (p 2573) (p 2577) (p 2651) (p 2655) (p 2662) (p 3983) (p 4973) (derived105820 p h) (derived105815 p h) (derived78220 p h) (derived88056 p h) (derived43928 p h) (derived102520 p h) (h 26555)

theorem derived105836 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2727) :=
  ElevenRUP.step105836 (p 2641) (p 2727) (p 3016) (p 4972) (p 4976) (derived44045 p h) (derived105465 p h) (derived79488 p h) (derived100481 p h)

theorem derived105837 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2630) :=
  ElevenRUP.step105837 (p 2630) (p 2797) (p 3016) (p 3019) (p 4972) (derived45401 p h) (derived79488 p h) (derived101604 p h) (derived87216 p h)

theorem derived105839 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2331) :=
  ElevenRUP.step105839 (p 2331) (p 2651) (p 3016) (p 3019) (p 4972) (derived79488 p h) (derived101604 p h) (derived98091 p h) (derived87202 p h)

theorem derived105841 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2246) :=
  ElevenRUP.step105841 (p 2246) (p 2331) (p 2641) (p 4245) (p 4319) (p 4972) (derived44045 p h) (derived100554 p h) (derived105839 p h) (derived85599 p h) (h 15125)

theorem derived105842 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2573) :=
  ElevenRUP.step105842 (p 2573) (p 2651) (p 2662) (p 3016) (p 4972) (derived98091 p h) (derived96928 p h) (derived79488 p h) (derived101056 p h)

theorem derived105846 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 3379) :=
  ElevenRUP.step105846 (p 2241) (p 2246) (p 2253) (p 2651) (p 2727) (p 3379) (p 4116) (p 4972) (derived105836 p h) (derived87265 p h) (derived105841 p h) (derived75367 p h) (derived82153 p h) (derived98091 p h) (derived100004 p h)

theorem derived105847 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2493) :=
  ElevenRUP.step105847 (p 2255) (p 2493) (p 2651) (p 2727) (p 3016) (p 3402) (p 4972) (derived105836 p h) (derived101758 p h) (derived79488 p h) (derived105367 p h) (derived98091 p h) (derived99300 p h)

theorem derived105848 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2811) :=
  ElevenRUP.step105848 (p 2630) (p 2651) (p 2811) (p 4972) (derived105837 p h) (derived98091 p h) (derived81859 p h)

theorem derived105851 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 3093) :=
  ElevenRUP.step105851 (p 2241) (p 2246) (p 2253) (p 2331) (p 2641) (p 3093) (p 4319) (p 4972) (derived105841 p h) (derived75367 p h) (derived82153 p h) (derived44045 p h) (derived85599 p h) (derived105839 p h) (derived100021 p h)

theorem derived105856 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2737) :=
  ElevenRUP.step105856 (p 2651) (p 2696) (p 2727) (p 2737) (p 2811) (p 4972) (derived105848 p h) (derived81801 p h) (derived98091 p h) (derived105836 p h) (derived105049 p h)

theorem derived105857 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2132) :=
  ElevenRUP.step105857 (p 2132) (p 2331) (p 2696) (p 2797) (p 2811) (p 4117) (p 4972) (derived105848 p h) (derived81801 p h) (derived84448 p h) (derived45401 p h) (derived105839 p h) (derived100739 p h)

theorem derived105859 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2774) :=
  ElevenRUP.step105859 (p 2331) (p 2696) (p 2774) (p 2797) (p 2811) (p 4117) (p 4337) (p 4972) (derived105848 p h) (derived81801 p h) (derived84448 p h) (derived105839 p h) (derived45401 p h) (derived90912 p h) (derived100759 p h)

theorem derived105860 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 3422) :=
  ElevenRUP.step105860 (p 2630) (p 2651) (p 2696) (p 2811) (p 3016) (p 3364) (p 3422) (p 4790) (p 4972) (derived105848 p h) (derived81801 p h) (derived100669 p h) (derived105837 p h) (derived88126 p h) (derived79488 p h) (derived98091 p h) (derived101257 p h)

theorem derived105864 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 3367) :=
  ElevenRUP.step105864 (p 2630) (p 2651) (p 2696) (p 2737) (p 2811) (p 3367) (p 4343) (p 4790) (p 4972) (derived105856 p h) (derived105837 p h) (derived91164 p h) (derived105848 p h) (derived81801 p h) (derived100669 p h) (derived98091 p h) (derived84446 p h)

theorem derived105865 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2829) :=
  ElevenRUP.step105865 (p 2331) (p 2696) (p 2737) (p 2797) (p 2811) (p 2829) (p 4337) (p 4790) (p 4972) (derived105856 p h) (derived105839 p h) (derived45401 p h) (derived90912 p h) (derived105848 p h) (derived81801 p h) (derived100669 p h) (derived100391 p h)

theorem derived105867 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2608) :=
  ElevenRUP.step105867 (p 2241) (p 2246) (p 2253) (p 2331) (p 2608) (p 2641) (p 2737) (p 2750) (p 4972) (derived105856 p h) (derived100642 p h) (derived105841 p h) (derived75367 p h) (derived82153 p h) (derived44045 p h) (derived105839 p h) (derived100014 p h)

theorem derived105870 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2352) :=
  ElevenRUP.step105870 (p 2352) (p 2608) (p 3367) (p 3422) (p 4972) (derived105867 p h) (derived105860 p h) (derived105864 p h) (derived43452 p h)

theorem derived105871 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2553) :=
  ElevenRUP.step105871 (p 2553) (p 2608) (p 3367) (p 3422) (p 4972) (derived105867 p h) (derived105860 p h) (derived105864 p h) (derived42845 p h)

theorem derived105872 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2122) :=
  ElevenRUP.step105872 (p 2122) (p 2553) (p 2608) (p 2829) (p 4972) (derived105867 p h) (derived105871 p h) (derived105865 p h) (derived90350 p h)

theorem derived105873 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2295) :=
  ElevenRUP.step105873 (p 2122) (p 2295) (p 2331) (p 2696) (p 2797) (p 2811) (p 4790) (p 4841) (p 4972) (derived105872 p h) (derived45401 p h) (derived102194 p h) (derived105848 p h) (derived81801 p h) (derived100669 p h) (derived105839 p h) (derived90293 p h)

theorem derived105874 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2307) :=
  ElevenRUP.step105874 (p 2255) (p 2295) (p 2307) (p 2331) (p 2641) (p 3987) (p 4972) (derived105873 p h) (derived105367 p h) (derived44045 p h) (derived105839 p h) (derived96449 p h) (derived83135 p h)

theorem derived105876 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2440) :=
  ElevenRUP.step105876 (p 2295) (p 2440) (p 4972) (derived105873 p h) (derived98658 p h)

theorem derived105877 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2996) :=
  ElevenRUP.step105877 (p 2295) (p 2641) (p 2996) (p 4067) (p 4972) (derived105873 p h) (derived98805 p h) (derived44045 p h) (derived81948 p h)

theorem derived105878 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2685) :=
  ElevenRUP.step105878 (p 2295) (p 2685) (p 2797) (p 4067) (p 4972) (derived105873 p h) (derived98805 p h) (derived45401 p h) (h 6856)

theorem derived105879 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2850) :=
  ElevenRUP.step105879 (p 2440) (p 2630) (p 2850) (p 4343) (p 4972) (derived105876 p h) (derived105837 p h) (derived91164 p h) (h 19857)

theorem derived105880 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2563) :=
  ElevenRUP.step105880 (p 2440) (p 2563) (p 3016) (p 3958) (p 4972) (derived105876 p h) (derived105378 p h) (derived79488 p h) (derived101272 p h)

theorem derived105882 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2230) :=
  ElevenRUP.step105882 (p 2230) (p 2440) (p 2630) (p 2696) (p 2811) (p 4790) (p 4972) (derived105876 p h) (derived105848 p h) (derived81801 p h) (derived100669 p h) (derived105837 p h) (derived103124 p h)

theorem derived105883 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2406) :=
  ElevenRUP.step105883 (p 2406) (p 2440) (p 2630) (p 4972) (derived105876 p h) (derived105837 p h) (derived104437 p h)

theorem derived105885 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2373) :=
  ElevenRUP.step105885 (p 2373) (p 2440) (p 2563) (p 3016) (p 4203) (p 4972) (derived105876 p h) (derived105880 p h) (derived87285 p h) (derived79488 p h) (derived78936 p h)

theorem derived105886 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2427) :=
  ElevenRUP.step105886 (p 2427) (p 2440) (p 2563) (p 3016) (p 4203) (p 4555) (p 4972) (derived105876 p h) (derived105542 p h) (derived79488 p h) (derived105880 p h) (derived87285 p h) (derived101271 p h)

theorem derived105887 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 3063) :=
  ElevenRUP.step105887 (p 2352) (p 2440) (p 2493) (p 2505) (p 2727) (p 3063) (p 4116) (p 4717) (p 4972) (derived105876 p h) (derived105424 p h) (derived105870 p h) (derived105847 p h) (derived96943 p h) (derived105836 p h) (derived87265 p h) (derived83526 p h)

theorem derived105888 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2992) :=
  ElevenRUP.step105888 (p 2440) (p 2727) (p 2992) (p 4700) (p 4972) (derived105876 p h) (derived100363 p h) (derived105836 p h) (derived81805 p h)

theorem derived105889 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 3136) :=
  ElevenRUP.step105889 (p 2440) (p 2630) (p 3136) (p 4700) (p 4972) (derived105876 p h) (derived100363 p h) (derived105837 p h) (derived84307 p h)

theorem derived105890 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2946) :=
  ElevenRUP.step105890 (p 2440) (p 2493) (p 2651) (p 2727) (p 2946) (p 3879) (p 4116) (p 4717) (p 4972) (derived105876 p h) (derived100365 p h) (derived98091 p h) (derived105424 p h) (derived105836 p h) (derived87265 p h) (derived105847 p h) (derived85767 p h)

theorem derived105894 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2870) :=
  ElevenRUP.step105894 (p 2427) (p 2850) (p 2870) (p 3054) (p 3422) (p 4717) (p 4972) (derived105879 p h) (derived102320 p h) (derived105424 p h) (derived105860 p h) (derived105886 p h) (derived86817 p h)

theorem derived105895 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2839) :=
  ElevenRUP.step105895 (p 2839) (p 2850) (p 3367) (p 3422) (p 3698) (p 4717) (p 4972) (derived105879 p h) (derived102190 p h) (derived105860 p h) (derived105864 p h) (derived105424 p h) (derived77706 p h)

theorem derived105896 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2274) :=
  ElevenRUP.step105896 (p 2122) (p 2274) (p 2563) (p 4972) (derived105880 p h) (derived105872 p h) (derived103196 p h)

theorem derived105897 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2982) :=
  ElevenRUP.step105897 (p 2440) (p 2563) (p 2982) (p 3016) (p 4203) (p 4972) (p 5043) (derived105880 p h) (derived87285 p h) (derived105471 p h) (derived105876 p h) (derived79488 p h) (derived92090 p h)

theorem derived105899 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2284) :=
  ElevenRUP.step105899 (p 2284) (p 2406) (p 2440) (p 2493) (p 2563) (p 4203) (p 4702) (p 4972) (derived105880 p h) (derived87285 p h) (derived105883 p h) (derived105876 p h) (derived98764 p h) (derived105847 p h) (derived85791 p h)

theorem derived105902 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 3051) :=
  ElevenRUP.step105902 (p 2230) (p 2427) (p 2573) (p 3051) (p 3904) (p 4717) (p 4972) (derived105882 p h) (derived102493 p h) (derived105842 p h) (derived105424 p h) (derived105886 p h) (derived92836 p h)

theorem derived105903 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2166) :=
  ElevenRUP.step105903 (p 2166) (p 2406) (p 2493) (p 2563) (p 4972) (derived105883 p h) (derived105880 p h) (derived105847 p h) (derived103244 p h)

theorem derived105905 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2210) :=
  ElevenRUP.step105905 (p 2210) (p 2406) (p 2493) (p 3379) (p 4034) (p 4717) (p 4972) (derived105883 p h) (derived101810 p h) (derived105847 p h) (derived105424 p h) (derived105846 p h) (derived85780 p h)

theorem derived105906 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 3156) :=
  ElevenRUP.step105906 (p 2373) (p 2440) (p 3016) (p 3156) (p 4700) (p 4717) (p 4972) (derived105885 p h) (derived105424 p h) (derived79488 p h) (derived105876 p h) (derived100363 p h) (derived83047 p h)

theorem derived105909 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2668) :=
  ElevenRUP.step105909 (p 2255) (p 2331) (p 2641) (p 2668) (p 3063) (p 3923) (p 4245) (p 4972) (p 4992) (p 4996) (derived105887 p h) (h 8340) (derived66420 p h) (h 8334) (derived105839 p h) (derived105367 p h) (derived44045 p h) (derived100554 p h) (derived48495 p h)

theorem derived105912 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2901) :=
  ElevenRUP.step105912 (p 2870) (p 2901) (p 3136) (p 4316) (p 4972) (derived105894 p h) (derived105889 p h) (derived84419 p h) (derived100652 p h)

theorem derived105914 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2707) :=
  ElevenRUP.step105914 (p 2707) (p 2839) (p 2870) (p 3587) (p 4972) (derived105894 p h) (derived102334 p h) (derived105895 p h) (derived83673 p h)

theorem derived105915 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 3246) :=
  ElevenRUP.step105915 (p 2608) (p 2839) (p 2870) (p 3246) (p 4972) (derived105895 p h) (derived105867 p h) (derived105894 p h) (derived42904 p h)

theorem derived105916 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2881) :=
  ElevenRUP.step105916 (p 2608) (p 2839) (p 2870) (p 2881) (p 4972) (derived105895 p h) (derived105894 p h) (derived105867 p h) (derived42847 p h)

theorem derived105921 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 3105) :=
  ElevenRUP.step105921 (p 2850) (p 2982) (p 3054) (p 3105) (p 3422) (p 4717) (p 4972) (derived105897 p h) (derived105424 p h) (derived105879 p h) (derived102320 p h) (derived105860 p h) (derived84551 p h)

theorem derived105924 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2807) :=
  ElevenRUP.step105924 (p 2284) (p 2807) (p 2946) (p 4555) (p 4972) (derived105899 p h) (derived105542 p h) (derived105890 p h) (derived98897 p h)

theorem derived105927 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 2220) :=
  ElevenRUP.step105927 (p 2166) (p 2220) (p 2230) (p 2406) (p 2573) (p 3904) (p 4034) (p 4717) (p 4972) (derived105903 p h) (derived105842 p h) (derived105883 p h) (derived101810 p h) (derived105882 p h) (derived102493 p h) (derived105424 p h) (derived87644 p h)

theorem derived105933 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 3166) :=
  ElevenRUP.step105933 (p 2946) (p 3156) (p 3166) (p 4237) (p 4972) (derived105906 p h) (derived100888 p h) (derived105890 p h) (h 6810)

theorem derived105940 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 3434) :=
  ElevenRUP.step105940 (p 2608) (p 2707) (p 3246) (p 3434) (p 4972) (derived105915 p h) (derived105867 p h) (derived105914 p h) (derived89561 p h)

theorem derived105941 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2717) :=
  ElevenRUP.step105941 (p 2608) (p 2707) (p 2717) (p 2881) (p 4972) (derived105916 p h) (derived105914 p h) (derived105867 p h) (derived89167 p h)

theorem derived105943 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (p 3115) :=
  ElevenRUP.step105943 (p 2132) (p 2284) (p 3105) (p 3115) (p 4972) (derived105921 p h) (derived105899 p h) (derived105857 p h) (derived90645 p h)

theorem derived105954 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2449) :=
  ElevenRUP.step105954 (p 2449) (p 2685) (p 2696) (p 2807) (p 2811) (p 3434) (p 4357) (p 4790) (p 4972) (derived105940 p h) (derived105878 p h) (derived102054 p h) (derived105848 p h) (derived81801 p h) (derived100669 p h) (derived105924 p h) (derived89812 p h)

theorem derived105955 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 3527) :=
  ElevenRUP.step105955 (p 2685) (p 2696) (p 2717) (p 2807) (p 2811) (p 2996) (p 3032) (p 3527) (p 4357) (p 4790) (p 4972) (derived105941 p h) (derived105878 p h) (derived102054 p h) (derived105877 p h) (derived76408 p h) (derived105848 p h) (derived81801 p h) (derived100669 p h) (derived105924 p h) (derived89819 p h)

theorem derived105964 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 3516) :=
  ElevenRUP.step105964 (p 2255) (p 2449) (p 2946) (p 2958) (p 2996) (p 3051) (p 3516) (p 4972) (p 4988) (derived105954 p h) (derived105890 p h) (derived96895 p h) (derived105877 p h) (derived105902 p h) (derived102490 p h) (derived105367 p h) (derived99940 p h)

theorem derived105970 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2264) :=
  ElevenRUP.step105970 (p 2255) (p 2264) (p 2807) (p 2996) (p 3031) (p 3527) (p 4972) (derived105955 p h) (derived105924 p h) (derived105877 p h) (derived101921 p h) (derived105367 p h) (derived88242 p h)

theorem derived105971 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 2341) :=
  ElevenRUP.step105971 (p 2255) (p 2341) (p 2807) (p 2996) (p 3527) (p 4104) (p 4972) (derived105955 p h) (derived105877 p h) (derived105924 p h) (derived93816 p h) (derived105367 p h) (derived103686 p h)

theorem derived105976 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 3483) :=
  ElevenRUP.step105976 (p 2122) (p 2315) (p 3483) (p 3516) (p 4972) (derived105964 p h) (derived105368 p h) (derived105872 p h) (derived90221 p h)

theorem derived105983 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 3564) :=
  ElevenRUP.step105983 (p 3422) (p 3483) (p 3564) (p 4390) (p 4972) (derived105976 p h) (derived105860 p h) (derived96274 p h) (h 40201)

theorem derived105985 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 3654) :=
  ElevenRUP.step105985 (p 2230) (p 2573) (p 2584) (p 3564) (p 3654) (p 4717) (p 4972) (derived105983 p h) (derived105842 p h) (derived96934 p h) (derived105424 p h) (derived105882 p h) (derived99114 p h)

theorem derived105987 (p : Nat → Prop) (h : Inputs p) :
    (p 4972) ∨ (¬ p 3323) :=
  ElevenRUP.step105987 (p 2331) (p 2667) (p 3323) (p 3654) (p 4972) (derived105985 p h) (derived105839 p h) (derived96448 p h) (h 22610)

theorem derived105991 (p : Nat → Prop) (h : Inputs p) :
    (p 4905) ∨ (¬ p 4988) :=
  ElevenRUP.step105991 (p 2220) (p 2341) (p 2881) (p 4132) (p 4905) (p 4988) (derived46740 p h) (derived102241 p h) (derived81812 p h) (derived95081 p h) (h 22087)

theorem derived105995 (p : Nat → Prop) (h : Inputs p) :
    (p 4905) :=
  ElevenRUP.step105995 (p 2341) (p 2881) (p 3051) (p 4905) (p 4985) (p 4988) (derived105991 p h) (derived102415 p h) (derived96334 p h) (derived81812 p h) (derived102241 p h) (derived89667 p h)

theorem derived105996 (p : Nat → Prop) (h : Inputs p) :
    (p 4885) ∨ (p 2598) :=
  ElevenRUP.step105996 (p 2598) (p 2850) (p 4885) (derived81320 p h) (derived101816 p h)

theorem derived105997 (p : Nat → Prop) (h : Inputs p) :
    (p 4885) ∨ (p 2427) :=
  ElevenRUP.step105997 (p 2427) (p 2850) (p 2870) (p 3698) (p 4885) (derived86564 p h) (derived81320 p h) (derived102190 p h) (derived90155 p h)

theorem derived106000 (p : Nat → Prop) (h : Inputs p) :
    (p 4885) ∨ (¬ p 2406) :=
  ElevenRUP.step106000 (p 2132) (p 2406) (p 2598) (p 2850) (p 3698) (p 4885) (p 5217) (derived42901 p h) (derived105493 p h) (derived105996 p h) (derived81320 p h) (derived102190 p h) (derived90165 p h)

theorem derived106001 (p : Nat → Prop) (h : Inputs p) :
    (p 4885) ∨ (p 2440) :=
  ElevenRUP.step106001 (p 2132) (p 2440) (p 2598) (p 4750) (p 4885) (derived42901 p h) (derived105996 p h) (derived105433 p h) (derived103374 p h)

theorem derived106004 (p : Nat → Prop) (h : Inputs p) :
    (p 4885) ∨ (¬ p 2860) :=
  ElevenRUP.step106004 (p 2563) (p 2850) (p 2860) (p 3698) (p 4885) (derived81320 p h) (derived102190 p h) (derived45074 p h) (derived90162 p h)

theorem derived106007 (p : Nat → Prop) (h : Inputs p) :
    (p 4885) ∨ (¬ p 4204) :=
  ElevenRUP.step106007 (p 2427) (p 2563) (p 4204) (p 4885) (derived105997 p h) (derived45074 p h) (derived83000 p h)

theorem derived106011 (p : Nat → Prop) (h : Inputs p) :
    (p 4885) ∨ (¬ p 2493) :=
  ElevenRUP.step106011 (p 2406) (p 2493) (p 2563) (p 2590) (p 4885) (derived106000 p h) (derived45074 p h) (derived96410 p h) (derived104618 p h)

theorem derived106014 (p : Nat → Prop) (h : Inputs p) :
    (p 4885) ∨ (¬ p 2156) :=
  ElevenRUP.step106014 (p 2156) (p 2440) (p 2563) (p 4885) (derived106001 p h) (derived45074 p h) (derived102952 p h)

theorem derived106018 (p : Nat → Prop) (h : Inputs p) :
    (p 4885) ∨ (p 3367) :=
  ElevenRUP.step106018 (p 2132) (p 2598) (p 2860) (p 3367) (p 4885) (derived106004 p h) (derived42901 p h) (derived105996 p h) (derived83365 p h)

theorem derived106021 (p : Nat → Prop) (h : Inputs p) :
    (p 4885) ∨ (¬ p 2774) :=
  ElevenRUP.step106021 (p 2132) (p 2774) (p 2860) (p 4193) (p 4885) (derived106004 p h) (derived95792 p h) (derived42901 p h) (derived99731 p h)

theorem derived106023 (p : Nat → Prop) (h : Inputs p) :
    (p 4885) ∨ (p 2553) :=
  ElevenRUP.step106023 (p 2274) (p 2553) (p 2860) (p 2870) (p 3958) (p 4140) (p 4204) (p 4885) (derived106007 p h) (derived98491 p h) (derived95963 p h) (derived105378 p h) (derived86564 p h) (derived106004 p h) (derived83256 p h)

theorem derived106027 (p : Nat → Prop) (h : Inputs p) :
    (p 4885) ∨ (¬ p 2230) :=
  ElevenRUP.step106027 (p 2230) (p 2598) (p 2774) (p 2850) (p 3362) (p 4885) (p 5221) (derived106021 p h) (derived105996 p h) (derived101922 p h) (derived105796 p h) (derived81320 p h) (derived86377 p h)

theorem derived106033 (p : Nat → Prop) (h : Inputs p) :
    (p 4866) ∨ (¬ p 4861) :=
  ElevenRUP.step106033 (p 2829) (p 3537) (p 4861) (p 4866) (derived90427 p h) (derived46904 p h) (derived102037 p h)

theorem derived106034 (p : Nat → Prop) (h : Inputs p) :
    (p 4866) ∨ (¬ p 2122) :=
  ElevenRUP.step106034 (p 2122) (p 2819) (p 2829) (p 3537) (p 4857) (p 4861) (p 4866) (derived90427 p h) (derived46904 p h) (derived106033 p h) (derived86287 p h) (derived93122 p h) (derived102038 p h)

theorem derived106036 (p : Nat → Prop) (h : Inputs p) :
    (p 4866) ∨ (p 2774) :=
  ElevenRUP.step106036 (p 2608) (p 2774) (p 2829) (p 3366) (p 4866) (derived75629 p h) (derived87229 p h) (derived90427 p h) (derived86302 p h)

theorem derived106037 (p : Nat → Prop) (h : Inputs p) :
    (p 4866) ∨ (p 3093) :=
  ElevenRUP.step106037 (p 2608) (p 2829) (p 3093) (p 4866) (p 4869) (derived90427 p h) (derived102297 p h) (derived75629 p h) (derived92033 p h)

theorem derived106041 (p : Nat → Prop) (h : Inputs p) :
    (p 4866) ∨ (¬ p 3367) :=
  ElevenRUP.step106041 (p 3093) (p 3367) (p 4866) (derived106037 p h) (derived56618 p h)

theorem derived106043 (p : Nat → Prop) (h : Inputs p) :
    (p 4866) ∨ (p 2307) :=
  ElevenRUP.step106043 (p 2307) (p 3093) (p 3204) (p 3309) (p 4866) (derived106037 p h) (derived101909 p h) (derived101191 p h) (h 33892)

theorem derived106046 (p : Nat → Prop) (h : Inputs p) :
    (p 4866) ∨ (¬ p 5220) :=
  ElevenRUP.step106046 (p 2829) (p 3367) (p 4866) (p 5220) (derived106041 p h) (derived90427 p h) (derived77760 p h)

theorem derived106049 (p : Nat → Prop) (h : Inputs p) :
    (p 4866) ∨ (p 2598) :=
  ElevenRUP.step106049 (p 2122) (p 2307) (p 2598) (p 2774) (p 2786) (p 4866) (p 5224) (derived106043 p h) (derived106036 p h) (derived102220 p h) (derived106034 p h) (derived105494 p h) (derived81067 p h)

theorem derived106057 (p : Nat → Prop) (h : Inputs p) :
    (p 4866) ∨ (¬ p 2553) :=
  ElevenRUP.step106057 (p 2122) (p 2553) (p 3422) (p 4390) (p 4866) (p 5220) (derived106046 p h) (derived97807 p h) (derived96274 p h) (derived106034 p h) (derived87956 p h)

theorem derived106063 (p : Nat → Prop) (h : Inputs p) :
    (p 4866) :=
  ElevenRUP.step106063 (p 2553) (p 2598) (p 2829) (p 3309) (p 3367) (p 4866) (p 4869) (derived106057 p h) (derived106049 p h) (derived106041 p h) (derived101191 p h) (derived90427 p h) (derived102297 p h) (derived85172 p h)

theorem derived106065 (p : Nat → Prop) (h : Inputs p) :
    (p 4842) ∨ (p 3367) :=
  ElevenRUP.step106065 (p 2630) (p 2737) (p 2797) (p 3367) (p 4343) (p 4842) (p 4975) (derived101561 p h) (derived81225 p h) (derived105464 p h) (derived47675 p h) (derived91164 p h) (derived92304 p h)

theorem derived106066 (p : Nat → Prop) (h : Inputs p) :
    (p 4842) ∨ (p 2641) :=
  ElevenRUP.step106066 (p 2641) (p 2737) (p 2748) (p 2797) (p 4842) (derived81225 p h) (derived86489 p h) (derived101561 p h) (derived100463 p h)

theorem derived106067 (p : Nat → Prop) (h : Inputs p) :
    (p 4842) ∨ (p 2829) :=
  ElevenRUP.step106067 (p 2737) (p 2797) (p 2829) (p 4426) (p 4842) (derived101561 p h) (derived96383 p h) (derived81225 p h) (derived94907 p h)

theorem derived106069 (p : Nat → Prop) (h : Inputs p) :
    (p 4842) ∨ (p 2839) :=
  ElevenRUP.step106069 (p 2829) (p 2839) (p 2860) (p 3985) (p 4193) (p 4842) (derived67310 p h) (derived100457 p h) (derived95792 p h) (derived106067 p h) (derived99681 p h)

theorem derived106074 (p : Nat → Prop) (h : Inputs p) :
    (p 4730) :=
  ElevenRUP.step106074 (p 2598) (p 4730) (derived97805 p h) (derived105528 p h)

theorem derived106079 (p : Nat → Prop) (h : Inputs p) :
    (p 4702) :=
  ElevenRUP.step106079 (p 2284) (p 2440) (p 2563) (p 4241) (p 4702) (derived97930 p h) (derived96413 p h) (derived45950 p h) (derived78003 p h) (derived79163 p h)

theorem derived106080 (p : Nat → Prop) (h : Inputs p) :
    (p 4629) ∨ (¬ p 2608) :=
  ElevenRUP.step106080 (p 2230) (p 2406) (p 2608) (p 4629) (derived97678 p h) (derived45127 p h) (derived104621 p h)

theorem derived106081 (p : Nat → Prop) (h : Inputs p) :
    (p 4629) ∨ (¬ p 2427) :=
  ElevenRUP.step106081 (p 2406) (p 2427) (p 2891) (p 4210) (p 4629) (derived97678 p h) (derived96428 p h) (derived43744 p h) (h 6670)

theorem derived106085 (p : Nat → Prop) (h : Inputs p) :
    (p 4629) ∨ (¬ p 2210) :=
  ElevenRUP.step106085 (p 2210) (p 2608) (p 2839) (p 4243) (p 4629) (p 4875) (p 4882) (derived105453 p h) (h 23767) (derived83161 p h) (derived106080 p h) (derived102527 p h) (derived97446 p h)

theorem derived106086 (p : Nat → Prop) (h : Inputs p) :
    (p 4629) ∨ (¬ p 2241) :=
  ElevenRUP.step106086 (p 2230) (p 2241) (p 2406) (p 2608) (p 4629) (p 4749) (derived106080 p h) (derived105432 p h) (derived45127 p h) (derived97678 p h) (derived104556 p h)

theorem derived106089 (p : Nat → Prop) (h : Inputs p) :
    (p 4629) ∨ (¬ p 3389) :=
  ElevenRUP.step106089 (p 2230) (p 2427) (p 2441) (p 3389) (p 4629) (derived106081 p h) (derived95462 p h) (derived45127 p h) (derived74736 p h)

theorem derived106093 (p : Nat → Prop) (h : Inputs p) :
    (p 4521) ∨ (¬ p 4202) :=
  ElevenRUP.step106093 (p 2210) (p 3379) (p 4202) (p 4521) (derived45885 p h) (derived75445 p h) (h 6790)

theorem derived106094 (p : Nat → Prop) (h : Inputs p) :
    (p 4521) ∨ (¬ p 2440) :=
  ElevenRUP.step106094 (p 2210) (p 2406) (p 2440) (p 3379) (p 4202) (p 4210) (p 4521) (p 4814) (derived45885 p h) (derived106093 p h) (derived97675 p h) (derived96428 p h) (derived105440 p h) (derived75445 p h) (derived79705 p h)

theorem derived106096 (p : Nat → Prop) (h : Inputs p) :
    (p 4521) ∨ (p 2493) :=
  ElevenRUP.step106096 (p 2210) (p 2406) (p 2493) (p 3379) (p 4202) (p 4210) (p 4521) (p 4715) (derived45885 p h) (derived75445 p h) (derived105423 p h) (derived106093 p h) (derived97675 p h) (derived96428 p h) (derived79696 p h)

theorem derived106098 (p : Nat → Prop) (h : Inputs p) :
    (p 4521) ∨ (¬ p 2509) :=
  ElevenRUP.step106098 (p 2210) (p 2406) (p 2509) (p 3379) (p 4202) (p 4210) (p 4521) (p 4608) (derived45885 p h) (derived106093 p h) (derived97675 p h) (derived96428 p h) (derived105540 p h) (derived75445 p h) (derived79704 p h)

theorem derived106103 (p : Nat → Prop) (h : Inputs p) :
    (p 4518) ∨ (¬ p 3370) :=
  ElevenRUP.step106103 (p 2156) (p 2192) (p 3370) (p 4518) (derived99458 p h) (derived85378 p h) (derived79946 p h)

theorem derived106113 (p : Nat → Prop) (h : Inputs p) :
    (p 4518) :=
  ElevenRUP.step106113 (p 2156) (p 2192) (p 2210) (p 3093) (p 3370) (p 3957) (p 4172) (p 4518) (derived99458 p h) (derived96469 p h) (derived106103 p h) (derived75444 p h) (derived102417 p h) (derived47663 p h) (derived85378 p h) (derived91553 p h)

theorem derived106114 (p : Nat → Prop) (h : Inputs p) :
    (p 4438) ∨ (¬ p 2528) :=
  ElevenRUP.step106114 (p 2459) (p 2528) (p 2911) (p 4383) (p 4438) (derived47903 p h) (derived80109 p h) (derived85674 p h) (derived74499 p h)

theorem derived106115 (p : Nat → Prop) (h : Inputs p) :
    (p 4438) ∨ (¬ p 4710) :=
  ElevenRUP.step106115 (p 2177) (p 2911) (p 4438) (p 4710) (derived97273 p h) (derived80109 p h) (h 17517)

theorem derived106118 (p : Nat → Prop) (h : Inputs p) :
    (p 4438) ∨ (¬ p 3256) :=
  ElevenRUP.step106118 (p 2528) (p 3083) (p 3256) (p 4437) (p 4438) (derived47818 p h) (derived93397 p h) (derived106114 p h) (h 25758)

theorem derived106119 (p : Nat → Prop) (h : Inputs p) :
    (p 4438) ∨ (¬ p 2417) :=
  ElevenRUP.step106119 (p 2417) (p 2459) (p 2911) (p 3657) (p 4438) (derived47903 p h) (derived96417 p h) (derived80109 p h) (derived75803 p h)

theorem derived106121 (p : Nat → Prop) (h : Inputs p) :
    (p 4438) ∨ (¬ p 2363) :=
  ElevenRUP.step106121 (p 2177) (p 2363) (p 2459) (p 2911) (p 3325) (p 4276) (p 4438) (derived97273 p h) (derived96473 p h) (derived105516 p h) (derived80109 p h) (derived47903 p h) (derived101391 p h)

theorem derived106122 (p : Nat → Prop) (h : Inputs p) :
    (p 4438) ∨ (¬ p 3343) :=
  ElevenRUP.step106122 (p 2528) (p 3083) (p 3343) (p 4045) (p 4438) (derived106114 p h) (derived98809 p h) (derived47818 p h) (derived79484 p h)

theorem derived106124 (p : Nat → Prop) (h : Inputs p) :
    (p 4438) ∨ (¬ p 2352) :=
  ElevenRUP.step106124 (p 2177) (p 2352) (p 2553) (p 2911) (p 3550) (p 3581) (p 4438) (p 4710) (derived106115 p h) (derived76948 p h) (derived102249 p h) (derived80109 p h) (derived97273 p h) (derived96472 p h) (derived91293 p h)

theorem derived106125 (p : Nat → Prop) (h : Inputs p) :
    (p 4438) ∨ (¬ p 2274) :=
  ElevenRUP.step106125 (p 2177) (p 2274) (p 2553) (p 2911) (p 3581) (p 3958) (p 4438) (p 4710) (derived106115 p h) (derived76948 p h) (derived102249 p h) (derived97273 p h) (derived105378 p h) (derived80109 p h) (derived91294 p h)

theorem derived106126 (p : Nat → Prop) (h : Inputs p) :
    (p 4438) ∨ (¬ p 2307) :=
  ElevenRUP.step106126 (p 2177) (p 2307) (p 2553) (p 2586) (p 2911) (p 3581) (p 4438) (p 4710) (derived106115 p h) (derived76948 p h) (derived102249 p h) (derived97273 p h) (derived105372 p h) (derived80109 p h) (derived78298 p h)

theorem derived106132 (p : Nat → Prop) (h : Inputs p) :
    (p 4438) ∨ (¬ p 3146) :=
  ElevenRUP.step106132 (p 2352) (p 2363) (p 3146) (p 3958) (p 4438) (derived106124 p h) (derived106121 p h) (derived105378 p h) (derived103615 p h)

theorem derived106134 (p : Nat → Prop) (h : Inputs p) :
    (p 4438) ∨ (¬ p 2383) :=
  ElevenRUP.step106134 (p 2177) (p 2307) (p 2383) (p 2911) (p 3550) (p 4276) (p 4438) (derived106126 p h) (derived105516 p h) (derived97273 p h) (derived96472 p h) (derived80109 p h) (derived83994 p h)

theorem derived106140 (p : Nat → Prop) (h : Inputs p) :
    (p 4438) ∨ (¬ p 2088) :=
  ElevenRUP.step106140 (p 2088) (p 2363) (p 2383) (p 4170) (p 4438) (derived106134 p h) (derived93717 p h) (derived106121 p h) (derived78481 p h)

theorem derived106141 (p : Nat → Prop) (h : Inputs p) :
    (p 4434) ∨ (¬ p 4042) :=
  ElevenRUP.step106141 (p 2528) (p 4042) (p 4434) (p 4438) (derived99553 p h) (derived106114 p h) (h 27360)

theorem derived106144 (p : Nat → Prop) (h : Inputs p) :
    (p 4434) :=
  ElevenRUP.step106144 (p 2373) (p 3693) (p 4042) (p 4132) (p 4383) (p 4434) (p 4902) (derived105456 p h) (h 23626) (derived98726 p h) (derived94352 p h) (derived106141 p h) (h 24643) (h 35557)

theorem derived106148 (p : Nat → Prop) (h : Inputs p) :
    (p 4433) ∨ (p 4042) :=
  ElevenRUP.step106148 (p 2187) (p 3550) (p 4042) (p 4138) (p 4433) (p 4441) (p 4902) (derived98660 p h) (derived93560 p h) (derived105456 p h) (h 23399) (h 6575) (h 28032)

theorem derived106150 (p : Nat → Prop) (h : Inputs p) :
    (p 4433) :=
  ElevenRUP.step106150 (p 2177) (p 4042) (p 4138) (p 4433) (p 4503) (p 4902) (derived106148 p h) (derived105456 p h) (h 23399) (derived87333 p h) (derived96475 p h) (h 28093)

theorem derived106160 (p : Nat → Prop) (h : Inputs p) :
    (p 4384) ∨ (¬ p 3550) :=
  ElevenRUP.step106160 (p 2911) (p 3550) (p 4133) (p 4383) (p 4384) (p 4438) (derived105712 p h) (h 6705) (derived85673 p h) (derived92939 p h) (h 36516)

theorem derived106163 (p : Nat → Prop) (h : Inputs p) :
    (p 4384) ∨ (¬ p 3921) :=
  ElevenRUP.step106163 (p 2177) (p 2911) (p 3550) (p 3921) (p 4133) (p 4383) (p 4384) (derived106160 p h) (derived74607 p h) (derived105712 p h) (h 6705) (derived85673 p h) (derived82414 p h)

theorem derived106167 (p : Nat → Prop) (h : Inputs p) :
    (p 4384) :=
  ElevenRUP.step106167 (p 2352) (p 2553) (p 2911) (p 3550) (p 3920) (p 3921) (p 4133) (p 4138) (p 4383) (p 4384) (derived106160 p h) (h 6575) (derived106163 p h) (derived98256 p h) (derived94485 p h) (derived80726 p h) (derived105712 p h) (h 6705) (derived85673 p h) (derived99544 p h)

theorem derived106170 (p : Nat → Prop) (h : Inputs p) :
    (p 4377) :=
  ElevenRUP.step106170 (p 2210) (p 2608) (p 2839) (p 3369) (p 3370) (p 3371) (p 4377) (derived47641 p h) (derived96464 p h) (derived99609 p h) (derived96372 p h) (derived75630 p h) (derived96465 p h) (h 4838)

theorem derived106171 (p : Nat → Prop) (h : Inputs p) :
    (p 4362) ∨ (¬ p 3745) :=
  ElevenRUP.step106171 (p 2274) (p 2295) (p 2298) (p 3745) (p 4140) (p 4361) (p 4362) (p 4556) (derived105382 p h) (h 6641) (derived77956 p h) (derived105399 p h) (h 34515) (derived98781 p h) (derived78662 p h)

theorem derived106173 (p : Nat → Prop) (h : Inputs p) :
    (p 4362) :=
  ElevenRUP.step106173 (p 2284) (p 2295) (p 2298) (p 2901) (p 3745) (p 4140) (p 4275) (p 4336) (p 4361) (p 4362) (p 4556) (derived105382 p h) (h 6641) (h 36100) (derived106171 p h) (derived77961 p h) (derived79172 p h) (derived105399 p h) (h 34515) (derived98781 p h) (derived97933 p h) (derived78210 p h)

theorem derived106174 (p : Nat → Prop) (h : Inputs p) :
    (p 4158) ∨ (¬ p 4506) :=
  ElevenRUP.step106174 (p 2352) (p 4134) (p 4157) (p 4158) (p 4506) (p 4596) (derived105379 p h) (h 6207) (derived80723 p h) (derived102250 p h) (h 31880)

theorem derived106175 (p : Nat → Prop) (h : Inputs p) :
    (p 4158) ∨ (¬ p 4241) :=
  ElevenRUP.step106175 (p 2373) (p 3156) (p 4158) (p 4241) (derived47993 p h) (derived78879 p h) (h 30118)

theorem derived106178 (p : Nat → Prop) (h : Inputs p) :
    (p 4158) ∨ (¬ p 3016) :=
  ElevenRUP.step106178 (p 2373) (p 2440) (p 3016) (p 3156) (p 4158) (p 4241) (p 4700) (p 4717) (derived47993 p h) (derived105424 p h) (derived78879 p h) (derived106175 p h) (derived74475 p h) (derived100363 p h) (derived83047 p h)

theorem derived106183 (p : Nat → Prop) (h : Inputs p) :
    (p 4158) ∨ (p 2668) :=
  ElevenRUP.step106183 (p 2187) (p 2373) (p 2668) (p 4158) (p 4506) (p 4702) (derived106174 p h) (derived92414 p h) (derived106079 p h) (derived78879 p h) (derived98552 p h)

theorem derived106187 (p : Nat → Prop) (h : Inputs p) :
    (p 4158) :=
  ElevenRUP.step106187 (p 2352) (p 2668) (p 3016) (p 4134) (p 4157) (p 4158) (p 4389) (derived106183 p h) (derived106178 p h) (derived96024 p h) (derived105379 p h) (h 6207) (derived80723 p h) (derived79209 p h)

theorem derived106188 (p : Nat → Prop) (h : Inputs p) :
    (p 5560) :=
  ElevenRUP.step106188 (p 3941) (p 5560) (p 6145) (p 6146) (derived48808 p h) (h 14268) (derived66622 p h) (h 14272)

theorem derived106189 (p : Nat → Prop) (h : Inputs p) :
    (p 5559) :=
  ElevenRUP.step106189 (p 3941) (p 5559) (p 6145) (p 6146) (derived43116 p h) (h 14267) (derived66622 p h) (h 14272)

theorem derived106196 (p : Nat → Prop) (h : Inputs p) :
    (p 5123) ∨ (¬ p 3438) :=
  ElevenRUP.step106196 (p 3266) (p 3438) (p 3707) (p 5123) (derived99573 p h) (derived84033 p h) (derived96838 p h)

theorem derived106197 (p : Nat → Prop) (h : Inputs p) :
    (p 5123) ∨ (¬ p 2696) :=
  ElevenRUP.step106197 (p 2696) (p 3266) (p 5117) (p 5123) (derived99573 p h) (derived96294 p h) (derived51542 p h)

theorem derived106198 (p : Nat → Prop) (h : Inputs p) :
    (p 5123) ∨ (¬ p 2608) :=
  ElevenRUP.step106198 (p 2608) (p 3266) (p 5117) (p 5123) (derived99573 p h) (derived96294 p h) (derived47604 p h)

theorem derived106199 (p : Nat → Prop) (h : Inputs p) :
    (p 5123) ∨ (¬ p 3830) :=
  ElevenRUP.step106199 (p 2608) (p 3266) (p 3707) (p 3830) (p 5123) (derived106198 p h) (derived84033 p h) (derived99573 p h) (derived100405 p h)

theorem derived106200 (p : Nat → Prop) (h : Inputs p) :
    (p 5123) ∨ (¬ p 2241) :=
  ElevenRUP.step106200 (p 2241) (p 2608) (p 2696) (p 3873) (p 5123) (derived106198 p h) (derived96408 p h) (derived106197 p h) (derived103787 p h)

theorem derived106203 (p : Nat → Prop) (h : Inputs p) :
    (p 5062) ∨ (¬ p 4119) :=
  ElevenRUP.step106203 (p 2901) (p 3156) (p 4119) (p 5062) (derived46477 p h) (derived79157 p h) (h 6474)

theorem derived106207 (p : Nat → Prop) (h : Inputs p) :
    (p 5062) ∨ (p 2177) :=
  ElevenRUP.step106207 (p 2177) (p 2881) (p 2901) (p 3156) (p 4042) (p 4119) (p 4559) (p 5062) (derived106203 p h) (derived87257 p h) (derived96358 p h) (derived46477 p h) (derived105701 p h) (derived79157 p h) (derived78130 p h)

theorem derived106208 (p : Nat → Prop) (h : Inputs p) :
    (p 4960) ∨ (¬ p 2241) :=
  ElevenRUP.step106208 (p 2210) (p 2241) (p 2946) (p 4960) (derived101734 p h) (derived43574 p h) (derived103838 p h)

theorem derived106209 (p : Nat → Prop) (h : Inputs p) :
    (p 4960) :=
  ElevenRUP.step106209 (p 2241) (p 2246) (p 2946) (p 2992) (p 4960) (derived101734 p h) (derived106208 p h) (derived96975 p h) (derived85845 p h) (derived103200 p h)

theorem derived106210 (p : Nat → Prop) (h : Inputs p) :
    (p 4911) ∨ (¬ p 3246) :=
  ElevenRUP.step106210 (p 2891) (p 3246) (p 3571) (p 3631) (p 4911) (derived44571 p h) (derived92624 p h) (derived102333 p h) (derived92550 p h)

theorem derived106216 (p : Nat → Prop) (h : Inputs p) :
    (p 4911) ∨ (¬ p 2982) :=
  ElevenRUP.step106216 (p 2427) (p 2982) (p 3246) (p 4395) (p 4911) (derived106210 p h) (derived102356 p h) (derived47662 p h) (derived100886 p h)

theorem derived106221 (p : Nat → Prop) (h : Inputs p) :
    (p 4889) ∨ (p 3367) :=
  ElevenRUP.step106221 (p 2829) (p 3367) (p 3422) (p 3958) (p 4390) (p 4889) (p 5220) (derived105378 p h) (h 25032) (derived77553 p h) (derived97817 p h) (derived90429 p h) (derived77760 p h)

theorem derived106222 (p : Nat → Prop) (h : Inputs p) :
    (p 4875) ∨ (¬ p 2143) :=
  ElevenRUP.step106222 (p 2143) (p 2210) (p 4525) (p 4875) (derived75448 p h) (derived102413 p h) (h 25182)

theorem derived106227 (p : Nat → Prop) (h : Inputs p) :
    (p 4875) :=
  ElevenRUP.step106227 (p 2143) (p 2210) (p 2839) (p 3645) (p 4243) (p 4875) (derived106222 p h) (derived99610 p h) (derived96373 p h) (derived75448 p h) (derived101225 p h) (h 17146)

theorem derived106233 (p : Nat → Prop) (h : Inputs p) :
    (p 4761) ∨ (¬ p 4389) :=
  ElevenRUP.step106233 (p 2498) (p 2641) (p 4319) (p 4389) (p 4761) (p 4973) (derived105835 p h) (h 21877) (derived85988 p h) (derived85599 p h) (h 27249)

theorem derived106234 (p : Nat → Prop) (h : Inputs p) :
    (p 4761) :=
  ElevenRUP.step106234 (p 2493) (p 2498) (p 2507) (p 3984) (p 4389) (p 4761) (p 4973) (derived106233 p h) (h 21247) (derived105835 p h) (h 21877) (derived99258 p h) (derived96946 p h) (h 25039)

theorem derived106237 (p : Nat → Prop) (h : Inputs p) :
    (p 4705) ∨ (¬ p 2663) :=
  ElevenRUP.step106237 (p 2230) (p 2440) (p 2663) (p 3879) (p 4705) (derived101700 p h) (derived74477 p h) (derived100365 p h) (derived51878 p h)

theorem derived106238 (p : Nat → Prop) (h : Inputs p) :
    (p 4705) :=
  ElevenRUP.step106238 (p 2230) (p 2440) (p 2651) (p 2656) (p 2663) (p 4705) (derived101700 p h) (derived106237 p h) (derived78221 p h) (derived87995 p h) (derived74477 p h) (h 5209)

theorem derived106244 (p : Nat → Prop) (h : Inputs p) :
    (p 4650) ∨ (¬ p 2996) :=
  ElevenRUP.step106244 (p 2437) (p 2727) (p 2996) (p 3580) (p 4650) (derived75100 p h) (derived102335 p h) (derived100201 p h) (derived82316 p h)

theorem derived106245 (p : Nat → Prop) (h : Inputs p) :
    (p 4650) ∨ (p 2807) :=
  ElevenRUP.step106245 (p 2437) (p 2651) (p 2807) (p 3580) (p 4650) (derived75100 p h) (derived102335 p h) (derived98090 p h) (h 6564)

theorem derived106246 (p : Nat → Prop) (h : Inputs p) :
    (p 4650) ∨ (¬ p 3093) :=
  ElevenRUP.step106246 (p 2437) (p 3093) (p 3580) (p 4650) (derived75100 p h) (derived102335 p h) (derived47420 p h)

theorem derived106249 (p : Nat → Prop) (h : Inputs p) :
    (p 4650) ∨ (¬ p 2241) :=
  ElevenRUP.step106249 (p 2241) (p 2727) (p 3093) (p 4650) (p 4972) (derived106246 p h) (derived100201 p h) (derived105836 p h) (derived80454 p h)

theorem derived106250 (p : Nat → Prop) (h : Inputs p) :
    (p 4632) ∨ (¬ p 4418) :=
  ElevenRUP.step106250 (p 2230) (p 4418) (p 4632) (p 4885) (derived97780 p h) (derived106027 p h) (h 25401)

theorem derived106251 (p : Nat → Prop) (h : Inputs p) :
    (p 4632) ∨ (p 2608) :=
  ElevenRUP.step106251 (p 2230) (p 2406) (p 2608) (p 4632) (derived97780 p h) (derived76241 p h) (derived103475 p h)

theorem derived106257 (p : Nat → Prop) (h : Inputs p) :
    (p 4632) :=
  ElevenRUP.step106257 (p 2210) (p 2608) (p 2839) (p 3369) (p 3370) (p 3371) (p 3645) (p 4418) (p 4539) (p 4632) (derived106250 p h) (derived99608 p h) (derived96372 p h) (derived106251 p h) (derived105395 p h) (h 26853) (derived97487 p h) (derived96464 p h) (h 6404) (h 4838)

theorem derived106258 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (p 2449) :=
  ElevenRUP.step106258 (p 2295) (p 2396) (p 2449) (p 3552) (p 4620) (derived100890 p h) (derived98611 p h) (derived96452 p h) (h 6739)

theorem derived106260 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (p 3323) :=
  ElevenRUP.step106260 (p 2295) (p 2396) (p 3323) (p 4187) (p 4620) (derived100890 p h) (derived91160 p h) (derived98611 p h) (derived78664 p h)

theorem derived106261 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (¬ p 3955) :=
  ElevenRUP.step106261 (p 2396) (p 3955) (p 3990) (p 4187) (p 4620) (derived100890 p h) (derived91160 p h) (derived72306 p h) (h 23052)

theorem derived106262 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (p 2241) :=
  ElevenRUP.step106262 (p 2241) (p 2396) (p 4187) (p 4620) (p 5190) (derived100890 p h) (derived91160 p h) (derived105487 p h) (derived95377 p h)

theorem derived106263 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (¬ p 2608) :=
  ElevenRUP.step106263 (p 2396) (p 2608) (p 4187) (p 4620) (derived100890 p h) (derived91160 p h) (derived64133 p h)

theorem derived106264 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (¬ p 2459) :=
  ElevenRUP.step106264 (p 2177) (p 2363) (p 2459) (p 3550) (p 3955) (p 3990) (p 4620) (derived72306 p h) (derived90096 p h) (derived106261 p h) (derived78595 p h) (derived96472 p h) (derived74478 p h)

theorem derived106266 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (p 2881) :=
  ElevenRUP.step106266 (p 2177) (p 2295) (p 2881) (p 3955) (p 4620) (derived106261 p h) (derived78595 p h) (derived98611 p h) (derived102838 p h)

theorem derived106267 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (p 2264) :=
  ElevenRUP.step106267 (p 2177) (p 2264) (p 2295) (p 3552) (p 3955) (p 4620) (derived106261 p h) (derived78595 p h) (derived98611 p h) (derived96452 p h) (derived76676 p h)

theorem derived106268 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (¬ p 2641) :=
  ElevenRUP.step106268 (p 2177) (p 2241) (p 2295) (p 2641) (p 3955) (p 4620) (derived106262 p h) (derived98611 p h) (derived106261 p h) (derived78595 p h) (derived43081 p h)

theorem derived106269 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (¬ p 2741) :=
  ElevenRUP.step106269 (p 2241) (p 2608) (p 2741) (p 4620) (derived106262 p h) (derived106263 p h) (derived75632 p h)

theorem derived106271 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (¬ p 2685) :=
  ElevenRUP.step106271 (p 2241) (p 2264) (p 2608) (p 2685) (p 2737) (p 2741) (p 2748) (p 4620) (derived106262 p h) (derived106263 p h) (derived106267 p h) (derived106269 p h) (derived80753 p h) (derived86489 p h) (derived97610 p h)

theorem derived106273 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (p 2996) :=
  ElevenRUP.step106273 (p 2241) (p 2449) (p 2608) (p 2996) (p 4620) (derived106262 p h) (derived106258 p h) (derived106263 p h) (derived75635 p h)

theorem derived106276 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (¬ p 2331) :=
  ElevenRUP.step106276 (p 2241) (p 2253) (p 2331) (p 2608) (p 2641) (p 2737) (p 2741) (p 2750) (p 4620) (derived106263 p h) (derived106262 p h) (derived82153 p h) (derived106269 p h) (derived80753 p h) (derived100642 p h) (derived106268 p h) (derived100014 p h)

theorem derived106277 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (¬ p 2807) :=
  ElevenRUP.step106277 (p 2241) (p 2253) (p 2608) (p 2737) (p 2741) (p 2750) (p 2807) (p 2996) (p 4620) (derived106263 p h) (derived106262 p h) (derived82153 p h) (derived106269 p h) (derived80753 p h) (derived100642 p h) (derived106273 p h) (derived99947 p h)

theorem derived106280 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (p 2774) :=
  ElevenRUP.step106280 (p 2241) (p 2608) (p 2737) (p 2741) (p 2774) (p 4620) (derived106269 p h) (derived80753 p h) (derived106263 p h) (derived106262 p h) (derived103488 p h)

theorem derived106282 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (p 2829) :=
  ElevenRUP.step106282 (p 2241) (p 2608) (p 2641) (p 2737) (p 2741) (p 2748) (p 2829) (p 4620) (p 4842) (derived106269 p h) (derived80753 p h) (derived86489 p h) (derived106263 p h) (derived106268 p h) (derived106066 p h) (derived106262 p h) (derived90477 p h)

theorem derived106283 (p : Nat → Prop) (h : Inputs p) :
    (p 4620) ∨ (p 2839) :=
  ElevenRUP.step106283 (p 2241) (p 2608) (p 2737) (p 2741) (p 2748) (p 2839) (p 4620) (derived106269 p h) (derived80753 p h) (derived86489 p h) (derived106262 p h) (derived106263 p h) (derived97609 p h)

theorem derived106289 (p : Nat → Prop) (h : Inputs p) :
    (p 4604) ∨ (¬ p 3564) :=
  ElevenRUP.step106289 (p 2363) (p 3564) (p 4604) (derived98813 p h) (derived79506 p h)

theorem derived106291 (p : Nat → Prop) (h : Inputs p) :
    (p 4604) ∨ (¬ p 2352) :=
  ElevenRUP.step106291 (p 2352) (p 2363) (p 3146) (p 3564) (p 4134) (p 4171) (p 4604) (derived98661 p h) (derived106289 p h) (derived98813 p h) (derived96436 p h) (derived105379 p h) (derived78777 p h)

theorem derived106293 (p : Nat → Prop) (h : Inputs p) :
    (p 4604) :=
  ElevenRUP.step106293 (p 2352) (p 2363) (p 3146) (p 3958) (p 4604) (derived98661 p h) (derived106291 p h) (derived98813 p h) (derived105378 p h) (derived103615 p h)

theorem derived106294 (p : Nat → Prop) (h : Inputs p) :
    (p 4595) ∨ (p 2819) :=
  ElevenRUP.step106294 (p 2352) (p 2819) (p 3422) (p 4390) (p 4595) (derived99502 p h) (derived101293 p h) (derived96274 p h) (derived87951 p h)

theorem derived106295 (p : Nat → Prop) (h : Inputs p) :
    (p 4595) ∨ (p 3641) :=
  ElevenRUP.step106295 (p 2352) (p 2510) (p 3422) (p 3641) (p 4595) (derived99502 p h) (derived96441 p h) (derived101293 p h) (h 18786)

theorem derived106296 (p : Nat → Prop) (h : Inputs p) :
    (p 4595) ∨ (¬ p 2573) :=
  ElevenRUP.step106296 (p 2352) (p 2470) (p 2510) (p 2573) (p 4595) (derived99502 p h) (derived96441 p h) (derived47972 p h) (derived74786 p h)

theorem derived106297 (p : Nat → Prop) (h : Inputs p) :
    (p 4595) ∨ (¬ p 3363) :=
  ElevenRUP.step106297 (p 2470) (p 3363) (p 3641) (p 4595) (derived106295 p h) (derived47972 p h) (derived75783 p h)

theorem derived106299 (p : Nat → Prop) (h : Inputs p) :
    (p 4595) ∨ (¬ p 2098) :=
  ElevenRUP.step106299 (p 2098) (p 2470) (p 2598) (p 3363) (p 4595) (derived106297 p h) (derived97802 p h) (derived47972 p h) (derived93152 p h)

theorem derived106300 (p : Nat → Prop) (h : Inputs p) :
    (p 4595) ∨ (¬ p 3367) :=
  ElevenRUP.step106300 (p 2573) (p 2598) (p 3363) (p 3367) (p 3422) (p 3905) (p 4595) (derived106297 p h) (derived97802 p h) (derived95981 p h) (derived106296 p h) (derived101293 p h) (derived77581 p h)

theorem derived106303 (p : Nat → Prop) (h : Inputs p) :
    (p 4595) ∨ (¬ p 2774) :=
  ElevenRUP.step106303 (p 2098) (p 2774) (p 2819) (p 4595) (p 4861) (derived106299 p h) (derived106294 p h) (derived96379 p h) (derived101502 p h)

theorem derived106305 (p : Nat → Prop) (h : Inputs p) :
    (p 4595) ∨ (¬ p 2829) :=
  ElevenRUP.step106305 (p 2573) (p 2829) (p 3367) (p 3422) (p 4390) (p 4595) (derived106300 p h) (derived106296 p h) (derived101293 p h) (derived96274 p h) (derived87961 p h)

theorem derived106307 (p : Nat → Prop) (h : Inputs p) :
    (p 4566) :=
  ElevenRUP.step106307 (p 2284) (p 2331) (p 2667) (p 2946) (p 3987) (p 4153) (p 4566) (derived45167 p h) (derived98507 p h) (derived95238 p h) (derived101082 p h) (derived96449 p h) (derived96448 p h) (derived94324 p h)

theorem derived106308 (p : Nat → Prop) (h : Inputs p) :
    (p 4401) ∨ (¬ p 2137) :=
  ElevenRUP.step106308 (p 2137) (p 2156) (p 2860) (p 4401) (derived100459 p h) (derived85379 p h) (derived83249 p h)

theorem derived106309 (p : Nat → Prop) (h : Inputs p) :
    (p 4401) ∨ (p 2696) :=
  ElevenRUP.step106309 (p 2132) (p 2137) (p 2144) (p 2156) (p 2696) (p 2860) (p 4401) (p 5052) (derived100459 p h) (derived105473 p h) (derived106308 p h) (derived99783 p h) (derived96982 p h) (derived85379 p h) (derived93705 p h)

theorem derived106310 (p : Nat → Prop) (h : Inputs p) :
    (p 4401) ∨ (p 3745) :=
  ElevenRUP.step106310 (p 2860) (p 3745) (p 4328) (p 4337) (p 4401) (p 4428) (derived100459 p h) (derived95791 p h) (derived102207 p h) (h 6576) (h 21886)

theorem derived106312 (p : Nat → Prop) (h : Inputs p) :
    (p 4401) ∨ (p 2839) :=
  ElevenRUP.step106312 (p 2132) (p 2137) (p 2144) (p 2156) (p 2839) (p 2860) (p 4401) (derived106308 p h) (derived99783 p h) (derived96982 p h) (derived100459 p h) (derived85379 p h) (derived93702 p h)

theorem derived106313 (p : Nat → Prop) (h : Inputs p) :
    (p 4401) ∨ (p 2774) :=
  ElevenRUP.step106313 (p 2696) (p 2774) (p 2797) (p 4337) (p 4401) (p 4426) (derived106309 p h) (derived102207 p h) (derived90911 p h) (derived96383 p h) (derived86392 p h)

theorem derived106314 (p : Nat → Prop) (h : Inputs p) :
    (p 4401) ∨ (p 2331) :=
  ElevenRUP.step106314 (p 2331) (p 2696) (p 2797) (p 3361) (p 4337) (p 4401) (derived106309 p h) (derived101923 p h) (derived102207 p h) (derived90911 p h) (derived88536 p h)

theorem derived106315 (p : Nat → Prop) (h : Inputs p) :
    (p 4401) ∨ (p 2829) :=
  ElevenRUP.step106315 (p 2156) (p 2829) (p 2839) (p 2860) (p 4401) (p 4428) (derived106312 p h) (derived100459 p h) (derived95791 p h) (derived85379 p h) (derived83683 p h)

theorem derived106316 (p : Nat → Prop) (h : Inputs p) :
    (p 4401) ∨ (p 2782) :=
  ElevenRUP.step106316 (p 2331) (p 2667) (p 2782) (p 2797) (p 4337) (p 4401) (p 4846) (derived106314 p h) (derived96448 p h) (derived102207 p h) (derived90911 p h) (derived96385 p h) (h 27586)

theorem derived106320 (p : Nat → Prop) (h : Inputs p) :
    (p 4376) :=
  ElevenRUP.step106320 (p 2608) (p 3367) (p 3379) (p 3541) (p 4376) (derived52229 p h) (derived75628 p h) (derived75541 p h) (derived99791 p h) (derived81739 p h)

theorem derived106323 (p : Nat → Prop) (h : Inputs p) :
    (p 4330) ∨ (¬ p 4113) :=
  ElevenRUP.step106323 (p 2088) (p 2363) (p 4113) (p 4330) (derived78594 p h) (derived45341 p h) (derived78491 p h)

theorem derived106324 (p : Nat → Prop) (h : Inputs p) :
    (p 4330) ∨ (p 3654) :=
  ElevenRUP.step106324 (p 2363) (p 3654) (p 4330) (derived78594 p h) (derived100647 p h)

theorem derived106325 (p : Nat → Prop) (h : Inputs p) :
    (p 4330) ∨ (p 2177) :=
  ElevenRUP.step106325 (p 2177) (p 2363) (p 2459) (p 4330) (derived47704 p h) (derived78594 p h) (derived101349 p h)

theorem derived106329 (p : Nat → Prop) (h : Inputs p) :
    (p 4330) :=
  ElevenRUP.step106329 (p 2177) (p 2363) (p 2383) (p 2459) (p 3654) (p 4113) (p 4330) (p 4345) (p 4503) (derived106324 p h) (derived78594 p h) (derived99552 p h) (derived106325 p h) (derived96475 p h) (derived106323 p h) (derived78416 p h) (derived47704 p h) (derived90927 p h)

theorem derived106330 (p : Nat → Prop) (h : Inputs p) :
    (p 2781) ∨ (p 3873) :=
  ElevenRUP.step106330 (p 2774) (p 2781) (p 2786) (p 3093) (p 3873) (p 4736) (p 5015) (p 5020) (derived105431 p h) (h 34674) (derived100614 p h) (derived95391 p h) (derived86486 p h) (derived102220 p h) (h 11023)

theorem derived106331 (p : Nat → Prop) (h : Inputs p) :
    (p 2781) ∨ (¬ p 3987) :=
  ElevenRUP.step106331 (p 2248) (p 2781) (p 3873) (p 3987) (derived106330 p h) (derived105365 p h) (h 33967)

theorem derived106334 (p : Nat → Prop) (h : Inputs p) :
    (p 2751) ∨ (p 2608) :=
  ElevenRUP.step106334 (p 2608) (p 2737) (p 2751) (derived100370 p h) (derived81266 p h)

theorem derived106335 (p : Nat → Prop) (h : Inputs p) :
    (p 2751) ∨ (¬ p 2651) :=
  ElevenRUP.step106335 (p 2651) (p 2737) (p 2742) (p 2751) (derived100370 p h) (derived96922 p h) (derived43998 p h)

theorem derived106339 (p : Nat → Prop) (h : Inputs p) :
    (p 2751) ∨ (¬ p 2245) :=
  ElevenRUP.step106339 (p 2245) (p 2608) (p 2651) (p 2727) (p 2737) (p 2744) (p 2751) (derived106335 p h) (derived106334 p h) (derived100370 p h) (derived96920 p h) (derived100204 p h) (derived93433 p h)

theorem derived106343 (p : Nat → Prop) (h : Inputs p) :
    (p 2751) :=
  ElevenRUP.step106343 (p 2241) (p 2245) (p 2252) (p 2651) (p 2727) (p 2751) (p 3487) (p 4281) (derived106335 p h) (derived106339 p h) (derived75366 p h) (derived102287 p h) (derived100204 p h) (derived95900 p h) (derived95899 p h) (derived91829 p h)

theorem derived106345 (p : Nat → Prop) (h : Inputs p) :
    (p 2750) :=
  ElevenRUP.step106345 (p 2241) (p 2608) (p 2737) (p 2741) (p 2750) (derived100369 p h) (derived96923 p h) (derived80775 p h) (derived45313 p h) (derived75633 p h)

theorem derived106347 (p : Nat → Prop) (h : Inputs p) :
    (p 2478) ∨ (¬ p 3519) :=
  ElevenRUP.step106347 (p 2470) (p 2478) (p 2518) (p 3519) (derived45551 p h) (derived101662 p h) (h 26933)

theorem derived106350 (p : Nat → Prop) (h : Inputs p) :
    (p 2478) ∨ (p 2608) :=
  ElevenRUP.step106350 (p 2470) (p 2478) (p 2509) (p 2518) (p 2608) (p 3379) (p 3519) (p 4079) (p 4683) (p 4686) (derived106347 p h) (derived75362 p h) (derived87993 p h) (derived101662 p h) (derived45551 p h) (h 7556) (derived66365 p h) (h 7550) (derived75711 p h)

theorem derived106353 (p : Nat → Prop) (h : Inputs p) :
    (p 5472) ∨ (¬ p 4442) :=
  ElevenRUP.step106353 (p 3791) (p 4442) (p 5469) (p 5472) (p 5474) (h 9482) (derived66477 p h) (h 9487) (derived45562 p h)

theorem derived106357 (p : Nat → Prop) (h : Inputs p) :
    (p 5257) ∨ (p 2598) :=
  ElevenRUP.step106357 (p 2598) (p 3425) (p 3819) (p 5257) (derived90915 p h) (derived102064 p h) (derived89907 p h)

theorem derived106360 (p : Nat → Prop) (h : Inputs p) :
    (p 5119) ∨ (¬ p 4695) :=
  ElevenRUP.step106360 (p 3266) (p 3276) (p 4695) (p 5119) (derived43265 p h) (derived80752 p h) (derived79534 p h)

theorem derived106361 (p : Nat → Prop) (h : Inputs p) :
    (p 5119) ∨ (¬ p 2427) :=
  ElevenRUP.step106361 (p 2427) (p 3266) (p 5119) (p 5121) (derived80752 p h) (derived102658 p h) (derived53924 p h)

theorem derived106362 (p : Nat → Prop) (h : Inputs p) :
    (p 5119) ∨ (¬ p 2573) :=
  ElevenRUP.step106362 (p 2573) (p 3266) (p 5119) (p 5121) (derived80752 p h) (derived102658 p h) (derived50073 p h)

theorem derived106363 (p : Nat → Prop) (h : Inputs p) :
    (p 5119) ∨ (¬ p 2088) :=
  ElevenRUP.step106363 (p 2088) (p 2484) (p 2528) (p 3266) (p 3276) (p 4045) (p 4695) (p 5119) (derived106360 p h) (derived80717 p h) (derived98809 p h) (derived80752 p h) (derived105370 p h) (derived43265 p h) (derived79540 p h)

theorem derived106364 (p : Nat → Prop) (h : Inputs p) :
    (p 5119) ∨ (¬ p 2459) :=
  ElevenRUP.step106364 (p 2459) (p 2528) (p 3266) (p 3276) (p 4045) (p 4420) (p 4695) (p 5119) (derived106360 p h) (derived80717 p h) (derived98809 p h) (derived80752 p h) (derived105707 p h) (derived43265 p h) (derived99594 p h)

theorem derived106365 (p : Nat → Prop) (h : Inputs p) :
    (p 5104) ∨ (p 2427) :=
  ElevenRUP.step106365 (p 2427) (p 2982) (p 3246) (p 4395) (p 5104) (derived78108 p h) (derived102356 p h) (derived92042 p h) (derived100886 p h)

theorem derived106367 (p : Nat → Prop) (h : Inputs p) :
    (p 5059) ∨ (p 4445) :=
  ElevenRUP.step106367 (p 3146) (p 3246) (p 3949) (p 4135) (p 4382) (p 4445) (p 4669) (p 5059) (derived105415 p h) (h 27415) (derived93100 p h) (derived96169 p h) (derived78875 p h) (derived93632 p h) (h 22440)

theorem derived106370 (p : Nat → Prop) (h : Inputs p) :
    (p 5017) ∨ (¬ p 2245) :=
  ElevenRUP.step106370 (p 2245) (p 2248) (p 3093) (p 3987) (p 5017) (p 5020) (derived105365 p h) (h 22609) (derived80525 p h) (derived102428 p h) (h 30693)

theorem derived106373 (p : Nat → Prop) (h : Inputs p) :
    (p 4957) ∨ (p 2870) :=
  ElevenRUP.step106373 (p 2751) (p 2870) (p 2901) (p 2992) (p 4957) (derived101299 p h) (derived106343 p h) (derived78110 p h) (derived68388 p h)

theorem derived106374 (p : Nat → Prop) (h : Inputs p) :
    (p 4957) ∨ (¬ p 2996) :=
  ElevenRUP.step106374 (p 2901) (p 2992) (p 2995) (p 2996) (p 4957) (derived78110 p h) (derived85984 p h) (derived101299 p h) (h 4117)

theorem derived106375 (p : Nat → Prop) (h : Inputs p) :
    (p 4957) ∨ (p 2891) :=
  ElevenRUP.step106375 (p 2891) (p 2901) (p 2992) (p 4282) (p 4957) (derived101299 p h) (derived96339 p h) (derived78110 p h) (h 36523)

theorem derived106377 (p : Nat → Prop) (h : Inputs p) :
    (p 4953) ∨ (p 4032) :=
  ElevenRUP.step106377 (p 2230) (p 2982) (p 4032) (p 4109) (p 4953) (derived45177 p h) (derived91693 p h) (derived102271 p h) (derived92086 p h)

theorem derived106379 (p : Nat → Prop) (h : Inputs p) :
    (p 4953) ∨ (¬ p 3355) :=
  ElevenRUP.step106379 (p 2230) (p 2982) (p 3237) (p 3355) (p 4953) (derived102271 p h) (derived96343 p h) (derived45177 p h) (derived85036 p h)

theorem derived106383 (p : Nat → Prop) (h : Inputs p) :
    (p 4917) ∨ (¬ p 2996) :=
  ElevenRUP.step106383 (p 2901) (p 2992) (p 2995) (p 2996) (p 4917) (derived78213 p h) (derived85984 p h) (derived99816 p h) (h 4117)

theorem derived106385 (p : Nat → Prop) (h : Inputs p) :
    (p 4895) ∨ (¬ p 4275) :=
  ElevenRUP.step106385 (p 2870) (p 4275) (p 4344) (p 4473) (p 4556) (p 4895) (derived86562 p h) (derived88197 p h) (derived105399 p h) (h 31691) (h 34265)

theorem derived106386 (p : Nat → Prop) (h : Inputs p) :
    (p 4881) ∨ (¬ p 4109) :=
  ElevenRUP.step106386 (p 2850) (p 4109) (p 4881) (derived98845 p h) (derived48818 p h)

theorem derived106388 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (¬ p 5016) :=
  ElevenRUP.step106388 (p 2829) (p 4867) (p 5016) (derived90428 p h) (derived48582 p h)

theorem derived106389 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (¬ p 3366) :=
  ElevenRUP.step106389 (p 2774) (p 2829) (p 3366) (p 4867) (derived43131 p h) (derived90428 p h) (derived86302 p h)

theorem derived106392 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (¬ p 3379) :=
  ElevenRUP.step106392 (p 2608) (p 2774) (p 2829) (p 3366) (p 3379) (p 3873) (p 4867) (derived106389 p h) (derived87228 p h) (derived96408 p h) (derived43131 p h) (derived90428 p h) (derived86312 p h)

theorem derived106393 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (¬ p 2241) :=
  ElevenRUP.step106393 (p 2241) (p 2608) (p 2750) (p 2774) (p 2829) (p 3366) (p 3873) (p 4867) (derived106389 p h) (derived87228 p h) (derived96408 p h) (derived106345 p h) (derived90428 p h) (derived43131 p h) (derived86318 p h)

theorem derived106395 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (¬ p 2497) :=
  ElevenRUP.step106395 (p 2497) (p 3093) (p 3379) (p 4867) (p 5016) (derived106392 p h) (derived106388 p h) (derived80524 p h) (derived88187 p h)

theorem derived106397 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (¬ p 4245) :=
  ElevenRUP.step106397 (p 2241) (p 3093) (p 4245) (p 4867) (p 5016) (derived106393 p h) (derived106388 p h) (derived80524 p h) (derived83601 p h)

theorem derived106398 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (p 2727) :=
  ElevenRUP.step106398 (p 2241) (p 2641) (p 2727) (p 3093) (p 3922) (p 4245) (p 4867) (p 4975) (p 5016) (derived106393 p h) (derived105464 p h) (derived106388 p h) (derived80524 p h) (derived106397 p h) (derived100553 p h) (derived96021 p h) (derived93584 p h)

theorem derived106399 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (p 3987) :=
  ElevenRUP.step106399 (p 2241) (p 2245) (p 3093) (p 3987) (p 4867) (p 5016) (p 5020) (derived106393 p h) (derived96976 p h) (derived106388 p h) (derived80524 p h) (derived102428 p h) (h 30693)

theorem derived106401 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (p 3422) :=
  ElevenRUP.step106401 (p 2493) (p 2497) (p 2504) (p 3093) (p 3379) (p 3422) (p 4867) (p 5016) (p 5217) (derived106395 p h) (derived99257 p h) (derived96944 p h) (derived106388 p h) (derived80524 p h) (derived105493 p h) (derived106392 p h) (derived87319 p h)

theorem derived106403 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (¬ p 3567) :=
  ElevenRUP.step106403 (p 2641) (p 3567) (p 3922) (p 4245) (p 4867) (p 5016) (derived106397 p h) (derived100553 p h) (derived96021 p h) (derived106388 p h) (h 22555)

theorem derived106404 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (¬ p 2598) :=
  ElevenRUP.step106404 (p 2598) (p 2774) (p 3422) (p 4375) (p 4867) (derived106401 p h) (derived96275 p h) (derived43131 p h) (h 6675)

theorem derived106405 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (¬ p 2696) :=
  ElevenRUP.step106405 (p 2598) (p 2696) (p 2727) (p 2751) (p 4867) (derived106404 p h) (derived106398 p h) (derived106343 p h) (derived80989 p h)

theorem derived106406 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (¬ p 2737) :=
  ElevenRUP.step106406 (p 2608) (p 2696) (p 2737) (p 2829) (p 3093) (p 3366) (p 3873) (p 4867) (p 4870) (p 5016) (derived106405 p h) (derived90428 p h) (derived102586 p h) (derived106389 p h) (derived87228 p h) (derived96408 p h) (derived106388 p h) (derived80524 p h) (derived96029 p h)

theorem derived106407 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) ∨ (p 2797) :=
  ElevenRUP.step106407 (p 2667) (p 2696) (p 2797) (p 2811) (p 3567) (p 3987) (p 4867) (derived106405 p h) (derived91165 p h) (derived106403 p h) (h 6927) (derived106399 p h) (derived81848 p h)

theorem derived106410 (p : Nat → Prop) (h : Inputs p) :
    (p 4867) :=
  ElevenRUP.step106410 (p 2608) (p 2737) (p 2797) (p 2829) (p 3093) (p 3366) (p 4024) (p 4845) (p 4867) (p 5016) (derived106406 p h) (derived106407 p h) (derived96384 p h) (derived90428 p h) (derived102285 p h) (derived106388 p h) (derived80524 p h) (derived106389 p h) (derived87228 p h) (derived91808 p h)

theorem derived106411 (p : Nat → Prop) (h : Inputs p) :
    (p 4854) ∨ (¬ p 3740) :=
  ElevenRUP.step106411 (p 2807) (p 3575) (p 3740) (p 4066) (p 4327) (p 4854) (derived105381 p h) (h 34279) (derived75414 p h) (derived93396 p h) (h 23380)

theorem derived106412 (p : Nat → Prop) (h : Inputs p) :
    (p 4854) ∨ (¬ p 2651) :=
  ElevenRUP.step106412 (p 2437) (p 2651) (p 2807) (p 3580) (p 3740) (p 4854) (derived106411 p h) (derived75099 p h) (derived102335 p h) (derived75414 p h) (h 6564)

theorem derived106413 (p : Nat → Prop) (h : Inputs p) :
    (p 4846) ∨ (p 2295) :=
  ElevenRUP.step106413 (p 2122) (p 2295) (p 2797) (p 4337) (p 4846) (derived87130 p h) (derived90912 p h) (derived97818 p h) (derived98653 p h)

theorem derived106414 (p : Nat → Prop) (h : Inputs p) :
    (p 4845) ∨ (¬ p 2667) :=
  ElevenRUP.step106414 (p 2667) (p 2797) (p 4845) (derived87129 p h) (derived101572 p h)

theorem derived106415 (p : Nat → Prop) (h : Inputs p) :
    (p 4845) ∨ (¬ p 3019) :=
  ElevenRUP.step106415 (p 2630) (p 2797) (p 3019) (p 4845) (derived100557 p h) (derived87129 p h) (derived87216 p h)

theorem derived106418 (p : Nat → Prop) (h : Inputs p) :
    (p 4845) ∨ (¬ p 2573) :=
  ElevenRUP.step106418 (p 2573) (p 2630) (p 2665) (p 2797) (p 3016) (p 3019) (p 4389) (p 4845) (derived106415 p h) (derived101603 p h) (derived96024 p h) (derived100557 p h) (derived105373 p h) (derived87129 p h) (derived87037 p h)

theorem derived106420 (p : Nat → Prop) (h : Inputs p) :
    (p 4832) ∨ (¬ p 3546) :=
  ElevenRUP.step106420 (p 3527) (p 3546) (p 4832) (derived101716 p h) (derived48432 p h)

theorem derived106424 (p : Nat → Prop) (h : Inputs p) :
    (p 4790) :=
  ElevenRUP.step106424 (p 2696) (p 2811) (p 4790) (derived105360 p h) (derived100368 p h) (derived91165 p h)

theorem derived106425 (p : Nat → Prop) (h : Inputs p) :
    (p 4786) :=
  ElevenRUP.step106425 (p 2696) (p 4786) (derived81802 p h) (derived105614 p h)

theorem derived106431 (p : Nat → Prop) (h : Inputs p) :
    (p 4757) ∨ (¬ p 2241) :=
  ElevenRUP.step106431 (p 2241) (p 2641) (p 4757) (derived101297 p h) (derived46950 p h)

theorem derived106434 (p : Nat → Prop) (h : Inputs p) :
    (p 4756) ∨ (¬ p 2241) :=
  ElevenRUP.step106434 (p 2241) (p 2641) (p 3093) (p 4756) (p 4759) (derived101296 p h) (derived96022 p h) (derived45216 p h) (derived80422 p h)

theorem derived106435 (p : Nat → Prop) (h : Inputs p) :
    (p 4653) ∨ (¬ p 2656) :=
  ElevenRUP.step106435 (p 2437) (p 2656) (p 3389) (p 4653) (derived99984 p h) (derived98008 p h) (derived75170 p h)

theorem derived106436 (p : Nat → Prop) (h : Inputs p) :
    (p 4653) ∨ (p 2807) :=
  ElevenRUP.step106436 (p 2437) (p 2651) (p 2656) (p 2663) (p 2807) (p 3389) (p 3740) (p 4653) (derived98008 p h) (derived96076 p h) (derived99984 p h) (derived106435 p h) (derived87994 p h) (derived96927 p h) (derived75831 p h)

theorem derived106437 (p : Nat → Prop) (h : Inputs p) :
    (p 4653) ∨ (p 2630) :=
  ElevenRUP.step106437 (p 2437) (p 2630) (p 2651) (p 2656) (p 2663) (p 3389) (p 4653) (p 4790) (derived106435 p h) (derived87994 p h) (derived96927 p h) (derived106424 p h) (derived98008 p h) (derived99984 p h) (derived84424 p h)

theorem derived106443 (p : Nat → Prop) (h : Inputs p) :
    (p 4625) ∨ (¬ p 4171) :=
  ElevenRUP.step106443 (p 2459) (p 3950) (p 4171) (p 4443) (p 4604) (p 4625) (derived106293 p h) (h 26957) (derived87657 p h) (derived96419 p h) (h 27824)

theorem derived106450 (p : Nat → Prop) (h : Inputs p) :
    (p 4625) ∨ (p 2177) :=
  ElevenRUP.step106450 (p 2177) (p 2363) (p 2459) (p 4171) (p 4443) (p 4604) (p 4625) (derived106443 p h) (derived78592 p h) (derived106293 p h) (h 26957) (derived87657 p h) (derived101349 p h)

theorem derived106455 (p : Nat → Prop) (h : Inputs p) :
    (p 4625) :=
  ElevenRUP.step106455 (p 2177) (p 2363) (p 2396) (p 2459) (p 3325) (p 4171) (p 4443) (p 4445) (p 4604) (p 4625) (derived106450 p h) (derived96473 p h) (derived106443 p h) (derived78592 p h) (derived106293 p h) (h 26957) (derived87657 p h) (derived96416 p h) (derived75377 p h) (h 37656)

theorem derived106456 (p : Nat → Prop) (h : Inputs p) :
    (p 4610) ∨ (p 2230) :=
  ElevenRUP.step106456 (p 2230) (p 2373) (p 2470) (p 4607) (p 4610) (derived98725 p h) (derived94353 p h) (derived99649 p h) (derived77542 p h)

theorem derived106457 (p : Nat → Prop) (h : Inputs p) :
    (p 4596) ∨ (¬ p 2386) :=
  ElevenRUP.step106457 (p 2352) (p 2383) (p 2386) (p 2484) (p 4113) (p 4596) (derived105370 p h) (h 23477) (derived78416 p h) (derived99503 p h) (derived91305 p h)

theorem derived106459 (p : Nat → Prop) (h : Inputs p) :
    (p 4596) ∨ (¬ p 3389) :=
  ElevenRUP.step106459 (p 2352) (p 2383) (p 2386) (p 2484) (p 2573) (p 2577) (p 3389) (p 4113) (p 4596) (p 4711) (derived106457 p h) (derived96935 p h) (derived102520 p h) (derived99503 p h) (derived105370 p h) (h 23477) (derived78416 p h) (derived105655 p h) (derived74768 p h)

theorem derived106461 (p : Nat → Prop) (h : Inputs p) :
    (p 4596) ∨ (¬ p 2230) :=
  ElevenRUP.step106461 (p 2230) (p 2352) (p 2383) (p 2386) (p 2484) (p 2573) (p 2577) (p 4113) (p 4596) (p 4715) (derived106457 p h) (derived96935 p h) (derived102520 p h) (derived99503 p h) (derived105423 p h) (derived105370 p h) (h 23477) (derived78416 p h) (derived87491 p h)

theorem derived106462 (p : Nat → Prop) (h : Inputs p) :
    (p 4563) ∨ (p 2156) :=
  ElevenRUP.step106462 (p 2156) (p 2284) (p 2946) (p 2957) (p 4563) (derived77962 p h) (derived101735 p h) (derived96894 p h) (h 6478)

theorem derived106463 (p : Nat → Prop) (h : Inputs p) :
    (p 4563) ∨ (p 2807) :=
  ElevenRUP.step106463 (p 2284) (p 2807) (p 2946) (p 4555) (p 4563) (derived101735 p h) (derived105542 p h) (derived77962 p h) (derived98897 p h)

theorem derived106465 (p : Nat → Prop) (h : Inputs p) :
    (p 4472) ∨ (¬ p 3425) :=
  ElevenRUP.step106465 (p 2122) (p 2774) (p 3425) (p 3426) (p 4472) (derived86295 p h) (derived97813 p h) (derived96484 p h) (h 4943)

theorem derived106467 (p : Nat → Prop) (h : Inputs p) :
    (p 4450) ∨ (¬ p 2156) :=
  ElevenRUP.step106467 (p 2088) (p 2156) (p 3146) (p 4450) (derived98723 p h) (derived46402 p h) (derived70399 p h)

theorem derived106468 (p : Nat → Prop) (h : Inputs p) :
    (p 4450) ∨ (¬ p 4115) :=
  ElevenRUP.step106468 (p 2088) (p 3146) (p 4115) (p 4450) (derived98723 p h) (derived46402 p h) (derived93723 p h)

theorem derived106469 (p : Nat → Prop) (h : Inputs p) :
    (p 4450) ∨ (¬ p 2166) :=
  ElevenRUP.step106469 (p 2166) (p 3146) (p 4450) (derived98723 p h) (derived48383 p h)

theorem derived106470 (p : Nat → Prop) (h : Inputs p) :
    (p 4450) ∨ (¬ p 2972) :=
  ElevenRUP.step106470 (p 2088) (p 2166) (p 2220) (p 2532) (p 2972) (p 3146) (p 4115) (p 4450) (p 4529) (derived98723 p h) (derived78872 p h) (derived46402 p h) (derived106468 p h) (derived102327 p h) (derived96462 p h) (derived106469 p h) (derived76101 p h)

theorem derived106471 (p : Nat → Prop) (h : Inputs p) :
    (p 4450) ∨ (¬ p 2373) :=
  ElevenRUP.step106471 (p 2088) (p 2220) (p 2373) (p 3146) (p 3697) (p 4115) (p 4450) (p 4533) (derived106468 p h) (derived102327 p h) (derived96460 p h) (derived105394 p h) (derived46402 p h) (derived98723 p h) (derived94644 p h)

theorem derived106472 (p : Nat → Prop) (h : Inputs p) :
    (p 4450) ∨ (¬ p 2982) :=
  ElevenRUP.step106472 (p 2088) (p 2220) (p 2373) (p 2532) (p 2982) (p 3146) (p 4115) (p 4450) (p 4529) (derived106468 p h) (derived102327 p h) (derived96462 p h) (derived98723 p h) (derived78872 p h) (derived46402 p h) (derived106471 p h) (derived78908 p h)

theorem derived106474 (p : Nat → Prop) (h : Inputs p) :
    (p 4448) ∨ (¬ p 2241) :=
  ElevenRUP.step106474 (p 2210) (p 2241) (p 2992) (p 4365) (p 4448) (derived47210 p h) (derived101298 p h) (derived96340 p h) (derived75456 p h)

theorem derived106481 (p : Nat → Prop) (h : Inputs p) :
    (p 4419) ∨ (¬ p 4236) :=
  ElevenRUP.step106481 (p 2598) (p 2663) (p 3362) (p 4236) (p 4419) (p 4786) (derived106425 p h) (h 25506) (derived77057 p h) (derived101922 p h) (h 34410)

theorem derived106483 (p : Nat → Prop) (h : Inputs p) :
    (p 4419) ∨ (p 2241) :=
  ElevenRUP.step106483 (p 2241) (p 2608) (p 2696) (p 3589) (p 3873) (p 4236) (p 4419) (p 5190) (derived106481 p h) (derived81800 p h) (derived105487 p h) (h 24353) (derived75624 p h) (h 6353) (derived102891 p h)

theorem derived106486 (p : Nat → Prop) (h : Inputs p) :
    (p 4419) ∨ (¬ p 2630) :=
  ElevenRUP.step106486 (p 2630) (p 2651) (p 2663) (p 2696) (p 3361) (p 4236) (p 4419) (p 4786) (derived106481 p h) (derived81800 p h) (derived101923 p h) (derived106425 p h) (h 25506) (derived78221 p h) (derived88480 p h)

theorem derived106487 (p : Nat → Prop) (h : Inputs p) :
    (p 4041) ∨ (¬ p 4437) :=
  ElevenRUP.step106487 (p 3256) (p 4041) (p 4437) (p 4438) (derived100965 p h) (derived106118 p h) (h 6889)

theorem derived106488 (p : Nat → Prop) (h : Inputs p) :
    (p 4041) ∨ (p 2459) :=
  ElevenRUP.step106488 (p 2264) (p 2459) (p 3256) (p 4041) (p 4548) (derived75418 p h) (derived95329 p h) (derived100965 p h) (derived75187 p h)

theorem derived106489 (p : Nat → Prop) (h : Inputs p) :
    (p 3950) ∨ (¬ p 3399) :=
  ElevenRUP.step106489 (p 2459) (p 3399) (p 3631) (p 3950) (p 4443) (derived100322 p h) (derived79496 p h) (derived87658 p h) (derived44451 p h)

theorem derived106490 (p : Nat → Prop) (h : Inputs p) :
    (p 3040) ∨ (¬ p 2298) :=
  ElevenRUP.step106490 (p 2298) (p 2996) (p 3032) (p 3040) (p 4427) (derived72292 p h) (derived75790 p h) (derived76408 p h) (h 38184)

theorem derived106491 (p : Nat → Prop) (h : Inputs p) :
    (p 3040) ∨ (¬ p 2641) :=
  ElevenRUP.step106491 (p 2295) (p 2298) (p 2641) (p 2996) (p 3040) (p 4156) (derived106490 p h) (derived98781 p h) (derived96453 p h) (derived75790 p h) (h 20048)

theorem derived106493 (p : Nat → Prop) (h : Inputs p) :
    (p 2954) ∨ (¬ p 4117) :=
  ElevenRUP.step106493 (p 2946) (p 2954) (p 4117) (derived101602 p h) (derived47702 p h)

theorem derived106494 (p : Nat → Prop) (h : Inputs p) :
    (p 2954) :=
  ElevenRUP.step106494 (p 2140) (p 2696) (p 2811) (p 2946) (p 2954) (p 3136) (p 4117) (p 5051) (derived105364 p h) (h 24693) (derived84267 p h) (derived101602 p h) (derived106493 p h) (derived84447 p h) (derived91165 p h) (h 30539)

theorem derived106495 (p : Nat → Prop) (h : Inputs p) :
    (p 2782) ∨ (¬ p 4356) :=
  ElevenRUP.step106495 (p 2782) (p 4356) (p 4401) (derived106316 p h) (h 6749)

theorem derived106498 (p : Nat → Prop) (h : Inputs p) :
    (p 2782) ∨ (¬ p 2122) :=
  ElevenRUP.step106498 (p 2122) (p 2307) (p 2774) (p 2782) (p 2785) (derived86487 p h) (derived102227 p h) (derived47816 p h) (derived90318 p h)

theorem derived106500 (p : Nat → Prop) (h : Inputs p) :
    (p 2782) ∨ (¬ p 2667) :=
  ElevenRUP.step106500 (p 2122) (p 2667) (p 2782) (p 4846) (derived106498 p h) (derived97818 p h) (h 27586)

theorem derived106501 (p : Nat → Prop) (h : Inputs p) :
    (p 2744) ∨ (p 2696) :=
  ElevenRUP.step106501 (p 2608) (p 2696) (p 2737) (p 2744) (p 3366) (derived80755 p h) (derived75627 p h) (derived87229 p h) (derived82531 p h)

theorem derived106503 (p : Nat → Prop) (h : Inputs p) :
    (p 2744) :=
  ElevenRUP.step106503 (p 2696) (p 2737) (p 2744) (p 2749) (derived80755 p h) (derived93452 p h) (derived106501 p h) (derived51598 p h)

theorem derived106504 (p : Nat → Prop) (h : Inputs p) :
    (p 2507) ∨ (¬ p 3402) :=
  ElevenRUP.step106504 (p 2493) (p 2507) (p 3402) (derived87263 p h) (derived87343 p h)

theorem derived106505 (p : Nat → Prop) (h : Inputs p) :
    (p 2507) ∨ (¬ p 3016) :=
  ElevenRUP.step106505 (p 2493) (p 2507) (p 2727) (p 3016) (p 3402) (p 3487) (derived106504 p h) (derived100198 p h) (derived95900 p h) (derived87263 p h) (derived87696 p h)

theorem derived106506 (p : Nat → Prop) (h : Inputs p) :
    (p 2501) ∨ (¬ p 3347) :=
  ElevenRUP.step106506 (p 2493) (p 2501) (p 3347) (derived99260 p h) (derived45688 p h)

theorem derived106509 (p : Nat → Prop) (h : Inputs p) :
    (p 2501) ∨ (p 3016) :=
  ElevenRUP.step106509 (p 2493) (p 2501) (p 2504) (p 3016) (p 3093) (p 3347) (p 3379) (p 4814) (derived106506 p h) (derived101933 p h) (derived80337 p h) (derived99260 p h) (derived96944 p h) (derived105440 p h) (derived87318 p h)

theorem derived106512 (p : Nat → Prop) (h : Inputs p) :
    (p 2501) ∨ (p 2573) :=
  ElevenRUP.step106512 (p 2493) (p 2501) (p 2504) (p 2573) (p 3093) (p 3347) (p 3379) (p 4108) (derived106506 p h) (derived101933 p h) (derived91521 p h) (derived80337 p h) (derived99260 p h) (derived96944 p h) (derived87306 p h)

theorem derived106513 (p : Nat → Prop) (h : Inputs p) :
    (p 2249) :=
  ElevenRUP.step106513 (p 2241) (p 2249) (p 2254) (derived75369 p h) (derived105366 p h) (h 21109)

theorem derived106519 (p : Nat → Prop) (h : Inputs p) :
    (p 5250) ∨ (¬ p 3990) :=
  ElevenRUP.step106519 (p 3461) (p 3990) (p 5250) (derived82520 p h) (derived48934 p h)

theorem derived106520 (p : Nat → Prop) (h : Inputs p) :
    (p 5250) ∨ (p 3266) :=
  ElevenRUP.step106520 (p 2363) (p 3266) (p 3461) (p 3990) (p 4171) (p 5250) (derived106519 p h) (derived90096 p h) (derived96436 p h) (derived82520 p h) (derived79610 p h)

theorem derived106521 (p : Nat → Prop) (h : Inputs p) :
    (p 4794) ∨ (¬ p 2608) :=
  ElevenRUP.step106521 (p 2254) (p 2608) (p 2707) (p 3576) (p 4794) (derived88249 p h) (derived101865 p h) (derived105366 p h) (derived42872 p h)

theorem derived106522 (p : Nat → Prop) (h : Inputs p) :
    (p 4771) ∨ (p 3166) :=
  ElevenRUP.step106522 (p 2668) (p 3166) (p 4771) (derived98530 p h) (derived101962 p h)

theorem derived106523 (p : Nat → Prop) (h : Inputs p) :
    (p 4771) ∨ (¬ p 2651) :=
  ElevenRUP.step106523 (p 2651) (p 2668) (p 4417) (p 4771) (derived98530 p h) (derived96398 p h) (derived49400 p h)

theorem derived106524 (p : Nat → Prop) (h : Inputs p) :
    (p 4771) ∨ (¬ p 3878) :=
  ElevenRUP.step106524 (p 2651) (p 3166) (p 3878) (p 4771) (derived106523 p h) (derived106522 p h) (derived85676 p h)

theorem derived106526 (p : Nat → Prop) (h : Inputs p) :
    (p 4598) ∨ (¬ p 2608) :=
  ElevenRUP.step106526 (p 2352) (p 2608) (p 3573) (p 4598) (derived80725 p h) (derived102496 p h) (derived48394 p h)

theorem derived106527 (p : Nat → Prop) (h : Inputs p) :
    (p 4592) ∨ (¬ p 4042) :=
  ElevenRUP.step106527 (p 2341) (p 3696) (p 3960) (p 4042) (p 4592) (p 4905) (derived105995 p h) (h 27003) (derived85375 p h) (derived89806 p h) (h 22442)

theorem derived106528 (p : Nat → Prop) (h : Inputs p) :
    (p 4592) ∨ (p 3051) :=
  ElevenRUP.step106528 (p 2220) (p 2881) (p 3051) (p 3696) (p 4042) (p 4119) (p 4592) (p 4905) (derived106527 p h) (derived81809 p h) (derived87258 p h) (derived105995 p h) (h 27003) (derived76417 p h) (h 29469)

theorem derived106529 (p : Nat → Prop) (h : Inputs p) :
    (p 4503) ∨ (¬ p 4032) :=
  ElevenRUP.step106529 (p 2177) (p 4032) (p 4138) (p 4503) (derived74610 p h) (derived87334 p h) (derived53038 p h)

theorem derived106530 (p : Nat → Prop) (h : Inputs p) :
    (p 4503) :=
  ElevenRUP.step106530 (p 2177) (p 3212) (p 4032) (p 4138) (p 4503) (p 5089) (p 5092) (derived74610 p h) (derived87334 p h) (derived106529 p h) (h 8571) (derived66432 p h) (h 8577) (derived49310 p h)

theorem derived106531 (p : Nat → Prop) (h : Inputs p) :
    (p 4445) ∨ (p 3951) :=
  ElevenRUP.step106531 (p 2459) (p 3951) (p 4443) (p 4445) (p 5059) (derived79494 p h) (derived87658 p h) (derived106367 p h) (h 33144)

theorem derived106532 (p : Nat → Prop) (h : Inputs p) :
    (p 3951) ∨ (¬ p 4443) :=
  ElevenRUP.step106532 (p 3246) (p 3951) (p 4382) (p 4443) (p 4669) (p 5059) (derived78109 p h) (derived93101 p h) (derived105415 p h) (h 27415) (h 33144)

theorem derived106533 (p : Nat → Prop) (h : Inputs p) :
    (p 3951) ∨ (¬ p 3949) :=
  ElevenRUP.step106533 (p 2459) (p 3949) (p 3950) (p 3951) (p 4443) (derived106532 p h) (derived87657 p h) (derived96419 p h) (h 5864)

theorem derived106534 (p : Nat → Prop) (h : Inputs p) :
    (p 3951) ∨ (¬ p 4132) :=
  ElevenRUP.step106534 (p 2459) (p 3146) (p 3657) (p 3949) (p 3951) (p 4132) (p 4443) (p 4445) (derived106533 p h) (derived93631 p h) (derived106531 p h) (derived106532 p h) (derived87657 p h) (derived96417 p h) (h 6906)

theorem derived106536 (p : Nat → Prop) (h : Inputs p) :
    (p 3951) :=
  ElevenRUP.step106536 (p 2881) (p 3146) (p 3246) (p 3747) (p 3949) (p 3951) (p 4132) (p 4445) (derived106534 p h) (derived95080 p h) (derived96359 p h) (derived106533 p h) (derived93631 p h) (derived78109 p h) (derived106531 p h) (derived78738 p h)

theorem derived106537 (p : Nat → Prop) (h : Inputs p) :
    (p 2664) :=
  ElevenRUP.step106537 (p 2651) (p 2664) (derived78222 p h) (derived105591 p h)

theorem derived106539 (p : Nat → Prop) (h : Inputs p) :
    (p 2139) ∨ (¬ p 4236) :=
  ElevenRUP.step106539 (p 2132) (p 2139) (p 2144) (p 2958) (p 4236) (p 4786) (derived106425 p h) (h 30062) (derived99784 p h) (derived96982 p h) (h 10616)

theorem derived106541 (p : Nat → Prop) (h : Inputs p) :
    (p 4514) ∨ (¬ p 2608) :=
  ElevenRUP.step106541 (p 2156) (p 2192) (p 2608) (p 3093) (p 4377) (p 4514) (derived105552 p h) (derived83583 p h) (derived46833 p h) (derived106170 p h) (derived97400 p h)

theorem derived106554 (p : Nat → Prop) (h : Inputs p) :
    (p 5053) ∨ (p 2829) :=
  ElevenRUP.step106554 (p 2829) (p 2850) (p 3367) (p 3698) (p 4702) (p 4715) (p 5053) (derived105618 p h) (derived105423 p h) (derived106079 p h) (h 27306) (derived99638 p h) (derived68719 p h)

theorem derived106555 (p : Nat → Prop) (h : Inputs p) :
    (p 5053) ∨ (¬ p 2440) :=
  ElevenRUP.step106555 (p 2440) (p 2630) (p 2850) (p 3698) (p 4343) (p 4702) (p 5053) (derived105617 p h) (derived91164 p h) (derived106079 p h) (h 27306) (derived99638 p h) (h 19857)

theorem derived106563 (p : Nat → Prop) (h : Inputs p) :
    (p 4450) ∨ (¬ p 3156) :=
  ElevenRUP.step106563 (p 2088) (p 2220) (p 2954) (p 3146) (p 3156) (p 3697) (p 4115) (p 4450) (derived98723 p h) (derived46402 p h) (derived106468 p h) (derived102327 p h) (derived96460 p h) (derived106494 p h) (derived94641 p h)

theorem derived106564 (p : Nat → Prop) (h : Inputs p) :
    (p 4450) ∨ (¬ p 3115) :=
  ElevenRUP.step106564 (p 2088) (p 2220) (p 2532) (p 3115) (p 3146) (p 3156) (p 4115) (p 4450) (p 4529) (derived106563 p h) (derived106468 p h) (derived102327 p h) (derived96462 p h) (derived98723 p h) (derived78872 p h) (derived46402 p h) (derived96686 p h)

theorem derived106565 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2528) ∨ (p 3256) ∨ (p 3146) ∨ (¬ p 4595) ∨ (¬ p 3016) ∨ (¬ p 2440) :=
  ElevenRUP.step106565 (p 2440) (p 2528) (p 3016) (p 3083) (p 3146) (p 3256) (p 3878) (p 4595) (derived101326 p h) (derived101024 p h) (derived93398 p h)

theorem derived106566 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2598) ∨ (p 2528) ∨ (p 3367) ∨ (¬ p 3422) ∨ (p 2274) ∨ (¬ p 2727) ∨ (¬ p 3389) ∨ (¬ p 2437) ∨ (¬ p 2440) :=
  ElevenRUP.step106566 (p 2132) (p 2274) (p 2437) (p 2440) (p 2528) (p 2598) (p 2727) (p 3367) (p 3389) (p 3422) (p 4646) (derived105534 p h) (derived77694 p h) (derived103906 p h)

theorem derived106567 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2132) ∨ (p 2598) ∨ (¬ p 4968) ∨ (¬ p 4744) ∨ (p 3367) ∨ (¬ p 4390) ∨ (¬ p 3475) ∨ (¬ p 3985) ∨ (¬ p 2651) ∨ (¬ p 2440) :=
  ElevenRUP.step106567 (p 2098) (p 2132) (p 2230) (p 2440) (p 2598) (p 2651) (p 2774) (p 2850) (p 3367) (p 3475) (p 3905) (p 3985) (p 4390) (p 4717) (p 4744) (p 4968) (derived105424 p h) (derived95981 p h) (derived81314 p h) (derived90698 p h) (derived104671 p h) (derived87965 p h) (derived87716 p h)

theorem derived106568 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (p 2307) ∨ (p 2383) ∨ (¬ p 2785) ∨ (p 2528) ∨ (¬ p 4272) ∨ (¬ p 5400) ∨ (¬ p 4322) ∨ (p 3146) ∨ (p 2829) ∨ (p 2881) ∨ (¬ p 2241) ∨ (¬ p 2210) ∨ (¬ p 2992) ∨ (¬ p 2891) ∨ (¬ p 5021) :=
  ElevenRUP.step106568 (p 2177) (p 2210) (p 2241) (p 2307) (p 2363) (p 2383) (p 2396) (p 2459) (p 2528) (p 2761) (p 2785) (p 2829) (p 2881) (p 2891) (p 2992) (p 3146) (p 3266) (p 3461) (p 3654) (p 3990) (p 4272) (p 4322) (p 4335) (p 4345) (p 4420) (p 4433) (p 4443) (p 4556) (p 5021) (p 5400) (derived106150 p h) (derived105399 p h) (derived105707 p h) (derived100454 p h) (derived90097 p h) (derived99552 p h) (derived41793 p h) (derived104093 p h) (derived100293 p h) (derived90929 p h) (derived87658 p h) (derived98852 p h) (derived99878 p h) (derived75902 p h) (derived100956 p h)

theorem derived106569 (p : Nat → Prop) (h : Inputs p) :
    (p 2396) ∨ (¬ p 2177) ∨ (p 2707) ∨ (¬ p 4471) ∨ (¬ p 2774) ∨ (p 2132) ∨ (p 2829) ∨ (p 2881) :=
  ElevenRUP.step106569 (p 2132) (p 2177) (p 2396) (p 2707) (p 2717) (p 2774) (p 2829) (p 2881) (p 3425) (p 4471) (derived88395 p h) (derived90124 p h) (derived89154 p h)

theorem derived106570 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (p 2132) ∨ (p 2598) ∨ (p 2528) ∨ (¬ p 4272) ∨ (¬ p 3923) ∨ (¬ p 3115) ∨ (p 3146) ∨ (p 2829) ∨ (¬ p 4429) ∨ (p 2417) ∨ (p 2553) ∨ (p 2881) ∨ (¬ p 2241) ∨ (¬ p 2210) ∨ (¬ p 2992) ∨ (¬ p 4117) ∨ (¬ p 4450) ∨ (¬ p 2891) ∨ (¬ p 3987) ∨ (¬ p 5021) ∨ (¬ p 3579) :=
  ElevenRUP.step106570 (p 2122) (p 2132) (p 2177) (p 2210) (p 2241) (p 2307) (p 2363) (p 2383) (p 2396) (p 2417) (p 2459) (p 2528) (p 2553) (p 2598) (p 2707) (p 2761) (p 2774) (p 2785) (p 2786) (p 2819) (p 2829) (p 2881) (p 2891) (p 2992) (p 3115) (p 3146) (p 3266) (p 3322) (p 3461) (p 3506) (p 3579) (p 3654) (p 3680) (p 3689) (p 3923) (p 3987) (p 4117) (p 4187) (p 4272) (p 4276) (p 4322) (p 4429) (p 4450) (p 4471) (p 5021) (p 5038) (p 5281) (p 5284) (p 5287) (p 5396) (p 5400) (p 5401) (derived105516 p h) (derived102578 p h) (derived42959 p h) (h 9314) (derived66468 p h) (h 9308) (derived54722 p h) (h 9008) (derived66456 p h) (h 9002) (h 9310) (h 11044) (derived102227 p h) (derived98937 p h) (derived90363 p h) (derived90582 p h) (derived101823 p h) (derived102189 p h) (derived90587 p h) (derived87984 p h) (derived106568 p h) (derived96437 p h) (derived98385 p h) (derived90463 p h) (h 34103) (derived99576 p h) (derived85900 p h) (derived106569 p h) (derived91160 p h) (derived41080 p h) (derived81906 p h)

theorem derived106571 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 3266) ∨ (p 2307) ∨ (¬ p 2779) ∨ (¬ p 4272) ∨ (¬ p 3115) ∨ (¬ p 4204) ∨ (p 2264) ∨ (p 2881) ∨ (¬ p 2241) ∨ (¬ p 4401) ∨ (¬ p 2992) ∨ (¬ p 4450) ∨ (¬ p 4333) ∨ (¬ p 5021) :=
  ElevenRUP.step106571 (p 2122) (p 2177) (p 2241) (p 2264) (p 2307) (p 2363) (p 2383) (p 2459) (p 2779) (p 2881) (p 2992) (p 3115) (p 3266) (p 3550) (p 3680) (p 4204) (p 4272) (p 4333) (p 4401) (p 4450) (p 4556) (p 5021) (p 5396) (p 5400) (p 5401) (derived105399 p h) (derived42959 p h) (h 9314) (derived66468 p h) (h 9310) (derived105107 p h) (derived85900 p h) (derived98385 p h) (derived96472 p h) (derived90300 p h) (derived97855 p h)

theorem derived106572 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 2779) ∨ (p 2528) ∨ (¬ p 4272) ∨ (¬ p 3115) ∨ (p 3146) ∨ (¬ p 4429) ∨ (¬ p 4204) ∨ (¬ p 3581) ∨ (p 2264) ∨ (p 2417) ∨ (p 2881) ∨ (¬ p 2241) ∨ (¬ p 4401) ∨ (¬ p 2210) ∨ (¬ p 2992) ∨ (¬ p 4450) ∨ (¬ p 2891) ∨ (¬ p 4333) ∨ (¬ p 5021) ∨ (¬ p 3579) :=
  ElevenRUP.step106572 (p 2177) (p 2210) (p 2241) (p 2264) (p 2307) (p 2396) (p 2417) (p 2459) (p 2528) (p 2586) (p 2761) (p 2779) (p 2881) (p 2891) (p 2992) (p 3115) (p 3146) (p 3266) (p 3461) (p 3506) (p 3579) (p 3581) (p 3654) (p 3680) (p 4187) (p 4204) (p 4272) (p 4276) (p 4322) (p 4333) (p 4401) (p 4420) (p 4429) (p 4443) (p 4450) (p 4556) (p 4623) (p 5021) (p 5038) (p 5281) (p 5284) (p 5287) (p 5396) (p 5401) (derived105372 p h) (derived105516 p h) (derived105399 p h) (derived105707 p h) (derived102578 p h) (derived42959 p h) (h 9314) (derived66468 p h) (h 9308) (derived54722 p h) (h 9008) (derived66456 p h) (h 9002) (derived91159 p h) (derived91160 p h) (derived78395 p h) (derived41080 p h) (derived90931 p h) (derived81906 p h) (derived99576 p h) (derived106571 p h) (derived87658 p h) (derived98852 p h) (derived75902 p h)

theorem derived106573 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 3961) ∨ (p 2396) ∨ (p 2088) ∨ (p 2098) ∨ (p 2774) ∨ (p 2528) ∨ (¬ p 4272) ∨ (¬ p 5400) ∨ (¬ p 4322) ∨ (¬ p 3156) ∨ (p 2274) ∨ (¬ p 2241) ∨ (¬ p 4401) ∨ (¬ p 2992) ∨ (¬ p 5021) :=
  ElevenRUP.step106573 (p 2088) (p 2098) (p 2241) (p 2274) (p 2307) (p 2318) (p 2363) (p 2396) (p 2459) (p 2528) (p 2761) (p 2774) (p 2819) (p 2992) (p 3146) (p 3156) (p 3266) (p 3609) (p 3945) (p 3961) (p 4272) (p 4322) (p 4335) (p 4401) (p 4420) (p 4736) (p 4861) (p 4902) (p 5021) (p 5400) (derived105456 p h) (derived105431 p h) (derived105707 p h) (derived42990 p h) (derived100454 p h) (derived92417 p h) (derived57865 p h) (derived97117 p h) (derived79580 p h) (derived100956 p h) (derived96966 p h) (derived104414 p h) (derived74883 p h) (derived86464 p h) (derived96379 p h)

theorem derived106574 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2797) ∨ (¬ p 3379) ∨ (p 2996) ∨ (¬ p 2641) ∨ (¬ p 2727) ∨ (¬ p 3819) ∨ (¬ p 4117) ∨ (¬ p 2505) ∨ (¬ p 2437) ∨ (¬ p 3987) ∨ (¬ p 2651) ∨ (¬ p 3579) ∨ (¬ p 2440) :=
  ElevenRUP.step106574 (p 2088) (p 2098) (p 2122) (p 2132) (p 2156) (p 2177) (p 2187) (p 2192) (p 2210) (p 2241) (p 2249) (p 2264) (p 2274) (p 2284) (p 2307) (p 2318) (p 2341) (p 2352) (p 2396) (p 2406) (p 2417) (p 2427) (p 2437) (p 2440) (p 2449) (p 2459) (p 2493) (p 2505) (p 2528) (p 2553) (p 2563) (p 2573) (p 2598) (p 2608) (p 2619) (p 2630) (p 2641) (p 2651) (p 2662) (p 2668) (p 2717) (p 2727) (p 2751) (p 2774) (p 2779) (p 2797) (p 2829) (p 2860) (p 2870) (p 2881) (p 2891) (p 2901) (p 2911) (p 2922) (p 2934) (p 2946) (p 2957) (p 2972) (p 2982) (p 2992) (p 2996) (p 3005) (p 3016) (p 3063) (p 3115) (p 3136) (p 3146) (p 3156) (p 3166) (p 3178) (p 3189) (p 3201) (p 3246) (p 3256) (p 3309) (p 3367) (p 3379) (p 3389) (p 3422) (p 3425) (p 3426) (p 3475) (p 3487) (p 3527) (p 3569) (p 3579) (p 3581) (p 3680) (p 3727) (p 3737) (p 3819) (p 3879) (p 3923) (p 3961) (p 3985) (p 3987) (p 4117) (p 4138) (p 4202) (p 4203) (p 4204) (p 4237) (p 4272) (p 4322) (p 4333) (p 4390) (p 4395) (p 4401) (p 4429) (p 4450) (p 4475) (p 4477) (p 4558) (p 4595) (p 4629) (p 4646) (p 4700) (p 4717) (p 4736) (p 4744) (p 4750) (p 4790) (p 4794) (p 4846) (p 4867) (p 4882) (p 4968) (p 4969) (p 4992) (p 4996) (p 5021) (p 5043) (p 5051) (p 5225) (p 5396) (p 5400) (p 5401) (p 5430) (p 5433) (p 5436) (p 5440) (p 5442) (p 5446) (p 5737) (p 5740) (p 5743) (derived106343 p h) (derived106424 p h) (derived106513 p h) (derived105453 p h) (derived105400 p h) (derived105471 p h) (derived105433 p h) (derived105534 p h) (derived105424 p h) (derived105495 p h) (derived105431 p h) (derived106410 p h) (derived96385 p h) (derived100363 p h) (derived100365 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived98028 p h) (derived83046 p h) (derived103271 p h) (derived103160 p h) (derived95900 p h) (derived87700 p h) (derived67577 p h) (derived83188 p h) (derived102210 p h) (derived102203 p h) (derived96899 p h) (derived69917 p h) (derived98069 p h) (derived98032 p h) (derived96894 p h) (h 6478) (derived106467 p h) (derived87285 p h) (derived96928 p h) (derived98048 p h) (derived106089 p h) (derived92723 p h) (derived98896 p h) (derived105806 p h) (derived43456 p h) (derived42946 p h) (derived51416 p h) (derived45857 p h) (derived103895 p h) (derived43149 p h) (derived92156 p h) (derived85991 p h) (derived76184 p h) (derived75640 p h) (derived44316 p h) (derived42933 p h) (derived102356 p h) (derived82061 p h) (derived102249 p h) (derived96403 p h) (derived98067 p h) (derived106521 p h) (h 9398) (derived100361 p h) (derived102487 p h) (derived74692 p h) (derived77109 p h) (derived88750 p h) (derived103131 p h) (derived103905 p h) (derived96314 p h) (derived66472 p h) (derived106296 p h) (derived96274 p h) (derived103753 p h) (derived43146 p h) (derived92090 p h) (derived43158 p h) (derived72733 p h) (h 9393) (derived100888 p h) (derived42990 p h) (derived84772 p h) (derived102256 p h) (derived76254 p h) (derived83510 p h) (derived85833 p h) (derived84347 p h) (derived85922 p h) (h 6810) (derived91915 p h) (derived102537 p h) (derived76483 p h) (h 8340) (h 9374) (derived95978 p h) (derived95979 p h) (derived96873 p h) (derived93024 p h) (derived66420 p h) (derived66471 p h) (derived42959 p h) (h 8334) (h 9380) (h 9314) (derived61311 p h) (derived66468 p h) (h 10652) (h 9308) (h 9310) (derived66500 p h) (h 10658) (derived106565 p h) (derived106566 p h) (derived106567 p h) (derived106570 p h) (derived96911 p h) (derived103015 p h) (derived100716 p h) (derived106572 p h) (derived97851 p h) (derived96483 p h) (derived96484 p h) (derived96486 p h) (derived90300 p h) (derived86400 p h) (derived87334 p h) (derived88646 p h) (derived91609 p h) (derived106573 p h) (derived85900 p h) (derived97024 p h) (derived96966 p h) (derived56969 p h) (derived89225 p h)

theorem derived106575 (p : Nat → Prop) (h : Inputs p) :
    (p 2774) ∨ (¬ p 3923) ∨ (p 2528) ∨ (¬ p 2972) ∨ (¬ p 4375) ∨ (p 2307) ∨ (¬ p 2166) ∨ (¬ p 4355) ∨ (¬ p 3016) ∨ (¬ p 4204) ∨ (p 3319) ∨ (¬ p 4397) ∨ (¬ p 3873) ∨ (p 2881) ∨ (p 2241) ∨ (¬ p 4426) ∨ (¬ p 2386) ∨ (¬ p 4401) ∨ (¬ p 3985) ∨ (¬ p 5020) ∨ (¬ p 3093) ∨ (¬ p 3379) ∨ (¬ p 3922) ∨ (¬ p 3487) ∨ (¬ p 4450) ∨ (¬ p 2891) ∨ (¬ p 4596) ∨ (¬ p 2437) ∨ (¬ p 2782) ∨ (¬ p 4782) :=
  ElevenRUP.step106575 (p 2122) (p 2132) (p 2166) (p 2177) (p 2210) (p 2241) (p 2307) (p 2363) (p 2383) (p 2386) (p 2437) (p 2459) (p 2518) (p 2528) (p 2608) (p 2630) (p 2668) (p 2707) (p 2717) (p 2737) (p 2742) (p 2744) (p 2751) (p 2774) (p 2778) (p 2782) (p 2819) (p 2829) (p 2850) (p 2881) (p 2891) (p 2922) (p 2972) (p 3016) (p 3083) (p 3093) (p 3146) (p 3319) (p 3366) (p 3379) (p 3425) (p 3426) (p 3483) (p 3487) (p 3589) (p 3609) (p 3641) (p 3683) (p 3685) (p 3873) (p 3917) (p 3922) (p 3923) (p 3953) (p 3985) (p 4204) (p 4355) (p 4375) (p 4397) (p 4401) (p 4426) (p 4433) (p 4450) (p 4556) (p 4596) (p 4646) (p 4717) (p 4782) (p 4902) (p 5020) (p 5263) (p 5268) (p 5375) (derived106343 p h) (derived105534 p h) (derived105399 p h) (derived105424 p h) (derived105456 p h) (derived106150 p h) (derived106503 p h) (derived93587 p h) (derived87700 p h) (derived67577 p h) (derived97434 p h) (derived93410 p h) (derived96402 p h) (derived96910 p h) (derived81314 p h) (derived86312 p h) (derived103602 p h) (derived96374 p h) (derived94907 p h) (derived87229 p h) (derived99814 p h) (derived80817 p h) (derived96922 p h) (derived104463 p h) (derived97344 p h) (derived96484 p h) (derived95449 p h) (derived90300 p h) (derived91261 p h) (derived88381 p h) (derived89191 p h) (h 8962) (derived87779 p h) (derived97921 p h) (derived88560 p h) (derived66454 p h) (derived96249 p h) (derived89801 p h) (derived98046 p h) (h 8968) (h 32848) (derived95427 p h) (derived105302 p h) (derived90332 p h)

theorem derived106576 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2459) ∨ (¬ p 2785) ∨ (¬ p 3923) ∨ (p 2528) ∨ (¬ p 2972) ∨ (p 3146) ∨ (p 2307) ∨ (p 3654) ∨ (¬ p 2531) ∨ (¬ p 3016) ∨ (p 3309) ∨ (p 2230) ∨ (¬ p 3873) ∨ (¬ p 3136) ∨ (p 2881) ∨ (p 2241) ∨ (¬ p 3093) ∨ (¬ p 2210) ∨ (¬ p 3379) ∨ (¬ p 4450) ∨ (¬ p 2891) ∨ (¬ p 2437) ∨ (¬ p 4845) ∨ (¬ p 4700) :=
  ElevenRUP.step106576 (p 2122) (p 2177) (p 2210) (p 2230) (p 2241) (p 2307) (p 2383) (p 2396) (p 2437) (p 2459) (p 2528) (p 2531) (p 2608) (p 2630) (p 2696) (p 2737) (p 2751) (p 2753) (p 2761) (p 2785) (p 2829) (p 2850) (p 2881) (p 2891) (p 2972) (p 3016) (p 3083) (p 3093) (p 3136) (p 3146) (p 3266) (p 3309) (p 3367) (p 3379) (p 3641) (p 3654) (p 3680) (p 3683) (p 3727) (p 3873) (p 3923) (p 3945) (p 3969) (p 4024) (p 4272) (p 4322) (p 4335) (p 4396) (p 4420) (p 4443) (p 4450) (p 4556) (p 4700) (p 4717) (p 4845) (p 4870) (p 4902) (p 5116) (p 5214) (p 5396) (p 5400) (p 5401) (p 5430) (p 5433) (p 5436) (p 5567) (p 5569) (p 5571) (p 5737) (p 5740) (p 5743) (derived106343 p h) (derived105456 p h) (derived105707 p h) (derived105399 p h) (derived105492 p h) (derived105424 p h) (derived90318 p h) (derived97432 p h) (h 9314) (derived66468 p h) (h 9310) (h 9308) (derived100454 p h) (derived93410 p h) (derived96402 p h) (derived87658 p h) (derived92417 p h) (derived98852 p h) (derived57865 p h) (derived98046 p h) (derived75902 p h) (derived79580 p h) (derived96295 p h) (derived97300 p h) (derived102221 p h) (derived98328 p h) (derived98915 p h) (derived98690 p h) (derived102285 p h) (derived102586 p h) (derived104463 p h) (h 9797) (derived96406 p h) (derived91808 p h) (derived75761 p h) (derived66485 p h) (derived82535 p h) (derived104124 p h) (h 9792) (derived100916 p h) (derived77326 p h) (h 10658) (h 9374) (derived66500 p h) (derived66471 p h) (h 10652) (h 9380) (derived61311 p h)

theorem derived106577 (p : Nat → Prop) (h : Inputs p) :
    (p 2177) ∨ (¬ p 4870) ∨ (p 2459) ∨ (p 2122) ∨ (¬ p 2972) ∨ (p 3146) ∨ (p 2307) ∨ (p 2881) ∨ (p 2241) ∨ (¬ p 3093) ∨ (¬ p 2210) ∨ (¬ p 4450) ∨ (¬ p 2891) :=
  ElevenRUP.step106577 (p 2122) (p 2177) (p 2210) (p 2241) (p 2307) (p 2383) (p 2459) (p 2608) (p 2881) (p 2891) (p 2972) (p 3093) (p 3146) (p 3204) (p 3955) (p 4450) (p 4556) (p 4870) (derived105399 p h) (derived101909 p h) (derived78596 p h) (derived97443 p h) (derived83957 p h) (derived104463 p h)

theorem derived106578 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (¬ p 4402) ∨ (¬ p 5357) ∨ (¬ p 5358) ∨ (p 2363) ∨ (p 2459) ∨ (p 2122) ∨ (¬ p 3115) ∨ (¬ p 2972) ∨ (p 3146) ∨ (p 2307) ∨ (p 3654) ∨ (¬ p 3156) ∨ (¬ p 2531) ∨ (¬ p 3016) ∨ (p 2230) ∨ (¬ p 3873) ∨ (¬ p 3136) ∨ (p 2881) ∨ (p 2911) ∨ (p 2241) ∨ (¬ p 3093) ∨ (¬ p 2210) ∨ (¬ p 3379) ∨ (¬ p 4450) ∨ (¬ p 2891) ∨ (¬ p 3389) ∨ (¬ p 2437) ∨ (¬ p 4845) ∨ (¬ p 4700) :=
  ElevenRUP.step106578 (p 2122) (p 2177) (p 2210) (p 2230) (p 2241) (p 2307) (p 2311) (p 2341) (p 2363) (p 2383) (p 2396) (p 2417) (p 2437) (p 2459) (p 2470) (p 2481) (p 2531) (p 2608) (p 2630) (p 2696) (p 2737) (p 2751) (p 2761) (p 2787) (p 2829) (p 2850) (p 2881) (p 2891) (p 2911) (p 2972) (p 3016) (p 3083) (p 3093) (p 3115) (p 3136) (p 3146) (p 3156) (p 3204) (p 3266) (p 3367) (p 3379) (p 3389) (p 3461) (p 3550) (p 3571) (p 3641) (p 3654) (p 3657) (p 3680) (p 3683) (p 3707) (p 3727) (p 3873) (p 3960) (p 3969) (p 4024) (p 4187) (p 4272) (p 4276) (p 4322) (p 4383) (p 4395) (p 4402) (p 4445) (p 4450) (p 4556) (p 4646) (p 4700) (p 4717) (p 4845) (p 4870) (p 5201) (p 5214) (p 5357) (p 5358) (p 5396) (p 5400) (p 5401) (p 5430) (p 5433) (p 5436) (p 5567) (p 5569) (p 5571) (p 5737) (p 5740) (p 5743) (derived106343 p h) (derived105534 p h) (derived105492 p h) (derived105399 p h) (derived105516 p h) (derived105374 p h) (derived105424 p h) (derived96416 p h) (h 37232) (derived96417 p h) (derived75803 p h) (derived97432 p h) (h 9314) (derived66468 p h) (h 9310) (h 9308) (derived101808 p h) (derived96279 p h) (derived91434 p h) (derived89806 p h) (derived93410 p h) (derived96402 p h) (derived85674 p h) (derived101909 p h) (derived102333 p h) (derived102285 p h) (derived102586 p h) (derived106577 p h) (derived96472 p h) (derived74722 p h) (derived83994 p h) (derived96954 p h) (derived104463 p h) (derived76924 p h) (derived91808 p h) (derived75761 p h) (derived100937 p h) (derived97300 p h) (derived82535 p h) (derived104124 p h) (derived91160 p h) (derived49355 p h) (derived43242 p h) (derived90002 p h) (h 9797) (derived81906 p h) (derived66485 p h) (derived84325 p h) (h 9792) (derived100693 p h) (derived77326 p h) (h 10658) (h 9374) (derived66500 p h) (derived66471 p h) (h 10652) (h 9380) (derived61311 p h)

theorem derived106579 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2797) ∨ (¬ p 3379) ∨ (p 2996) ∨ (¬ p 2727) ∨ (¬ p 3819) ∨ (¬ p 4117) ∨ (¬ p 2505) ∨ (¬ p 2504) ∨ (¬ p 2437) ∨ (¬ p 2584) ∨ (¬ p 3019) ∨ (¬ p 2651) ∨ (¬ p 3579) ∨ (¬ p 2440) ∨ (¬ p 4782) :=
  ElevenRUP.step106579 (p 2122) (p 2156) (p 2166) (p 2192) (p 2210) (p 2230) (p 2241) (p 2245) (p 2249) (p 2264) (p 2274) (p 2284) (p 2307) (p 2331) (p 2341) (p 2352) (p 2363) (p 2373) (p 2386) (p 2406) (p 2427) (p 2437) (p 2440) (p 2459) (p 2493) (p 2504) (p 2505) (p 2528) (p 2531) (p 2553) (p 2563) (p 2573) (p 2584) (p 2608) (p 2641) (p 2651) (p 2662) (p 2667) (p 2727) (p 2744) (p 2751) (p 2774) (p 2782) (p 2785) (p 2797) (p 2829) (p 2860) (p 2870) (p 2881) (p 2891) (p 2901) (p 2911) (p 2922) (p 2934) (p 2946) (p 2957) (p 2972) (p 2982) (p 2992) (p 2996) (p 3016) (p 3019) (p 3037) (p 3051) (p 3063) (p 3093) (p 3115) (p 3125) (p 3136) (p 3146) (p 3156) (p 3189) (p 3201) (p 3204) (p 3246) (p 3256) (p 3309) (p 3319) (p 3347) (p 3379) (p 3389) (p 3399) (p 3422) (p 3449) (p 3487) (p 3527) (p 3546) (p 3564) (p 3569) (p 3579) (p 3589) (p 3631) (p 3654) (p 3657) (p 3819) (p 3873) (p 3879) (p 3922) (p 3923) (p 3953) (p 3985) (p 3987) (p 4079) (p 4117) (p 4202) (p 4204) (p 4282) (p 4283) (p 4288) (p 4355) (p 4375) (p 4397) (p 4401) (p 4402) (p 4426) (p 4431) (p 4450) (p 4496) (p 4558) (p 4595) (p 4596) (p 4629) (p 4646) (p 4700) (p 4717) (p 4718) (p 4782) (p 4790) (p 4813) (p 4845) (p 4882) (p 4901) (p 4992) (p 4996) (p 5008) (p 5020) (p 5062) (p 5201) (p 5357) (p 5358) (derived105469 p h) (derived106424 p h) (derived106513 p h) (derived105453 p h) (derived105400 p h) (derived106343 p h) (derived105425 p h) (derived105534 p h) (derived105424 p h) (derived106503 p h) (derived80352 p h) (derived101909 p h) (h 33521) (derived100363 p h) (derived100365 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived98028 p h) (derived83046 p h) (derived103271 p h) (derived103160 p h) (derived95900 p h) (derived87700 p h) (derived67577 p h) (derived83188 p h) (derived102210 p h) (derived102203 p h) (derived96899 p h) (h 6549) (derived102388 p h) (derived87993 p h) (h 11708) (derived101933 p h) (derived96881 p h) (derived87197 p h) (derived96021 p h) (derived98069 p h) (derived96339 p h) (derived69917 p h) (derived95901 p h) (derived98032 p h) (derived96894 p h) (h 6478) (derived106467 p h) (derived96928 p h) (derived98048 p h) (derived106089 p h) (derived92723 p h) (derived97247 p h) (derived92844 p h) (derived102419 p h) (derived106459 p h) (derived96279 p h) (derived87202 p h) (derived96448 p h) (derived106500 p h) (derived96449 p h) (derived106415 p h) (h 31515) (derived96383 p h) (derived106574 p h) (derived96976 p h) (derived88695 p h) (derived88836 p h) (derived91067 p h) (derived84116 p h) (derived93411 p h) (derived80879 p h) (derived97454 p h) (h 27689) (derived102591 p h) (derived80951 p h) (derived102256 p h) (derived87286 p h) (derived88806 p h) (derived93844 p h) (derived102435 p h) (derived84192 p h) (derived100361 p h) (derived102837 p h) (derived85301 p h) (derived96306 p h) (derived95848 p h) (derived106296 p h) (derived77058 p h) (derived83934 p h) (derived88742 p h) (derived79142 p h) (derived101940 p h) (derived76059 p h) (derived83047 p h) (derived74806 p h) (derived99114 p h) (derived91434 p h) (derived78525 p h) (derived105054 p h) (derived96275 p h) (derived85753 p h) (derived102268 p h) (derived97434 p h) (derived76483 p h) (derived83510 p h) (derived80538 p h) (derived94097 p h) (derived93024 p h) (h 8340) (derived106565 p h) (derived66420 p h) (h 8334) (derived106575 p h) (derived102227 p h) (derived90318 p h) (derived106576 p h) (derived96417 p h) (derived105107 p h) (derived89302 p h) (derived93552 p h) (derived90058 p h) (derived102129 p h) (derived100360 p h) (derived106578 p h) (derived96374 p h) (derived90472 p h) (derived93634 p h) (derived99814 p h)

theorem derived106581 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (p 2122) ∨ (p 2668) ∨ (p 2829) ∨ (p 2459) ∨ (¬ p 3873) ∨ (p 2210) ∨ (p 2241) ∨ (¬ p 5085) ∨ (¬ p 4117) ∨ (¬ p 4846) ∨ (¬ p 2807) ∨ (¬ p 4783) :=
  ElevenRUP.step106581 (p 2098) (p 2122) (p 2177) (p 2210) (p 2241) (p 2264) (p 2341) (p 2459) (p 2608) (p 2668) (p 2707) (p 2717) (p 2744) (p 2774) (p 2807) (p 2829) (p 3399) (p 3425) (p 3527) (p 3589) (p 3689) (p 3819) (p 3820) (p 3873) (p 4104) (p 4117) (p 4377) (p 4783) (p 4793) (p 4794) (p 4800) (p 4807) (p 4846) (p 5085) (derived106503 p h) (derived106170 p h) (derived105438 p h) (derived101823 p h) (derived87984 p h) (derived96391 p h) (derived93816 p h) (h 11042) (derived99814 p h) (derived90472 p h) (derived88268 p h) (derived103015 p h) (derived97847 p h) (derived96165 p h) (derived89839 p h) (derived97920 p h) (derived77955 p h) (derived100709 p h) (derived89912 p h) (derived85105 p h) (derived89229 p h) (derived76883 p h)

theorem derived106582 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2668) ∨ (¬ p 3923) ∨ (p 2829) ∨ (p 2363) ∨ (p 2459) ∨ (¬ p 3873) ∨ (p 2210) ∨ (p 2241) ∨ (¬ p 5085) ∨ (¬ p 4117) ∨ (¬ p 4846) ∨ (¬ p 2807) ∨ (¬ p 4783) :=
  ElevenRUP.step106582 (p 2122) (p 2210) (p 2241) (p 2363) (p 2459) (p 2608) (p 2668) (p 2807) (p 2819) (p 2829) (p 3093) (p 3873) (p 3923) (p 3953) (p 4117) (p 4783) (p 4846) (p 5085) (derived96374 p h) (derived106581 p h) (derived93634 p h) (derived90518 p h) (derived97843 p h)

theorem derived106583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3923) ∨ (p 2696) ∨ (p 2829) ∨ (¬ p 4022) ∨ (¬ p 2982) ∨ (¬ p 3016) ∨ (¬ p 3573) ∨ (p 2274) ∨ (p 2553) ∨ (p 2307) ∨ (¬ p 4397) ∨ (¬ p 2481) ∨ (¬ p 4332) ∨ (¬ p 4440) ∨ (p 2459) ∨ (¬ p 4401) ∨ (p 2881) ∨ (¬ p 2230) ∨ (p 2241) ∨ (p 3379) ∨ (¬ p 5085) ∨ (¬ p 3922) ∨ (¬ p 4117) ∨ (¬ p 4846) ∨ (¬ p 2782) ∨ (¬ p 2663) ∨ (¬ p 2440) ∨ (¬ p 2807) ∨ (¬ p 4783) :=
  ElevenRUP.step106583 (p 2122) (p 2177) (p 2210) (p 2230) (p 2241) (p 2245) (p 2274) (p 2307) (p 2363) (p 2383) (p 2440) (p 2459) (p 2481) (p 2553) (p 2608) (p 2663) (p 2668) (p 2696) (p 2707) (p 2717) (p 2774) (p 2778) (p 2782) (p 2807) (p 2819) (p 2829) (p 2881) (p 2982) (p 3016) (p 3083) (p 3266) (p 3276) (p 3343) (p 3366) (p 3379) (p 3425) (p 3426) (p 3461) (p 3483) (p 3519) (p 3573) (p 3680) (p 3873) (p 3917) (p 3922) (p 3923) (p 3941) (p 3979) (p 4022) (p 4108) (p 4117) (p 4138) (p 4149) (p 4170) (p 4204) (p 4322) (p 4332) (p 4376) (p 4397) (p 4401) (p 4440) (p 4449) (p 4475) (p 4556) (p 4783) (p 4786) (p 4814) (p 4846) (p 5085) (p 5122) (p 5123) (p 5225) (p 5263) (p 5268) (p 5396) (p 5401) (p 5555) (p 5558) (p 5561) (p 5577) (p 5580) (p 5583) (derived105440 p h) (derived105399 p h) (derived105483 p h) (derived105495 p h) (derived106425 p h) (derived106320 p h) (derived95997 p h) (derived100361 p h) (derived104093 p h) (derived91521 p h) (h 22317) (h 27689) (derived103179 p h) (derived91518 p h) (derived93587 p h) (derived79782 p h) (derived93717 p h) (derived106582 p h) (derived96483 p h) (derived96484 p h) (derived90300 p h) (derived82907 p h) (derived90586 p h) (derived86400 p h) (derived89191 p h) (derived87334 p h) (derived98338 p h) (derived96910 p h) (derived88258 p h) (derived90335 p h) (derived102130 p h) (derived87229 p h) (derived76927 p h) (derived95434 p h) (derived101328 p h) (derived90258 p h) (derived86269 p h) (h 8968) (h 9814) (derived66454 p h) (derived66486 p h) (h 8962) (h 9808) (derived98406 p h) (derived84909 p h) (derived79531 p h) (h 9727) (derived98400 p h) (derived66484 p h) (h 9308) (h 9721) (derived66468 p h) (derived97077 p h) (h 9314)

theorem derived106584 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 3923) ∨ (p 2696) ∨ (p 2829) ∨ (p 2274) ∨ (p 2553) ∨ (p 2307) ∨ (p 2459) ∨ (¬ p 4401) ∨ (p 2881) ∨ (p 2241) ∨ (¬ p 2782) :=
  ElevenRUP.step106584 (p 2122) (p 2177) (p 2241) (p 2274) (p 2307) (p 2459) (p 2553) (p 2608) (p 2696) (p 2707) (p 2717) (p 2744) (p 2774) (p 2778) (p 2782) (p 2829) (p 2881) (p 3309) (p 3366) (p 3399) (p 3426) (p 3547) (p 3923) (p 3955) (p 4204) (p 4401) (p 4424) (p 4475) (derived106503 p h) (derived100361 p h) (derived96483 p h) (derived96484 p h) (derived90300 p h) (derived82907 p h) (derived90586 p h) (derived89191 p h) (derived78596 p h) (derived96910 p h) (derived96390 p h) (derived88258 p h) (derived93488 p h) (derived98513 p h) (derived87229 p h) (derived91720 p h) (derived96286 p h)

theorem derived106585 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 4022) ∨ (¬ p 2982) ∨ (¬ p 3016) ∨ (¬ p 3573) ∨ (p 2274) ∨ (p 2553) ∨ (p 2307) ∨ (¬ p 4397) ∨ (¬ p 2481) ∨ (¬ p 4332) ∨ (¬ p 4440) ∨ (p 2459) ∨ (¬ p 4401) ∨ (p 2881) ∨ (¬ p 2230) ∨ (p 2241) ∨ (p 3379) ∨ (¬ p 5085) ∨ (¬ p 3922) ∨ (¬ p 4117) ∨ (¬ p 2797) ∨ (¬ p 2782) ∨ (¬ p 2663) ∨ (¬ p 2440) ∨ (¬ p 2807) ∨ (¬ p 4783) :=
  ElevenRUP.step106585 (p 2122) (p 2177) (p 2230) (p 2241) (p 2274) (p 2307) (p 2440) (p 2459) (p 2481) (p 2553) (p 2663) (p 2696) (p 2737) (p 2782) (p 2797) (p 2807) (p 2829) (p 2881) (p 2982) (p 3016) (p 3063) (p 3309) (p 3379) (p 3550) (p 3573) (p 3918) (p 3922) (p 3923) (p 3955) (p 4022) (p 4117) (p 4332) (p 4397) (p 4401) (p 4426) (p 4440) (p 4556) (p 4783) (p 4846) (p 4992) (p 4996) (p 5085) (derived105399 p h) (derived96385 p h) (derived96383 p h) (derived96376 p h) (derived94907 p h) (derived103792 p h) (derived106583 p h) (h 8334) (derived66420 p h) (h 8340) (derived106584 p h) (h 6880) (derived83445 p h) (derived83502 p h) (derived78596 p h) (derived96472 p h)

theorem derived106586 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 3063) ∨ (¬ p 2507) ∨ (¬ p 3581) ∨ (p 2911) ∨ (p 2881) :=
  ElevenRUP.step106586 (p 2177) (p 2507) (p 2881) (p 2911) (p 3063) (p 3309) (p 3550) (p 3581) (p 4556) (derived105399 p h) (derived96472 p h) (derived85174 p h) (derived83502 p h)

theorem derived106587 (p : Nat → Prop) (h : Inputs p) :
    (p 3923) ∨ (¬ p 2829) ∨ (¬ p 3115) ∨ (¬ p 3156) ∨ (¬ p 2507) ∨ (¬ p 3016) ∨ (p 2295) ∨ (p 2553) ∨ (p 2307) ∨ (p 2459) ∨ (¬ p 3136) ∨ (p 2911) ∨ (p 2881) ∨ (¬ p 2230) ∨ (p 2241) ∨ (¬ p 4450) ∨ (¬ p 4203) ∨ (¬ p 4845) ∨ (¬ p 2663) ∨ (¬ p 2440) :=
  ElevenRUP.step106587 (p 2122) (p 2177) (p 2187) (p 2230) (p 2241) (p 2295) (p 2307) (p 2363) (p 2440) (p 2459) (p 2507) (p 2553) (p 2663) (p 2696) (p 2737) (p 2774) (p 2785) (p 2811) (p 2829) (p 2881) (p 2911) (p 3016) (p 3063) (p 3093) (p 3115) (p 3136) (p 3156) (p 3309) (p 3449) (p 3581) (p 3923) (p 3955) (p 4203) (p 4450) (p 4518) (p 4556) (p 4733) (p 4845) (p 4869) (p 4902) (p 4992) (p 4996) (p 5015) (derived105456 p h) (derived105399 p h) (derived105430 p h) (derived106113 p h) (derived102297 p h) (derived102249 p h) (derived104093 p h) (h 8334) (derived66420 p h) (h 8340) (derived106586 p h) (derived78596 p h) (derived98281 p h) (derived98513 p h) (derived85303 p h) (derived95391 p h) (derived104446 p h) (derived104886 p h) (derived91165 p h) (derived47426 p h) (derived81245 p h) (derived85196 p h) (derived97847 p h) (derived102227 p h)

theorem derived106588 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 3923) ∨ (p 2307) ∨ (p 2363) ∨ (p 2241) :=
  ElevenRUP.step106588 (p 2241) (p 2307) (p 2363) (p 3093) (p 3309) (p 3923) (p 5015) (derived85239 p h) (derived85303 p h) (derived95391 p h)

theorem derived106589 (p : Nat → Prop) (h : Inputs p) :
    (p 2737) ∨ (¬ p 3093) ∨ (¬ p 2829) ∨ (p 2241) ∨ (¬ p 4845) :=
  ElevenRUP.step106589 (p 2241) (p 2608) (p 2737) (p 2742) (p 2829) (p 3093) (p 4024) (p 4845) (derived102285 p h) (derived96922 p h) (derived91808 p h) (derived97365 p h)

theorem derived106590 (p : Nat → Prop) (h : Inputs p) :
    (p 2177) ∨ (p 3309) ∨ (¬ p 2829) ∨ (¬ p 3115) ∨ (p 2459) ∨ (¬ p 3136) ∨ (¬ p 3873) ∨ (p 2241) ∨ (¬ p 4450) ∨ (¬ p 2284) ∨ (¬ p 4845) :=
  ElevenRUP.step106590 (p 2177) (p 2241) (p 2284) (p 2459) (p 2608) (p 2696) (p 2737) (p 2753) (p 2829) (p 3093) (p 3115) (p 3136) (p 3309) (p 3873) (p 4450) (p 4845) (p 4870) (derived102586 p h) (derived101202 p h) (derived106589 p h) (derived44740 p h) (derived96029 p h) (derived96406 p h) (derived84292 p h)

theorem derived106591 (p : Nat → Prop) (h : Inputs p) :
    (p 3399) ∨ (p 2717) ∨ (p 2850) ∨ (¬ p 3362) ∨ (¬ p 3449) ∨ (¬ p 4797) ∨ (¬ p 2177) ∨ (¬ p 2230) ∨ (¬ p 3201) :=
  ElevenRUP.step106591 (p 2177) (p 2230) (p 2717) (p 2850) (p 3201) (p 3362) (p 3399) (p 3449) (p 3527) (p 4276) (p 4733) (p 4797) (p 5307) (derived105430 p h) (derived105516 p h) (derived76357 p h) (derived97093 p h) (derived96266 p h)

theorem derived106592 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (p 3073) ∨ (¬ p 3641) ∨ (¬ p 2177) ∨ (p 2383) ∨ (¬ p 2829) ∨ (¬ p 3115) ∨ (¬ p 3156) ∨ (¬ p 2531) ∨ (¬ p 3016) ∨ (¬ p 5260) ∨ (p 2363) ∨ (¬ p 4395) ∨ (¬ p 4402) ∨ (p 2449) ∨ (p 2911) ∨ (p 2417) ∨ (p 2881) ∨ (¬ p 2230) ∨ (¬ p 3873) ∨ (p 2241) ∨ (p 3379) ∨ (¬ p 3201) ∨ (¬ p 2727) ∨ (¬ p 4450) ∨ (¬ p 2284) ∨ (¬ p 3571) ∨ (¬ p 4845) ∨ (¬ p 2440) ∨ (¬ p 4781) :=
  ElevenRUP.step106592 (p 2177) (p 2230) (p 2241) (p 2284) (p 2341) (p 2363) (p 2383) (p 2396) (p 2406) (p 2417) (p 2440) (p 2449) (p 2531) (p 2598) (p 2608) (p 2696) (p 2707) (p 2717) (p 2727) (p 2737) (p 2751) (p 2753) (p 2761) (p 2787) (p 2829) (p 2850) (p 2881) (p 2911) (p 3016) (p 3073) (p 3093) (p 3115) (p 3136) (p 3156) (p 3201) (p 3266) (p 3322) (p 3362) (p 3379) (p 3399) (p 3449) (p 3461) (p 3519) (p 3527) (p 3545) (p 3571) (p 3631) (p 3641) (p 3654) (p 3680) (p 3707) (p 3727) (p 3873) (p 3969) (p 4187) (p 4272) (p 4276) (p 4322) (p 4395) (p 4402) (p 4450) (p 4556) (p 4700) (p 4717) (p 4781) (p 4796) (p 4797) (p 4845) (p 4870) (p 5260) (p 5357) (p 5358) (p 5396) (p 5400) (p 5401) (p 5430) (p 5433) (p 5436) (p 5567) (p 5569) (p 5571) (p 5737) (p 5740) (p 5743) (derived106343 p h) (derived105424 p h) (derived105374 p h) (derived105439 p h) (derived105516 p h) (derived105399 p h) (derived96437 p h) (h 34103) (derived102586 p h) (derived91518 p h) (derived76848 p h) (derived104436 p h) (derived100363 p h) (derived106589 p h) (derived88253 p h) (derived44740 p h) (derived96029 p h) (derived55956 p h) (derived102685 p h) (derived96406 p h) (derived80989 p h) (derived43242 p h) (derived80553 p h) (h 9314) (derived101922 p h) (derived45993 p h) (h 9797) (derived66468 p h) (derived89208 p h) (derived66485 p h) (h 9308) (h 9310) (h 9792) (derived77326 p h) (h 9374) (derived66471 p h) (h 9380) (derived61311 p h) (h 10652) (derived66500 p h) (h 10658) (derived100693 p h) (derived84325 p h) (derived106591 p h) (derived102507 p h) (derived85075 p h) (derived89354 p h) (derived96058 p h) (derived90058 p h) (derived102129 p h) (derived100927 p h) (derived91160 p h) (derived49355 p h) (derived81906 p h) (derived90002 p h)

theorem derived106593 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (p 2459) ∨ (p 2911) ∨ (¬ p 2230) ∨ (p 2241) ∨ (p 3379) ∨ (¬ p 2727) ∨ (¬ p 4117) ∨ (¬ p 3571) ∨ (¬ p 2946) ∨ (¬ p 3580) ∨ (¬ p 2437) ∨ (¬ p 2797) ∨ (¬ p 2667) ∨ (¬ p 3019) ∨ (¬ p 2663) ∨ (¬ p 2440) ∨ (¬ p 2807) ∨ (¬ p 2685) :=
  ElevenRUP.step106593 (p 2156) (p 2177) (p 2230) (p 2241) (p 2245) (p 2248) (p 2249) (p 2264) (p 2274) (p 2284) (p 2295) (p 2307) (p 2311) (p 2363) (p 2373) (p 2383) (p 2386) (p 2396) (p 2406) (p 2417) (p 2427) (p 2437) (p 2440) (p 2449) (p 2459) (p 2470) (p 2481) (p 2493) (p 2507) (p 2528) (p 2531) (p 2553) (p 2563) (p 2573) (p 2630) (p 2641) (p 2663) (p 2667) (p 2685) (p 2727) (p 2751) (p 2782) (p 2787) (p 2797) (p 2807) (p 2829) (p 2860) (p 2870) (p 2881) (p 2901) (p 2911) (p 2946) (p 2957) (p 2982) (p 3016) (p 3019) (p 3063) (p 3073) (p 3083) (p 3093) (p 3115) (p 3125) (p 3136) (p 3156) (p 3201) (p 3246) (p 3266) (p 3276) (p 3309) (p 3319) (p 3322) (p 3325) (p 3343) (p 3355) (p 3379) (p 3438) (p 3461) (p 3519) (p 3564) (p 3569) (p 3571) (p 3573) (p 3580) (p 3581) (p 3641) (p 3680) (p 3683) (p 3873) (p 3879) (p 3919) (p 3922) (p 3923) (p 3941) (p 3979) (p 3986) (p 4009) (p 4022) (p 4108) (p 4117) (p 4121) (p 4149) (p 4171) (p 4186) (p 4203) (p 4276) (p 4322) (p 4332) (p 4383) (p 4395) (p 4397) (p 4401) (p 4402) (p 4440) (p 4449) (p 4450) (p 4556) (p 4558) (p 4610) (p 4636) (p 4646) (p 4700) (p 4717) (p 4781) (p 4783) (p 4790) (p 4845) (p 4882) (p 4992) (p 4993) (p 4996) (p 5043) (p 5085) (p 5122) (p 5123) (p 5190) (p 5203) (p 5260) (p 5396) (p 5401) (p 5555) (p 5558) (p 5561) (p 5577) (p 5580) (p 5583) (p 5597) (p 5600) (p 5603) (derived106343 p h) (derived106513 p h) (derived106424 p h) (derived105453 p h) (derived105399 p h) (derived105400 p h) (derived105534 p h) (derived105424 p h) (derived105374 p h) (derived105471 p h) (derived105490 p h) (derived105516 p h) (derived105483 p h) (derived105487 p h) (derived105365 p h) (derived96894 p h) (derived100363 p h) (derived100365 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived98028 p h) (derived83046 p h) (h 6478) (derived106467 p h) (derived50095 p h) (derived104093 p h) (derived96436 p h) (h 6924) (derived85674 p h) (derived74499 p h) (derived87461 p h) (derived96954 p h) (derived96437 p h) (derived102583 p h) (derived102553 p h) (derived61403 p h) (h 34724) (derived102356 p h) (derived100360 p h) (derived103160 p h) (derived91518 p h) (derived76848 p h) (derived83200 p h) (derived102210 p h) (derived91169 p h) (derived86542 p h) (derived102587 p h) (derived103124 p h) (derived96402 p h) (derived104436 p h) (derived104425 p h) (derived96935 p h) (derived91521 p h) (h 22317) (h 27689) (derived69917 p h) (derived96303 p h) (derived87197 p h) (derived96021 p h) (derived98807 p h) (derived87285 p h) (derived106500 p h) (derived106415 p h) (derived96397 p h) (derived96395 p h) (derived101808 p h) (derived91303 p h) (derived79301 p h) (h 25649) (h 21376) (derived102249 p h) (derived91057 p h) (derived103484 p h) (h 32074) (derived103131 p h) (derived96946 p h) (derived78936 p h) (derived92090 p h) (derived79502 p h) (derived101940 p h) (derived102135 p h) (derived79039 p h) (derived95997 p h) (derived93048 p h) (derived90153 p h) (h 6922) (derived106585 p h) (derived106587 p h) (derived79782 p h) (derived91284 p h) (derived106588 p h) (derived106590 p h) (derived96473 p h) (derived104494 p h) (derived106586 p h) (derived102136 p h) (derived97300 p h) (h 8340) (derived66420 p h) (h 8333) (derived80247 p h) (derived102672 p h) (derived106196 p h) (derived106592 p h) (derived80449 p h) (derived80466 p h) (derived82485 p h) (derived76206 p h) (derived96034 p h) (derived101328 p h) (derived79531 p h) (derived102429 p h) (derived89963 p h) (derived75856 p h) (h 9870) (h 9308) (derived66488 p h) (derived66468 p h) (h 9864) (h 9314) (derived71834 p h) (derived98922 p h) (h 9727) (h 9808) (derived66484 p h) (derived66486 p h) (h 9721) (h 9814) (derived99426 p h)

theorem derived106594 (p : Nat → Prop) (h : Inputs p) :
    (p 3309) ∨ (¬ p 2307) ∨ (¬ p 2518) ∨ (p 2363) ∨ (p 2911) ∨ (¬ p 4598) ∨ (p 3379) :=
  ElevenRUP.step106594 (p 2177) (p 2307) (p 2363) (p 2383) (p 2518) (p 2553) (p 2586) (p 2911) (p 3309) (p 3379) (p 3581) (p 3923) (p 3955) (p 4598) (derived105372 p h) (derived104858 p h) (derived78372 p h) (derived102249 p h) (derived79782 p h) (derived78298 p h) (derived98513 p h) (derived78596 p h)

theorem derived106595 (p : Nat → Prop) (h : Inputs p) :
    (p 2553) ∨ (p 2177) ∨ (¬ p 3309) ∨ (¬ p 2307) ∨ (p 2459) ∨ (¬ p 3136) ∨ (¬ p 2573) ∨ (¬ p 2230) ∨ (p 3379) ∨ (¬ p 2786) ∨ (¬ p 4450) ∨ (¬ p 3051) ∨ (¬ p 2437) ∨ (¬ p 2584) ∨ (¬ p 3019) ∨ (¬ p 2663) ∨ (¬ p 2440) :=
  ElevenRUP.step106595 (p 2122) (p 2177) (p 2230) (p 2274) (p 2295) (p 2307) (p 2318) (p 2319) (p 2341) (p 2406) (p 2427) (p 2437) (p 2440) (p 2459) (p 2493) (p 2507) (p 2553) (p 2563) (p 2573) (p 2584) (p 2586) (p 2608) (p 2663) (p 2665) (p 2696) (p 2707) (p 2717) (p 2737) (p 2786) (p 2811) (p 2829) (p 2860) (p 2870) (p 2901) (p 2982) (p 3016) (p 3019) (p 3051) (p 3093) (p 3115) (p 3136) (p 3309) (p 3379) (p 3399) (p 3426) (p 3519) (p 3527) (p 3543) (p 3569) (p 3879) (p 4203) (p 4401) (p 4450) (p 4452) (p 4475) (p 4518) (p 4558) (p 4700) (p 4733) (p 4845) (p 4882) (p 5043) (p 5225) (derived105453 p h) (derived105400 p h) (derived105373 p h) (derived105372 p h) (derived105471 p h) (derived106113 p h) (derived105430 p h) (derived105495 p h) (derived96287 p h) (derived96969 p h) (derived96966 p h) (derived100365 p h) (derived100363 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived98028 p h) (derived103160 p h) (derived91518 p h) (derived76848 p h) (derived83200 p h) (derived102210 p h) (derived87285 p h) (derived106415 p h) (derived74846 p h) (derived76826 p h) (derived79304 p h) (derived78503 p h) (derived85355 p h) (derived78539 p h) (derived96946 p h) (derived92090 p h) (derived103290 p h) (derived78583 p h) (derived93048 p h) (derived95924 p h) (derived76302 p h) (derived100682 p h) (derived91165 p h) (derived82711 p h) (derived47426 p h) (derived96483 p h) (derived96484 p h) (derived81245 p h) (derived90586 p h) (derived95699 p h) (derived88258 p h)

theorem derived106596 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 3434) ∨ (p 3425) ∨ (¬ p 3125) ∨ (p 2241) ∨ (¬ p 2284) ∨ (¬ p 2946) :=
  ElevenRUP.step106596 (p 2241) (p 2248) (p 2284) (p 2608) (p 2707) (p 2744) (p 2946) (p 3125) (p 3425) (p 3434) (p 3589) (p 4621) (derived105407 p h) (derived105365 p h) (derived106503 p h) (derived75702 p h) (derived88381 p h) (derived99814 p h)

theorem derived106597 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (p 2839) ∨ (p 2132) ∨ (¬ p 3582) ∨ (p 2737) ∨ (¬ p 3125) ∨ (p 2459) ∨ (¬ p 2230) ∨ (¬ p 3873) ∨ (p 2241) ∨ (¬ p 5086) ∨ (¬ p 2284) ∨ (¬ p 4897) ∨ (¬ p 2946) ∨ (¬ p 3879) ∨ (¬ p 4782) :=
  ElevenRUP.step106597 (p 2132) (p 2230) (p 2241) (p 2284) (p 2459) (p 2608) (p 2707) (p 2717) (p 2737) (p 2839) (p 2946) (p 3125) (p 3399) (p 3425) (p 3434) (p 3527) (p 3576) (p 3582) (p 3657) (p 3687) (p 3873) (p 3879) (p 4330) (p 4782) (p 4786) (p 4897) (p 5086) (p 5190) (derived106425 p h) (derived105487 p h) (derived106329 p h) (derived96417 p h) (derived84090 p h) (derived89590 p h) (derived106596 p h) (derived101865 p h) (derived101905 p h) (derived81620 p h) (derived88089 p h) (derived97057 p h) (derived87496 p h)

theorem derived106598 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 3547) ∨ (p 2459) ∨ (¬ p 3136) ∨ (p 2911) ∨ (¬ p 4210) ∨ (¬ p 2406) ∨ (¬ p 2230) ∨ (¬ p 3873) ∨ (p 2241) ∨ (¬ p 5087) ∨ (¬ p 5086) ∨ (¬ p 3819) ∨ (¬ p 4431) ∨ (¬ p 2946) ∨ (¬ p 3580) ∨ (¬ p 2437) ∨ (¬ p 4419) ∨ (¬ p 2440) ∨ (¬ p 2685) :=
  ElevenRUP.step106598 (p 2098) (p 2122) (p 2132) (p 2156) (p 2230) (p 2241) (p 2248) (p 2264) (p 2274) (p 2284) (p 2341) (p 2406) (p 2427) (p 2437) (p 2440) (p 2459) (p 2553) (p 2563) (p 2573) (p 2608) (p 2685) (p 2696) (p 2707) (p 2717) (p 2737) (p 2811) (p 2839) (p 2850) (p 2860) (p 2870) (p 2881) (p 2901) (p 2911) (p 2946) (p 2957) (p 3016) (p 3125) (p 3136) (p 3399) (p 3425) (p 3527) (p 3537) (p 3547) (p 3564) (p 3569) (p 3580) (p 3582) (p 3609) (p 3819) (p 3820) (p 3873) (p 3879) (p 4210) (p 4330) (p 4377) (p 4419) (p 4431) (p 4477) (p 4558) (p 4620) (p 4646) (p 4700) (p 4710) (p 4711) (p 4752) (p 4753) (p 4782) (p 4783) (p 4794) (p 4804) (p 4805) (p 4882) (p 4897) (p 4898) (p 5086) (p 5087) (p 5190) (p 5206) (derived105534 p h) (derived105453 p h) (derived105400 p h) (derived105655 p h) (derived105514 p h) (derived105434 p h) (derived105455 p h) (derived105487 p h) (derived106329 p h) (derived105365 p h) (derived106170 p h) (derived100365 p h) (derived100363 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived98028 p h) (derived103160 p h) (derived83200 p h) (derived50095 p h) (derived96894 p h) (derived83046 p h) (h 6478) (derived104425 p h) (derived101919 p h) (derived106271 p h) (derived96397 p h) (derived96396 p h) (derived94484 p h) (derived46048 p h) (derived92584 p h) (derived83917 p h) (derived93186 p h) (derived97910 p h) (derived43222 p h) (derived74807 p h) (derived96486 p h) (derived91165 p h) (derived81200 p h) (h 26522) (derived43237 p h) (derived96367 p h) (derived82744 p h) (derived81242 p h) (derived106597 p h) (derived77952 p h) (derived77953 p h) (derived89154 p h) (derived93166 p h) (derived96165 p h) (derived89912 p h) (derived89227 p h) (derived89229 p h) (derived75049 p h) (derived89791 p h) (derived95923 p h) (derived89158 p h) (derived97206 p h) (derived91526 p h)

theorem derived106599 (p : Nat → Prop) (h : Inputs p) :
    (p 2459) ∨ (p 2911) ∨ (¬ p 2230) ∨ (p 2241) ∨ (p 3379) ∨ (¬ p 2727) ∨ (¬ p 2786) ∨ (¬ p 4117) ∨ (¬ p 3571) ∨ (¬ p 4431) ∨ (¬ p 2946) ∨ (¬ p 3580) ∨ (¬ p 2437) ∨ (¬ p 2797) ∨ (¬ p 2584) ∨ (¬ p 2667) ∨ (¬ p 3019) ∨ (¬ p 2663) ∨ (¬ p 2440) ∨ (¬ p 2807) ∨ (¬ p 2685) :=
  ElevenRUP.step106599 (p 2156) (p 2177) (p 2210) (p 2230) (p 2241) (p 2245) (p 2249) (p 2284) (p 2307) (p 2363) (p 2406) (p 2427) (p 2437) (p 2440) (p 2459) (p 2470) (p 2518) (p 2528) (p 2553) (p 2563) (p 2573) (p 2584) (p 2586) (p 2663) (p 2667) (p 2685) (p 2727) (p 2751) (p 2786) (p 2797) (p 2807) (p 2881) (p 2901) (p 2911) (p 2946) (p 2957) (p 3019) (p 3051) (p 3136) (p 3201) (p 3309) (p 3370) (p 3379) (p 3519) (p 3547) (p 3569) (p 3571) (p 3580) (p 3581) (p 3819) (p 3873) (p 3879) (p 4031) (p 4104) (p 4108) (p 4117) (p 4210) (p 4383) (p 4419) (p 4431) (p 4450) (p 4556) (p 4558) (p 4598) (p 4646) (p 4700) (p 4786) (p 4790) (p 4814) (p 5086) (p 5087) (derived106425 p h) (derived106343 p h) (derived106424 p h) (derived106513 p h) (derived105440 p h) (derived105400 p h) (derived105534 p h) (derived105399 p h) (derived105372 p h) (derived85674 p h) (derived91518 p h) (derived76848 p h) (derived104436 p h) (derived96894 p h) (derived100363 p h) (derived100365 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived98028 p h) (derived83046 p h) (h 6478) (derived104425 p h) (derived47457 p h) (derived103179 p h) (derived96465 p h) (derived96016 p h) (h 11474) (derived50095 p h) (derived91521 p h) (h 22317) (h 27689) (derived69917 p h) (derived96305 p h) (derived96304 p h) (derived93816 p h) (h 11042) (derived106467 p h) (derived92844 p h) (h 25506) (derived74499 p h) (derived104093 p h) (derived87461 p h) (h 26933) (derived106593 p h) (derived106594 p h) (derived96286 p h) (derived106598 p h) (derived102249 p h) (derived106595 p h) (derived78298 p h)

theorem derived106601 (p : Nat → Prop) (h : Inputs p) :
    (p 2122) ∨ (p 2598) ∨ (p 2737) ∨ (p 2608) ∨ (¬ p 3146) ∨ (¬ p 2373) ∨ (p 2396) ∨ (¬ p 3309) ∨ (¬ p 2230) ∨ (¬ p 2786) ∨ (¬ p 4845) ∨ (¬ p 4419) :=
  ElevenRUP.step106601 (p 2122) (p 2230) (p 2307) (p 2373) (p 2396) (p 2598) (p 2608) (p 2737) (p 2774) (p 2785) (p 2786) (p 2829) (p 3146) (p 3309) (p 4419) (p 4669) (p 4845) (p 4869) (p 5224) (derived105494 p h) (derived105415 p h) (derived81067 p h) (derived86382 p h) (derived90589 p h) (derived102227 p h) (derived102297 p h) (derived85196 p h)

theorem derived106602 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3146) ∨ (¬ p 3960) ∨ (p 3399) ∨ (¬ p 2373) ∨ (p 2274) ∨ (¬ p 3309) ∨ (¬ p 4401) ∨ (¬ p 3136) ∨ (¬ p 4210) ∨ (¬ p 2230) ∨ (¬ p 2246) ∨ (¬ p 5087) ∨ (¬ p 2786) ∨ (¬ p 2946) ∨ (¬ p 2437) ∨ (¬ p 4845) ∨ (¬ p 2663) ∨ (¬ p 2440) :=
  ElevenRUP.step106602 (p 2122) (p 2132) (p 2137) (p 2220) (p 2230) (p 2246) (p 2274) (p 2284) (p 2373) (p 2396) (p 2417) (p 2427) (p 2437) (p 2440) (p 2470) (p 2481) (p 2531) (p 2563) (p 2598) (p 2608) (p 2663) (p 2696) (p 2707) (p 2717) (p 2737) (p 2744) (p 2786) (p 2829) (p 2839) (p 2850) (p 2901) (p 2946) (p 3083) (p 3136) (p 3146) (p 3156) (p 3246) (p 3309) (p 3399) (p 3434) (p 3569) (p 3631) (p 3879) (p 3960) (p 4031) (p 4204) (p 4210) (p 4401) (p 4419) (p 4434) (p 4452) (p 4475) (p 4518) (p 4558) (p 4646) (p 4669) (p 4700) (p 4752) (p 4753) (p 4786) (p 4845) (p 5087) (p 5190) (derived106425 p h) (derived106113 p h) (derived105400 p h) (derived105534 p h) (derived106144 p h) (derived106503 p h) (derived105514 p h) (derived105434 p h) (derived105415 p h) (derived105487 p h) (derived87445 p h) (derived96954 p h) (derived96016 p h) (h 23730) (derived100363 p h) (derived100365 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived98028 p h) (derived83046 p h) (derived79039 p h) (derived101940 p h) (derived96287 p h) (derived61403 p h) (h 34724) (derived100361 p h) (derived75882 p h) (derived89328 p h) (h 25506) (derived76401 p h) (derived44912 p h) (derived58637 p h) (derived44910 p h) (derived95968 p h) (derived82744 p h) (derived81200 p h) (derived89554 p h) (derived102427 p h) (derived82874 p h) (derived88389 p h) (derived83844 p h) (derived106601 p h) (derived96483 p h) (derived90353 p h) (derived90586 p h)

theorem derived106603 (p : Nat → Prop) (h : Inputs p) :
    (p 2707) ∨ (p 2608) ∨ (p 3146) ∨ (¬ p 2481) ∨ (¬ p 2531) ∨ (¬ p 2459) ∨ (¬ p 4969) ∨ (¬ p 3166) ∨ (¬ p 2230) ∨ (¬ p 4117) ∨ (¬ p 2437) ∨ (¬ p 2440) :=
  ElevenRUP.step106603 (p 2088) (p 2098) (p 2230) (p 2248) (p 2427) (p 2437) (p 2440) (p 2459) (p 2481) (p 2531) (p 2608) (p 2707) (p 2717) (p 2753) (p 2881) (p 2901) (p 3083) (p 3146) (p 3166) (p 3178) (p 3256) (p 3569) (p 3685) (p 3879) (p 4117) (p 4119) (p 4700) (p 4898) (p 4902) (p 4969) (p 5190) (derived105455 p h) (derived105365 p h) (derived105487 p h) (derived105456 p h) (derived96406 p h) (derived100365 p h) (derived100363 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived50095 p h) (derived87258 p h) (derived89212 p h) (derived97921 p h) (derived96873 p h) (derived88444 p h) (derived88289 p h) (derived88423 p h) (derived76915 p h) (derived100716 p h)

theorem derived106604 (p : Nat → Prop) (h : Inputs p) :
    (p 2829) ∨ (¬ p 2707) ∨ (p 2608) ∨ (p 2274) ∨ (¬ p 3309) ∨ (¬ p 4401) :=
  ElevenRUP.step106604 (p 2122) (p 2274) (p 2608) (p 2707) (p 2829) (p 3309) (p 4401) (p 4475) (derived90589 p h) (derived90586 p h) (derived96483 p h)

theorem derived106605 (p : Nat → Prop) (h : Inputs p) :
    (p 2737) ∨ (¬ p 4390) ∨ (p 2598) ∨ (¬ p 2850) ∨ (¬ p 2829) ∨ (p 3125) ∨ (p 2274) ∨ (¬ p 3309) ∨ (¬ p 3873) ∨ (¬ p 2786) ∨ (¬ p 2563) ∨ (¬ p 4328) ∨ (¬ p 4845) ∨ (¬ p 2440) :=
  ElevenRUP.step106605 (p 2122) (p 2274) (p 2295) (p 2307) (p 2440) (p 2563) (p 2598) (p 2737) (p 2774) (p 2785) (p 2786) (p 2829) (p 2839) (p 2850) (p 3125) (p 3309) (p 3319) (p 3367) (p 3564) (p 3695) (p 3873) (p 4328) (p 4390) (p 4753) (p 4845) (p 4869) (p 5224) (derived105514 p h) (derived105494 p h) (derived96366 p h) (derived102297 p h) (derived87804 p h) (derived83821 p h) (derived87157 p h) (derived81245 p h) (derived87955 p h) (derived81067 p h) (derived103137 p h) (derived85196 p h) (derived86479 p h) (derived102227 p h)

theorem derived106606 (p : Nat → Prop) (h : Inputs p) :
    (p 2696) ∨ (¬ p 2829) ∨ (p 3125) ∨ (p 2274) ∨ (¬ p 3309) ∨ (¬ p 2573) ∨ (¬ p 2230) ∨ (¬ p 3873) ∨ (¬ p 2786) ∨ (¬ p 2505) ∨ (¬ p 2563) ∨ (¬ p 4328) ∨ (¬ p 2331) ∨ (¬ p 4845) ∨ (¬ p 2663) ∨ (¬ p 2440) :=
  ElevenRUP.step106606 (p 2230) (p 2274) (p 2295) (p 2307) (p 2331) (p 2386) (p 2440) (p 2505) (p 2563) (p 2573) (p 2598) (p 2663) (p 2696) (p 2737) (p 2786) (p 2811) (p 2829) (p 2850) (p 3016) (p 3125) (p 3309) (p 3422) (p 3873) (p 4328) (p 4390) (p 4752) (p 4814) (p 4845) (derived105434 p h) (derived105440 p h) (derived96935 p h) (derived91165 p h) (derived81200 p h) (derived82874 p h) (derived87796 p h) (derived96274 p h) (derived106605 p h) (derived47426 p h) (derived81874 p h) (derived85328 p h) (derived104611 p h)

theorem derived106607 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 3073) ∨ (¬ p 3961) ∨ (¬ p 2459) ∨ (¬ p 3955) ∨ (p 2553) ∨ (¬ p 2839) ∨ (p 3146) ∨ (¬ p 2132) ∨ (¬ p 2696) ∨ (¬ p 2507) ∨ (¬ p 2619) ∨ (¬ p 3988) ∨ (p 3093) ∨ (p 2274) ∨ (¬ p 2284) ∨ (¬ p 2563) ∨ (p 2210) ∨ (¬ p 2651) ∨ (¬ p 2230) :=
  ElevenRUP.step106607 (p 2088) (p 2132) (p 2210) (p 2230) (p 2274) (p 2284) (p 2307) (p 2318) (p 2363) (p 2459) (p 2507) (p 2553) (p 2563) (p 2619) (p 2651) (p 2663) (p 2696) (p 2839) (p 3073) (p 3093) (p 3146) (p 3923) (p 3955) (p 3961) (p 3988) (p 4317) (p 4433) (p 4489) (p 4814) (p 4902) (p 5971) (p 5972) (derived105390 p h) (derived105440 p h) (derived106150 p h) (derived105456 p h) (derived96927 p h) (derived96966 p h) (derived102871 p h) (derived98463 p h) (derived104414 p h) (h 12824) (derived80464 p h) (derived66564 p h) (h 12818)

theorem derived106608 (p : Nat → Prop) (h : Inputs p) :
    (p 2274) ∨ (¬ p 2437) ∨ (¬ p 2829) ∨ (p 2608) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106608 (p 2132) (p 2156) (p 2166) (p 2177) (p 2187) (p 2192) (p 2210) (p 2230) (p 2241) (p 2255) (p 2264) (p 2274) (p 2284) (p 2295) (p 2307) (p 2331) (p 2341) (p 2363) (p 2373) (p 2406) (p 2417) (p 2427) (p 2437) (p 2440) (p 2459) (p 2493) (p 2505) (p 2507) (p 2528) (p 2553) (p 2563) (p 2573) (p 2584) (p 2608) (p 2619) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2667) (p 2685) (p 2696) (p 2727) (p 2753) (p 2786) (p 2797) (p 2807) (p 2829) (p 2839) (p 2870) (p 2881) (p 2891) (p 2901) (p 2911) (p 2946) (p 2982) (p 2992) (p 2995) (p 3005) (p 3016) (p 3019) (p 3073) (p 3093) (p 3115) (p 3125) (p 3136) (p 3146) (p 3156) (p 3166) (p 3256) (p 3309) (p 3379) (p 3449) (p 3569) (p 3571) (p 3580) (p 3581) (p 3873) (p 3879) (p 3919) (p 3948) (p 3955) (p 3961) (p 3987) (p 3988) (p 4031) (p 4117) (p 4119) (p 4186) (p 4203) (p 4204) (p 4210) (p 4276) (p 4282) (p 4313) (p 4328) (p 4338) (p 4431) (p 4450) (p 4518) (p 4556) (p 4558) (p 4595) (p 4596) (p 4646) (p 4700) (p 4733) (p 4790) (p 4814) (p 4845) (p 4882) (p 4902) (p 4972) (p 5008) (p 5015) (p 5043) (p 5203) (derived105453 p h) (derived106424 p h) (derived105469 p h) (derived105534 p h) (derived105367 p h) (derived105373 p h) (derived105400 p h) (derived105516 p h) (derived105440 p h) (derived105471 p h) (derived105490 p h) (derived105430 p h) (derived105399 p h) (derived105456 p h) (derived106113 p h) (derived96016 p h) (derived100365 p h) (derived100363 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived98023 p h) (derived104425 p h) (derived96934 p h) (h 5209) (derived87995 p h) (derived50095 p h) (derived82395 p h) (derived91169 p h) (derived100245 p h) (derived82296 p h) (derived96339 p h) (derived98028 p h) (derived79993 p h) (derived102260 p h) (derived106467 p h) (derived87258 p h) (derived83046 p h) (derived87285 p h) (derived105882 p h) (derived96927 p h) (derived101098 p h) (derived103475 p h) (derived104436 p h) (derived84343 p h) (derived96382 p h) (h 36523) (derived102333 p h) (derived97247 p h) (derived101769 p h) (derived84349 p h) (derived85984 p h) (derived103124 p h) (derived102335 p h) (derived83857 p h) (h 6564) (derived61403 p h) (derived103160 p h) (derived106305 p h) (derived96315 p h) (derived91068 p h) (derived104473 p h) (derived96428 p h) (derived79705 p h) (derived96429 p h) (derived96406 p h) (derived96408 p h) (derived96449 p h) (h 11044) (derived96448 p h) (derived106414 p h) (derived102873 p h) (derived106461 p h) (derived100361 p h) (derived103484 p h) (derived76001 p h) (derived85301 p h) (h 35121) (derived91680 p h) (derived95391 p h) (derived79039 p h) (derived84680 p h) (derived90965 p h) (derived96943 p h) (derived96946 p h) (derived106606 p h) (derived84293 p h) (derived44910 p h) (derived87172 p h) (derived94042 p h) (derived84322 p h) (derived92141 p h) (derived102429 p h) (derived103846 p h) (derived102249 p h) (derived103131 p h) (derived85174 p h) (derived101604 p h) (derived92090 p h) (derived106565 p h) (derived78596 p h) (derived106599 p h) (derived93048 p h) (derived101666 p h) (derived78588 p h) (derived91609 p h) (derived104446 p h) (derived80634 p h) (derived106607 p h) (derived104886 p h) (derived103898 p h)

theorem derived106609 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 2829) ∨ (p 2608) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106609 (p 2230) (p 2255) (p 2274) (p 2284) (p 2406) (p 2427) (p 2437) (p 2440) (p 2563) (p 2608) (p 2696) (p 2727) (p 2737) (p 2829) (p 2850) (p 2901) (p 3016) (p 3136) (p 3309) (p 3367) (p 3569) (p 3879) (p 4117) (p 4203) (p 4558) (p 4646) (p 4700) (p 4752) (p 4753) (derived105367 p h) (derived105400 p h) (derived105534 p h) (derived105514 p h) (derived105434 p h) (derived100245 p h) (derived103475 p h) (derived104436 p h) (derived100365 p h) (derived100363 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived98028 p h) (derived87285 p h) (derived83046 p h) (derived106608 p h) (derived53072 p h) (derived43222 p h) (derived102848 p h) (derived81200 p h) (derived87804 p h) (derived103102 p h)

theorem derived106610 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2563) ∨ (¬ p 3759) ∨ (¬ p 2274) ∨ (¬ p 2829) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106610 (p 2230) (p 2274) (p 2440) (p 2563) (p 2829) (p 3016) (p 3367) (p 3759) (p 4203) (p 4753) (derived105514 p h) (derived87285 p h) (derived45753 p h) (derived53072 p h) (derived102848 p h)

theorem derived106611 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2901) ∨ (¬ p 2187) ∨ (p 2363) ∨ (p 2132) ∨ (¬ p 4243) ∨ (¬ p 3367) ∨ (p 2563) ∨ (¬ p 3759) ∨ (¬ p 2797) ∨ (¬ p 2811) ∨ (¬ p 4140) ∨ (p 2437) ∨ (¬ p 2406) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106611 (p 2132) (p 2156) (p 2187) (p 2192) (p 2230) (p 2255) (p 2284) (p 2331) (p 2352) (p 2363) (p 2383) (p 2406) (p 2427) (p 2437) (p 2440) (p 2459) (p 2470) (p 2493) (p 2509) (p 2510) (p 2528) (p 2563) (p 2573) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2685) (p 2707) (p 2727) (p 2737) (p 2751) (p 2797) (p 2807) (p 2811) (p 2870) (p 2881) (p 2891) (p 2901) (p 2911) (p 2946) (p 2992) (p 3016) (p 3073) (p 3096) (p 3125) (p 3322) (p 3323) (p 3367) (p 3425) (p 3527) (p 3544) (p 3576) (p 3759) (p 3879) (p 3948) (p 3958) (p 4031) (p 4133) (p 4140) (p 4153) (p 4186) (p 4194) (p 4198) (p 4243) (p 4282) (p 4330) (p 4344) (p 4399) (p 4431) (p 4558) (p 4620) (p 4650) (p 4683) (p 4686) (p 4688) (p 4781) (p 4814) (p 4972) (p 4976) (derived105367 p h) (derived105378 p h) (derived106343 p h) (derived105373 p h) (derived105400 p h) (derived105465 p h) (derived106329 p h) (derived105712 p h) (derived105440 p h) (derived96437 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived96078 p h) (derived95141 p h) (derived81850 p h) (derived96395 p h) (derived77876 p h) (derived88253 p h) (derived101865 p h) (derived96017 p h) (derived75064 p h) (derived96481 p h) (derived100365 p h) (derived83077 p h) (derived95238 p h) (derived101272 p h) (derived96025 p h) (derived96429 p h) (derived98962 p h) (derived96409 p h) (derived105882 p h) (derived101098 p h) (derived106276 p h) (derived100245 p h) (derived82296 p h) (derived96339 p h) (derived102873 p h) (derived96016 p h) (h 30182) (derived68388 p h) (h 36523) (derived87413 p h) (derived80089 p h) (derived46185 p h) (derived90987 p h) (derived95235 p h) (derived88197 p h) (derived97247 p h) (derived97962 p h) (derived104100 p h) (derived66699 p h) (derived75065 p h) (derived92946 p h) (derived79937 p h) (derived91169 p h) (derived96441 p h) (derived71205 p h) (derived88577 p h) (derived102269 p h) (derived74786 p h) (h 7550) (derived88107 p h) (derived77853 p h) (derived66365 p h) (derived80174 p h) (h 7555)

theorem derived106612 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (p 3527) ∨ (p 2717) ∨ (¬ p 2295) ∨ (¬ p 3425) ∨ (p 2363) ∨ (¬ p 3576) ∨ (¬ p 2737) ∨ (¬ p 2811) ∨ (¬ p 2331) :=
  ElevenRUP.step106612 (p 2177) (p 2295) (p 2331) (p 2363) (p 2396) (p 2459) (p 2717) (p 2737) (p 2811) (p 2881) (p 3246) (p 3323) (p 3425) (p 3527) (p 3576) (p 3955) (p 4330) (p 4396) (p 4559) (derived106329 p h) (derived105701 p h) (derived45486 p h) (derived102221 p h) (derived48835 p h) (derived78596 p h) (derived98517 p h) (derived97068 p h) (derived88577 p h) (derived79319 p h)

theorem derived106613 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2870) ∨ (¬ p 3425) ∨ (p 2427) ∨ (p 2363) ∨ (p 2132) ∨ (¬ p 2737) ∨ (¬ p 4781) ∨ (p 2696) ∨ (¬ p 3819) ∨ (¬ p 2331) ∨ (¬ p 2440) :=
  ElevenRUP.step106613 (p 2132) (p 2177) (p 2295) (p 2331) (p 2341) (p 2363) (p 2427) (p 2440) (p 2459) (p 2668) (p 2696) (p 2707) (p 2717) (p 2737) (p 2811) (p 2870) (p 2881) (p 3425) (p 3527) (p 3576) (p 3687) (p 3819) (p 3820) (p 4133) (p 4781) (derived105712 p h) (derived96165 p h) (derived88253 p h) (derived101905 p h) (derived101865 p h) (derived91165 p h) (derived48835 p h) (derived89677 p h) (derived94446 p h) (derived88685 p h) (derived106612 p h) (derived74491 p h) (derived86734 p h) (derived79363 p h)

theorem derived106614 (p : Nat → Prop) (h : Inputs p) :
    (p 2696) ∨ (¬ p 2274) ∨ (¬ p 2829) ∨ (p 2608) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106614 (p 2122) (p 2132) (p 2136) (p 2156) (p 2187) (p 2210) (p 2230) (p 2274) (p 2295) (p 2307) (p 2331) (p 2363) (p 2406) (p 2427) (p 2437) (p 2440) (p 2553) (p 2563) (p 2598) (p 2608) (p 2651) (p 2656) (p 2663) (p 2665) (p 2685) (p 2696) (p 2737) (p 2778) (p 2797) (p 2807) (p 2811) (p 2829) (p 2839) (p 2850) (p 2860) (p 2870) (p 2901) (p 3016) (p 3051) (p 3093) (p 3309) (p 3367) (p 3379) (p 3425) (p 3582) (p 3695) (p 3759) (p 3819) (p 3873) (p 3958) (p 4104) (p 4117) (p 4140) (p 4193) (p 4194) (p 4198) (p 4210) (p 4243) (p 4399) (p 4632) (p 4650) (p 4700) (p 4752) (p 4753) (p 4781) (p 4814) (p 4869) (p 4885) (p 4972) (derived105440 p h) (derived105434 p h) (derived105378 p h) (derived106257 p h) (derived105514 p h) (derived105373 p h) (derived95963 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived106609 p h) (derived96078 p h) (derived95141 p h) (derived93816 p h) (h 11042) (derived102297 p h) (derived103475 p h) (derived91068 p h) (derived96428 p h) (derived79705 p h) (derived96408 p h) (derived105882 p h) (derived101098 p h) (derived106027 p h) (derived96017 p h) (derived100363 p h) (derived91165 p h) (derived100735 p h) (derived81200 p h) (derived81850 p h) (derived96366 p h) (derived96367 p h) (derived82874 p h) (derived96395 p h) (derived95983 p h) (derived106610 p h) (derived101272 p h) (derived81596 p h) (derived75064 p h) (derived103381 p h) (derived96025 p h) (derived102848 p h) (derived95792 p h) (derived96481 p h) (derived87778 p h) (derived77876 p h) (derived96373 p h) (derived82556 p h) (derived102521 p h) (derived92030 p h) (h 32814) (derived90375 p h) (derived103603 p h) (derived83333 p h) (derived106611 p h) (derived75063 p h) (derived78198 p h) (derived99709 p h) (derived83665 p h) (derived106613 p h) (derived103846 p h) (derived83913 p h)

theorem derived106615 (p : Nat → Prop) (h : Inputs p) :
    (p 2295) ∨ (¬ p 2307) ∨ (p 3093) ∨ (p 3016) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106615 (p 2230) (p 2295) (p 2307) (p 2440) (p 2553) (p 2573) (p 3016) (p 3093) (derived103846 p h) (derived104611 p h) (derived87416 p h)

theorem derived106617 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (p 2911) ∨ (p 2396) ∨ (¬ p 2797) ∨ (¬ p 2295) ∨ (p 2363) ∨ (p 2427) ∨ (¬ p 2696) ∨ (p 2437) ∨ (p 2210) :=
  ElevenRUP.step106617 (p 2166) (p 2210) (p 2295) (p 2363) (p 2396) (p 2427) (p 2437) (p 2696) (p 2797) (p 2881) (p 2911) (p 3146) (p 3246) (p 3323) (p 4330) (p 4396) (p 4559) (p 4632) (p 4733) (derived106257 p h) (derived106329 p h) (derived105430 p h) (derived105701 p h) (derived102221 p h) (derived104050 p h) (derived105207 p h) (derived100859 p h) (derived92235 p h) (derived79319 p h)

theorem derived106619 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 2797) ∨ (¬ p 2295) ∨ (p 2363) ∨ (p 2891) ∨ (p 2427) ∨ (¬ p 2696) ∨ (p 2210) ∨ (¬ p 2440) :=
  ElevenRUP.step106619 (p 2210) (p 2295) (p 2363) (p 2427) (p 2440) (p 2459) (p 2668) (p 2696) (p 2797) (p 2881) (p 2891) (p 4133) (p 4733) (derived105712 p h) (derived105430 p h) (derived74491 p h) (derived79185 p h) (derived79363 p h)

theorem derived106620 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2797) ∨ (¬ p 2295) ∨ (p 2363) ∨ (p 2891) ∨ (p 2427) ∨ (¬ p 2737) ∨ (¬ p 2696) ∨ (p 2437) ∨ (p 2210) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106620 (p 2166) (p 2177) (p 2210) (p 2230) (p 2248) (p 2264) (p 2295) (p 2331) (p 2363) (p 2373) (p 2396) (p 2427) (p 2437) (p 2440) (p 2459) (p 2470) (p 2651) (p 2656) (p 2663) (p 2665) (p 2696) (p 2737) (p 2797) (p 2881) (p 2891) (p 2911) (p 3146) (p 3389) (p 3693) (p 3747) (p 3950) (p 3955) (p 4042) (p 4112) (p 4156) (p 4327) (p 4404) (p 4559) (p 4972) (derived105701 p h) (derived105365 p h) (derived105373 p h) (derived105381 p h) (derived96453 p h) (derived96077 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived43497 p h) (derived78596 p h) (derived92207 p h) (derived106619 p h) (derived96358 p h) (derived96359 p h) (derived98517 p h) (derived98747 p h) (derived92716 p h) (derived78741 p h) (derived96419 p h) (derived94352 p h) (derived75479 p h) (derived87459 p h) (derived106617 p h) (derived92936 p h) (derived74852 p h) (derived77508 p h)

theorem derived106623 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 2850) ∨ (p 3093) ∨ (p 3016) ∨ (¬ p 2785) ∨ (¬ p 2274) ∨ (p 3379) ∨ (¬ p 3309) ∨ (¬ p 2667) :=
  ElevenRUP.step106623 (p 2274) (p 2295) (p 2307) (p 2493) (p 2505) (p 2553) (p 2667) (p 2785) (p 2850) (p 3016) (p 3093) (p 3309) (p 3379) (p 3422) (p 4390) (p 4814) (derived105440 p h) (derived78668 p h) (derived103846 p h) (derived87865 p h) (derived79808 p h) (derived96274 p h) (derived96943 p h) (derived87290 p h)

theorem derived106625 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (p 2363) ∨ (p 3399) ∨ (p 2563) ∨ (¬ p 4153) ∨ (¬ p 2696) ∨ (¬ p 4140) ∨ (p 2437) ∨ (¬ p 2406) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106625 (p 2156) (p 2187) (p 2190) (p 2192) (p 2230) (p 2255) (p 2331) (p 2352) (p 2363) (p 2383) (p 2406) (p 2427) (p 2437) (p 2440) (p 2459) (p 2470) (p 2493) (p 2509) (p 2510) (p 2528) (p 2563) (p 2573) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2696) (p 2727) (p 2797) (p 2881) (p 2891) (p 2901) (p 2911) (p 3005) (p 3073) (p 3083) (p 3096) (p 3125) (p 3136) (p 3146) (p 3156) (p 3166) (p 3256) (p 3322) (p 3323) (p 3399) (p 3449) (p 3527) (p 3544) (p 3743) (p 3878) (p 3948) (p 4031) (p 4140) (p 4153) (p 4186) (p 4198) (p 4210) (p 4330) (p 4399) (p 4431) (p 4558) (p 4620) (p 4683) (p 4686) (p 4688) (p 4700) (p 4733) (p 4814) (p 4902) (p 4972) (p 4976) (p 5008) (derived105469 p h) (derived105367 p h) (derived105465 p h) (derived106329 p h) (derived105373 p h) (derived105440 p h) (derived105400 p h) (derived105430 p h) (derived105456 p h) (derived96017 p h) (derived75064 p h) (derived96016 p h) (derived85437 p h) (derived93561 p h) (derived96437 p h) (derived96482 p h) (derived96481 p h) (derived96429 p h) (derived98962 p h) (derived96409 p h) (derived100245 p h) (derived104436 p h) (derived96428 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived106276 p h) (derived101769 p h) (derived100363 p h) (derived75063 p h) (h 6670) (derived97996 p h) (derived90987 p h) (derived87394 p h) (derived95235 p h) (derived84343 p h) (derived84349 p h) (derived44465 p h) (derived97247 p h) (derived97962 p h) (derived66699 p h) (derived97963 p h) (derived94051 p h) (derived104100 p h) (derived79937 p h) (derived96441 p h) (derived71205 p h) (derived91169 p h) (derived102269 p h) (derived92177 p h) (derived74786 p h) (h 7550) (derived97015 p h) (h 27565) (derived66365 p h) (derived93398 p h) (h 7555) (derived75067 p h) (derived80174 p h) (derived103075 p h) (derived80634 p h) (derived79034 p h)

theorem derived106626 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 4341) ∨ (p 2797) ∨ (p 2891) ∨ (p 2427) ∨ (¬ p 2295) ∨ (p 2363) ∨ (p 2284) ∨ (p 2210) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106626 (p 2210) (p 2230) (p 2248) (p 2264) (p 2284) (p 2295) (p 2331) (p 2363) (p 2427) (p 2440) (p 2459) (p 2630) (p 2651) (p 2656) (p 2663) (p 2797) (p 2881) (p 2891) (p 3005) (p 3256) (p 4117) (p 4133) (p 4341) (p 4550) (p 4733) (p 4790) (p 4972) (derived106424 p h) (derived105712 p h) (derived105365 p h) (derived105430 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived103124 p h) (derived74491 p h) (derived76171 p h) (derived75524 p h) (derived102508 p h) (derived87023 p h) (derived99273 p h)

theorem derived106627 (p : Nat → Prop) (h : Inputs p) :
    (p 2264) ∨ (¬ p 5109) ∨ (p 2459) ∨ (¬ p 2881) ∨ (¬ p 3297) ∨ (p 2166) ∨ (¬ p 3693) ∨ (p 2797) ∨ (¬ p 3552) ∨ (¬ p 3543) ∨ (p 2437) ∨ (¬ p 3040) ∨ (p 2210) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106627 (p 2166) (p 2177) (p 2210) (p 2230) (p 2248) (p 2264) (p 2331) (p 2437) (p 2440) (p 2449) (p 2459) (p 2470) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2685) (p 2797) (p 2881) (p 2911) (p 3040) (p 3146) (p 3246) (p 3297) (p 3389) (p 3516) (p 3543) (p 3552) (p 3657) (p 3693) (p 3747) (p 3755) (p 4112) (p 4280) (p 4327) (p 4404) (p 4559) (p 4656) (p 4790) (p 4972) (p 5109) (p 5295) (derived106424 p h) (derived105701 p h) (derived105365 p h) (derived105599 p h) (derived105373 p h) (derived105381 p h) (derived96417 p h) (derived96359 p h) (derived96077 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived103124 p h) (derived76676 p h) (derived99411 p h) (derived82160 p h) (derived78741 p h) (derived102489 p h) (derived87459 p h) (derived94936 p h) (derived89127 p h) (derived102648 p h) (derived89113 p h) (derived100859 p h) (derived92936 p h) (derived74852 p h) (derived77508 p h)

theorem derived106628 (p : Nat → Prop) (h : Inputs p) :
    (p 2088) ∨ (¬ p 5557) ∨ (¬ p 3146) ∨ (p 2761) ∨ (¬ p 2177) ∨ (p 2850) ∨ (p 3256) ∨ (p 2459) ∨ (¬ p 3697) ∨ (p 2972) ∨ (¬ p 2295) ∨ (p 2210) ∨ (¬ p 2331) ∨ (¬ p 4031) :=
  ElevenRUP.step106628 (p 2088) (p 2177) (p 2210) (p 2248) (p 2295) (p 2331) (p 2459) (p 2533) (p 2761) (p 2850) (p 2972) (p 3146) (p 3256) (p 3266) (p 3680) (p 3697) (p 3791) (p 3969) (p 4031) (p 4260) (p 4322) (p 4455) (p 4456) (p 4826) (p 4905) (p 5063) (p 5396) (p 5401) (p 5557) (p 5567) (p 5568) (p 5571) (p 6124) (p 6125) (derived105474 p h) (derived105995 p h) (derived105444 p h) (derived105365 p h) (derived96311 p h) (derived102705 p h) (derived102704 p h) (derived94643 p h) (derived104779 p h) (h 9791) (derived101015 p h) (derived66485 p h) (h 9314) (h 9797) (derived66468 p h) (derived41917 p h) (h 9308) (h 13957) (derived75525 p h) (derived66615 p h) (h 13964)

theorem derived106629 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3005) ∨ (p 2850) ∨ (p 2685) ∨ (¬ p 4378) ∨ (p 3256) ∨ (p 2459) ∨ (p 3083) ∨ (¬ p 3697) ∨ (p 2166) ∨ (¬ p 4947) ∨ (p 2972) ∨ (¬ p 2122) ∨ (p 2573) ∨ (¬ p 4592) ∨ (¬ p 2295) ∨ (¬ p 3543) ∨ (¬ p 4438) ∨ (¬ p 2807) ∨ (¬ p 2829) ∨ (p 2210) ∨ (¬ p 5145) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106629 (p 2088) (p 2122) (p 2166) (p 2177) (p 2210) (p 2230) (p 2248) (p 2295) (p 2331) (p 2396) (p 2440) (p 2449) (p 2459) (p 2470) (p 2482) (p 2528) (p 2533) (p 2573) (p 2651) (p 2656) (p 2663) (p 2665) (p 2685) (p 2761) (p 2807) (p 2829) (p 2850) (p 2972) (p 3005) (p 3083) (p 3146) (p 3256) (p 3266) (p 3346) (p 3355) (p 3543) (p 3657) (p 3680) (p 3697) (p 3941) (p 3950) (p 4031) (p 4155) (p 4322) (p 4378) (p 4438) (p 4592) (p 4666) (p 4947) (p 4972) (p 5063) (p 5145) (p 5180) (p 5185) (p 5396) (p 5401) (p 5555) (p 5557) (p 5561) (derived105658 p h) (derived105365 p h) (derived105474 p h) (derived105373 p h) (derived96419 p h) (derived96417 p h) (derived93817 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived96016 p h) (derived93334 p h) (derived100160 p h) (derived46848 p h) (derived86523 p h) (h 9727) (derived45719 p h) (derived75479 p h) (derived66484 p h) (derived96311 p h) (h 9720) (derived106628 p h) (derived81926 p h) (derived101015 p h) (h 9314) (derived66468 p h) (h 9308) (derived61395 p h) (h 8776) (derived66444 p h) (h 8782) (derived102979 p h) (derived87461 p h) (derived78446 p h) (derived96955 p h)

theorem derived106630 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (p 2459) ∨ (¬ p 2881) ∨ (¬ p 3297) ∨ (p 3083) ∨ (¬ p 3697) ∨ (p 2166) ∨ (¬ p 3693) ∨ (¬ p 4947) ∨ (p 2972) ∨ (p 2573) ∨ (p 2797) ∨ (¬ p 4592) ∨ (¬ p 2295) ∨ (¬ p 3543) ∨ (¬ p 3363) ∨ (¬ p 4438) ∨ (p 2437) ∨ (¬ p 2829) ∨ (¬ p 3040) ∨ (p 2210) ∨ (¬ p 5145) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106630 (p 2088) (p 2122) (p 2166) (p 2210) (p 2230) (p 2264) (p 2295) (p 2331) (p 2341) (p 2437) (p 2440) (p 2459) (p 2470) (p 2528) (p 2573) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2685) (p 2797) (p 2807) (p 2829) (p 2850) (p 2881) (p 2972) (p 3005) (p 3040) (p 3083) (p 3166) (p 3177) (p 3256) (p 3297) (p 3363) (p 3475) (p 3543) (p 3552) (p 3693) (p 3697) (p 4378) (p 4437) (p 4438) (p 4590) (p 4592) (p 4650) (p 4790) (p 4841) (p 4947) (p 4972) (p 5008) (p 5109) (p 5145) (derived105469 p h) (derived106424 p h) (derived105373 p h) (derived93397 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived102194 p h) (derived90293 p h) (derived96452 p h) (derived96078 p h) (derived95141 p h) (derived101769 p h) (derived96876 p h) (derived103124 p h) (derived96403 p h) (derived102660 p h) (derived106627 p h) (derived96456 p h) (derived104070 p h) (derived89114 p h) (derived96447 p h) (derived103464 p h) (derived106629 p h) (derived101018 p h) (derived87068 p h) (derived98449 p h) (derived87461 p h)

theorem derived106631 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (¬ p 2696) ∨ (¬ p 2274) ∨ (p 2437) ∨ (¬ p 2829) ∨ (p 2608) ∨ (¬ p 5145) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106631 (p 2088) (p 2132) (p 2156) (p 2166) (p 2177) (p 2187) (p 2192) (p 2210) (p 2220) (p 2230) (p 2255) (p 2274) (p 2284) (p 2295) (p 2307) (p 2331) (p 2352) (p 2363) (p 2373) (p 2396) (p 2406) (p 2427) (p 2437) (p 2440) (p 2459) (p 2493) (p 2497) (p 2528) (p 2533) (p 2563) (p 2573) (p 2598) (p 2608) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2696) (p 2727) (p 2737) (p 2751) (p 2753) (p 2761) (p 2797) (p 2829) (p 2881) (p 2891) (p 2972) (p 2982) (p 3016) (p 3040) (p 3051) (p 3083) (p 3093) (p 3096) (p 3136) (p 3146) (p 3156) (p 3166) (p 3177) (p 3256) (p 3266) (p 3286) (p 3297) (p 3319) (p 3323) (p 3346) (p 3355) (p 3363) (p 3379) (p 3399) (p 3519) (p 3543) (p 3564) (p 3609) (p 3657) (p 3680) (p 3693) (p 3697) (p 3948) (p 3958) (p 4031) (p 4041) (p 4117) (p 4134) (p 4140) (p 4153) (p 4210) (p 4281) (p 4312) (p 4322) (p 4341) (p 4389) (p 4399) (p 4421) (p 4437) (p 4438) (p 4445) (p 4509) (p 4558) (p 4559) (p 4592) (p 4598) (p 4607) (p 4632) (p 4700) (p 4715) (p 4759) (p 4790) (p 4814) (p 4947) (p 4972) (p 5008) (p 5046) (p 5145) (p 5180) (p 5185) (p 6106) (p 6107) (derived105469 p h) (derived106257 p h) (derived105378 p h) (derived105367 p h) (derived105400 p h) (derived105440 p h) (derived105373 p h) (derived106424 p h) (derived105472 p h) (derived105423 p h) (derived106343 p h) (derived105701 p h) (derived105392 p h) (derived105379 p h) (derived103475 p h) (derived91068 p h) (derived96428 p h) (derived79705 p h) (derived96429 p h) (derived100363 p h) (derived100245 p h) (derived104436 p h) (derived43222 p h) (derived75062 p h) (derived98962 p h) (derived79891 p h) (derived95924 p h) (derived101272 p h) (derived96024 p h) (derived103381 p h) (derived96017 p h) (derived75064 p h) (derived96409 p h) (derived95238 p h) (derived80989 p h) (derived99643 p h) (derived96406 p h) (derived81264 p h) (derived103124 p h) (derived86962 p h) (derived106125 p h) (derived95963 p h) (derived95899 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived93774 p h) (derived106491 p h) (derived96022 p h) (derived91518 p h) (derived101769 p h) (derived96876 p h) (derived96016 p h) (derived103603 p h) (derived106615 p h) (derived85437 p h) (derived106625 p h) (derived75069 p h) (derived106528 p h) (derived91674 p h) (derived106620 p h) (derived84344 p h) (derived87035 p h) (derived87037 p h) (derived102883 p h) (derived96197 p h) (derived101912 p h) (derived99315 p h) (derived99311 p h) (derived91018 p h) (derived91679 p h) (derived87404 p h) (derived78956 p h) (derived96399 p h) (derived91125 p h) (derived96442 p h) (derived96342 p h) (derived94353 p h) (derived94352 p h) (derived80065 p h) (derived96460 p h) (derived93418 p h) (h 20368) (derived95302 p h) (derived93397 p h) (derived83423 p h) (derived106487 p h) (derived96842 p h) (derived106626 p h) (derived103030 p h) (derived96417 p h) (derived96416 p h) (derived106630 p h) (derived68607 p h) (h 30629) (derived95466 p h) (derived103713 p h) (derived102842 p h) (derived78458 p h) (derived96311 p h) (derived102979 p h) (derived45719 p h) (h 8782) (derived75260 p h) (derived66444 p h) (derived93383 p h) (h 8776) (h 13790) (derived61395 p h) (derived66609 p h) (h 13783)

theorem derived106632 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 2829) ∨ (p 2608) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106632 (p 2156) (p 2210) (p 2230) (p 2255) (p 2274) (p 2284) (p 2295) (p 2307) (p 2331) (p 2406) (p 2437) (p 2440) (p 2493) (p 2505) (p 2553) (p 2563) (p 2608) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2667) (p 2696) (p 2727) (p 2774) (p 2785) (p 2829) (p 2850) (p 3016) (p 3093) (p 3136) (p 3309) (p 3379) (p 3958) (p 4031) (p 4117) (p 4198) (p 4210) (p 4399) (p 4632) (p 4700) (p 4790) (p 4814) (p 4972) (p 5145) (p 5217) (derived106424 p h) (derived105367 p h) (derived105440 p h) (derived105378 p h) (derived105373 p h) (derived106257 p h) (derived105493 p h) (derived106609 p h) (derived103475 p h) (derived91068 p h) (derived96428 p h) (derived79705 p h) (derived100245 p h) (derived104436 p h) (derived96289 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived96448 p h) (derived103124 p h) (derived96017 p h) (derived96016 p h) (derived100363 p h) (derived106614 p h) (derived86309 p h) (derived43222 p h) (derived102227 p h) (derived75062 p h) (derived101272 p h) (derived75064 p h) (derived103381 p h) (derived96481 p h) (derived106631 p h) (derived78668 p h) (derived106623 p h) (derived103846 p h) (derived95961 p h) (derived79808 p h) (derived96943 p h)

theorem derived106633 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 4279) ∨ (¬ p 2507) ∨ (¬ p 2386) ∨ (¬ p 4338) ∨ (p 2437) ∨ (¬ p 3948) ∨ (¬ p 3309) :=
  ElevenRUP.step106633 (p 2307) (p 2312) (p 2386) (p 2437) (p 2507) (p 3016) (p 3309) (p 3948) (p 4279) (p 4338) (p 4814) (derived105440 p h) (derived101806 p h) (derived85165 p h) (derived87562 p h)

theorem derived106634 (p : Nat → Prop) (h : Inputs p) :
    (p 2295) ∨ (¬ p 2307) ∨ (p 3093) ∨ (p 2437) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106634 (p 2230) (p 2295) (p 2307) (p 2437) (p 2440) (p 2553) (p 2586) (p 3016) (p 3093) (p 3921) (derived105372 p h) (derived103846 p h) (derived101858 p h) (derived106615 p h) (derived75161 p h)

theorem derived106635 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2829) ∨ (p 2608) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106635 (p 2156) (p 2166) (p 2192) (p 2210) (p 2230) (p 2241) (p 2255) (p 2274) (p 2284) (p 2295) (p 2307) (p 2331) (p 2373) (p 2386) (p 2406) (p 2427) (p 2437) (p 2440) (p 2493) (p 2507) (p 2563) (p 2573) (p 2608) (p 2651) (p 2656) (p 2663) (p 2665) (p 2696) (p 2727) (p 2737) (p 2797) (p 2811) (p 2829) (p 2839) (p 2850) (p 2992) (p 3051) (p 3093) (p 3136) (p 3309) (p 3367) (p 3369) (p 3379) (p 3389) (p 3660) (p 3695) (p 3741) (p 3879) (p 3948) (p 4117) (p 4210) (p 4275) (p 4279) (p 4282) (p 4328) (p 4336) (p 4338) (p 4399) (p 4518) (p 4632) (p 4700) (p 4752) (p 4753) (p 4814) (p 4972) (p 5190) (derived105367 p h) (derived106257 p h) (derived105487 p h) (derived106113 p h) (derived105373 p h) (derived105440 p h) (derived105434 p h) (derived105514 p h) (derived103475 p h) (derived91068 p h) (derived96428 p h) (derived79705 p h) (derived96464 p h) (h 5209) (derived87995 p h) (derived104473 p h) (derived100245 p h) (derived104436 p h) (derived96429 p h) (derived105882 p h) (derived96927 p h) (derived101098 p h) (derived100365 p h) (derived82296 p h) (derived96339 p h) (derived96017 p h) (derived100363 p h) (derived106609 p h) (derived106632 p h) (derived90849 p h) (derived103380 p h) (derived85301 p h) (derived93347 p h) (derived79993 p h) (derived85491 p h) (derived75062 p h) (derived87393 p h) (derived102260 p h) (derived85162 p h) (derived79172 p h) (derived96935 p h) (derived76001 p h) (derived75069 p h) (derived84339 p h) (derived91680 p h) (derived88131 p h) (derived96382 p h) (derived90965 p h) (derived87271 p h) (derived96946 p h) (derived96281 p h) (derived106633 p h) (derived106634 p h) (derived92141 p h) (derived87157 p h) (derived91165 p h) (derived81200 p h) (derived81874 p h) (derived96366 p h) (derived87804 p h) (derived83821 p h)

theorem derived106636 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3016) ∨ (¬ p 2295) ∨ (¬ p 2406) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106636 (p 2230) (p 2295) (p 2406) (p 2440) (p 2553) (p 2651) (p 2656) (p 2663) (p 3016) (p 3019) (h 5209) (derived87995 p h) (derived96927 p h) (derived101604 p h) (derived46048 p h) (derived79304 p h)

theorem derived106637 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (p 2098) ∨ (¬ p 3051) ∨ (¬ p 2427) ∨ (¬ p 2807) ∨ (¬ p 4117) :=
  ElevenRUP.step106637 (p 2098) (p 2264) (p 2427) (p 2717) (p 2807) (p 2881) (p 2960) (p 3051) (p 4117) (p 4533) (p 4807) (p 4882) (derived105394 p h) (derived105453 p h) (derived105377 p h) (derived104103 p h) (derived98222 p h) (derived77955 p h) (derived100709 p h)

theorem derived106638 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (¬ p 2553) ∨ (¬ p 4311) ∨ (p 2187) ∨ (¬ p 2373) ∨ (¬ p 2427) ∨ (p 2707) ∨ (p 2274) ∨ (¬ p 2807) ∨ (¬ p 2295) ∨ (¬ p 2307) ∨ (¬ p 3426) ∨ (p 2132) ∨ (p 2696) ∨ (p 2737) ∨ (p 2829) ∨ (¬ p 2641) ∨ (p 2608) ∨ (¬ p 4117) ∨ (¬ p 3987) ∨ (¬ p 2230) :=
  ElevenRUP.step106638 (p 2098) (p 2132) (p 2177) (p 2187) (p 2230) (p 2249) (p 2274) (p 2295) (p 2307) (p 2319) (p 2341) (p 2352) (p 2363) (p 2373) (p 2383) (p 2427) (p 2459) (p 2528) (p 2553) (p 2608) (p 2641) (p 2668) (p 2696) (p 2707) (p 2717) (p 2737) (p 2742) (p 2753) (p 2774) (p 2786) (p 2807) (p 2819) (p 2829) (p 2881) (p 3051) (p 3146) (p 3426) (p 3552) (p 3987) (p 3988) (p 4031) (p 4117) (p 4155) (p 4311) (p 4326) (p 4401) (p 4489) (p 4718) (p 4790) (derived105425 p h) (derived105390 p h) (derived106424 p h) (derived106513 p h) (derived102299 p h) (derived96016 p h) (h 19331) (derived93817 p h) (derived96452 p h) (derived96969 p h) (derived96922 p h) (derived96406 p h) (derived90544 p h) (derived106315 p h) (h 11044) (derived90518 p h) (derived78358 p h) (derived78787 p h) (derived77005 p h) (derived96378 p h) (derived84979 p h) (derived92404 p h) (derived86430 p h) (derived106637 p h) (derived78329 p h) (derived78546 p h) (derived89226 p h) (derived104971 p h) (derived88258 p h)

theorem derived106639 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 3256) ∨ (¬ p 2553) ∨ (¬ p 2901) ∨ (¬ p 2373) ∨ (p 3399) ∨ (p 2707) ∨ (p 2274) ∨ (p 2608) ∨ (¬ p 4452) ∨ (¬ p 3166) ∨ (¬ p 2230) ∨ (¬ p 3879) :=
  ElevenRUP.step106639 (p 2230) (p 2248) (p 2274) (p 2373) (p 2396) (p 2553) (p 2608) (p 2707) (p 2717) (p 2901) (p 3146) (p 3166) (p 3246) (p 3256) (p 3399) (p 3434) (p 3631) (p 3879) (p 4204) (p 4452) (p 4518) (p 4668) (p 4669) (p 4718) (p 4902) (p 5190) (derived105414 p h) (derived105365 p h) (derived105456 p h) (derived105425 p h) (derived105487 p h) (derived105415 p h) (derived106113 p h) (derived100361 p h) (derived88374 p h) (derived88444 p h) (derived75884 p h) (derived88390 p h) (derived89328 p h) (derived89554 p h)

theorem derived106640 (p : Nat → Prop) (h : Inputs p) :
    (p 2274) ∨ (¬ p 4279) ∨ (¬ p 4338) ∨ (p 2437) ∨ (¬ p 2307) ∨ (p 2608) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106640 (p 2122) (p 2132) (p 2166) (p 2177) (p 2187) (p 2230) (p 2241) (p 2255) (p 2274) (p 2284) (p 2295) (p 2307) (p 2319) (p 2331) (p 2341) (p 2352) (p 2363) (p 2373) (p 2406) (p 2427) (p 2437) (p 2440) (p 2470) (p 2528) (p 2553) (p 2563) (p 2573) (p 2584) (p 2608) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2696) (p 2707) (p 2717) (p 2727) (p 2737) (p 2807) (p 2829) (p 2850) (p 2901) (p 2946) (p 3016) (p 3083) (p 3093) (p 3156) (p 3166) (p 3201) (p 3256) (p 3309) (p 3325) (p 3379) (p 3399) (p 3426) (p 3660) (p 3878) (p 3879) (p 3948) (p 3953) (p 3987) (p 4117) (p 4210) (p 4275) (p 4279) (p 4281) (p 4311) (p 4336) (p 4338) (p 4401) (p 4434) (p 4452) (p 4489) (p 4518) (p 4555) (p 4632) (p 4650) (p 4700) (p 4752) (p 4753) (p 4790) (p 4814) (p 4972) (p 5008) (p 5085) (derived105469 p h) (derived105367 p h) (derived106424 p h) (derived105434 p h) (derived106257 p h) (derived106113 p h) (derived105542 p h) (derived105440 p h) (derived106144 p h) (derived105373 p h) (derived105514 p h) (derived105390 p h) (derived103475 p h) (derived106635 p h) (derived96374 p h) (derived93634 p h) (derived106634 p h) (derived106636 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived96078 p h) (derived95141 p h) (derived96969 p h) (derived91068 p h) (derived104473 p h) (derived103124 p h) (derived105882 p h) (derived68861 p h) (derived103792 p h) (derived81200 p h) (derived90589 p h) (derived96484 p h) (derived96428 p h) (derived82744 p h) (derived106315 p h) (derived100245 p h) (derived95899 p h) (derived101098 p h) (derived93774 p h) (derived96429 p h) (derived96287 p h) (derived96449 p h) (derived101769 p h) (derived102873 p h) (derived100365 p h) (derived100363 p h) (derived90849 p h) (derived103380 p h) (derived106604 p h) (derived103290 p h) (derived76001 p h) (derived90886 p h) (derived93347 p h) (derived75062 p h) (derived69099 p h) (derived91680 p h) (derived75063 p h) (derived87393 p h) (derived79172 p h) (derived96303 p h) (derived79039 p h) (derived87445 p h) (derived96934 p h) (derived79409 p h) (derived102484 p h) (derived78503 p h) (derived106638 p h) (derived103503 p h) (derived83881 p h) (derived93398 p h) (derived75067 p h) (derived106639 p h) (derived76884 p h) (derived78546 p h) (derived96473 p h) (derived68848 p h) (h 6284)

theorem derived106641 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2717) ∨ (¬ p 3425) ∨ (¬ p 5085) ∨ (¬ p 2274) ∨ (¬ p 4279) ∨ (¬ p 4783) ∨ (¬ p 2807) ∨ (p 2437) ∨ (¬ p 3819) ∨ (p 2839) ∨ (¬ p 3582) ∨ (¬ p 4477) ∨ (p 2132) ∨ (¬ p 2406) ∨ (¬ p 2753) ∨ (¬ p 4117) ∨ (¬ p 2440) :=
  ElevenRUP.step106641 (p 2098) (p 2132) (p 2177) (p 2264) (p 2274) (p 2341) (p 2406) (p 2437) (p 2440) (p 2563) (p 2619) (p 2717) (p 2753) (p 2807) (p 2839) (p 2860) (p 3425) (p 3537) (p 3582) (p 3819) (p 4117) (p 4188) (p 4279) (p 4359) (p 4477) (p 4509) (p 4753) (p 4783) (p 4804) (p 4807) (p 5085) (derived105514 p h) (derived105392 p h) (derived77952 p h) (derived77955 p h) (derived76884 p h) (derived89912 p h) (derived100709 p h) (derived93163 p h) (derived89708 p h) (derived88677 p h) (derived96150 p h) (derived62452 p h) (derived101917 p h) (derived81596 p h) (derived88211 p h)

theorem derived106642 (p : Nat → Prop) (h : Inputs p) :
    (p 2563) ∨ (p 2717) ∨ (p 2707) ∨ (¬ p 2427) ∨ (¬ p 4140) ∨ (p 3016) ∨ (¬ p 2850) ∨ (p 2608) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106642 (p 2156) (p 2187) (p 2230) (p 2352) (p 2363) (p 2383) (p 2427) (p 2440) (p 2459) (p 2510) (p 2528) (p 2563) (p 2573) (p 2584) (p 2608) (p 2665) (p 2707) (p 2717) (p 2819) (p 2850) (p 2860) (p 2870) (p 2901) (p 3016) (p 3051) (p 3083) (p 3246) (p 3422) (p 3434) (p 3537) (p 3582) (p 3587) (p 3609) (p 3685) (p 3695) (p 3879) (p 4031) (p 4133) (p 4140) (p 4193) (p 4198) (p 4375) (p 4399) (p 4420) (p 4558) (p 4668) (p 4669) (p 4700) (p 4753) (p 4861) (p 5190) (derived105414 p h) (derived105707 p h) (derived105400 p h) (derived105373 p h) (derived105415 p h) (derived105514 p h) (derived105712 p h) (derived105487 p h) (derived97921 p h) (derived89777 p h) (derived88258 p h) (derived101674 p h) (derived88325 p h) (derived100363 p h) (derived75063 p h) (derived100365 p h) (derived88374 p h) (derived96366 p h) (derived86718 p h) (derived102334 p h) (derived96016 p h) (h 19331) (derived96367 p h) (derived96017 p h) (derived75064 p h) (derived81596 p h) (derived78008 p h) (derived103147 p h) (derived96481 p h) (derived95792 p h) (derived83372 p h) (derived94768 p h) (derived100831 p h) (derived96934 p h) (derived87796 p h) (derived83960 p h) (derived96379 p h) (derived96275 p h) (derived96441 p h) (derived88307 p h) (derived74990 p h) (derived88404 p h)

theorem derived106643 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (¬ p 2274) ∨ (¬ p 4279) ∨ (¬ p 2295) ∨ (p 2437) ∨ (¬ p 3819) ∨ (p 3367) ∨ (p 2598) ∨ (¬ p 2850) ∨ (¬ p 4477) ∨ (¬ p 3426) ∨ (p 2132) ∨ (p 2608) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106643 (p 2132) (p 2187) (p 2230) (p 2274) (p 2284) (p 2295) (p 2352) (p 2363) (p 2373) (p 2383) (p 2396) (p 2406) (p 2427) (p 2437) (p 2440) (p 2459) (p 2563) (p 2573) (p 2598) (p 2608) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2685) (p 2707) (p 2717) (p 2753) (p 2807) (p 2819) (p 2839) (p 2850) (p 2901) (p 3016) (p 3146) (p 3166) (p 3201) (p 3246) (p 3367) (p 3425) (p 3426) (p 3434) (p 3475) (p 3582) (p 3658) (p 3660) (p 3695) (p 3741) (p 3759) (p 3819) (p 3879) (p 3988) (p 4112) (p 4117) (p 4133) (p 4140) (p 4156) (p 4194) (p 4279) (p 4477) (p 4650) (p 4668) (p 4669) (p 4700) (p 4753) (p 4783) (p 4790) (p 5008) (p 5085) (p 5190) (derived105469 p h) (derived106424 p h) (derived105414 p h) (derived105712 p h) (derived105373 p h) (derived105487 p h) (derived105415 p h) (derived105514 p h) (derived95963 p h) (derived103475 p h) (derived106636 p h) (derived96077 p h) (derived96453 p h) (h 29696) (derived95983 p h) (derived103124 p h) (derived96403 p h) (derived96078 p h) (derived82973 p h) (derived96397 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived95141 p h) (derived96366 p h) (derived83821 p h) (derived96367 p h) (derived96406 p h) (derived101769 p h) (derived100365 p h) (derived100363 p h) (derived88131 p h) (derived75063 p h) (h 6803) (derived96302 p h) (derived96303 p h) (derived76147 p h) (derived76158 p h) (derived106641 p h) (derived88374 p h) (derived88258 p h) (derived79379 p h) (derived106642 p h) (derived93347 p h) (derived75062 p h) (derived88322 p h) (derived87393 p h) (derived72677 p h) (derived102299 p h) (derived98501 p h) (derived102894 p h) (derived74841 p h) (derived92389 p h) (derived75065 p h) (derived88390 p h) (derived105303 p h) (derived89628 p h)

theorem derived106644 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4279) ∨ (¬ p 4338) ∨ (p 2437) ∨ (¬ p 2307) ∨ (p 2608) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106644 (p 2098) (p 2122) (p 2132) (p 2220) (p 2230) (p 2241) (p 2264) (p 2274) (p 2295) (p 2307) (p 2319) (p 2331) (p 2341) (p 2373) (p 2406) (p 2427) (p 2437) (p 2440) (p 2553) (p 2573) (p 2598) (p 2608) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2685) (p 2696) (p 2707) (p 2717) (p 2737) (p 2753) (p 2786) (p 2807) (p 2829) (p 2839) (p 2850) (p 2870) (p 2881) (p 2911) (p 3016) (p 3051) (p 3093) (p 3201) (p 3309) (p 3367) (p 3379) (p 3425) (p 3426) (p 3475) (p 3582) (p 3695) (p 3759) (p 3819) (p 3920) (p 3953) (p 3987) (p 4001) (p 4117) (p 4136) (p 4210) (p 4279) (p 4338) (p 4389) (p 4399) (p 4477) (p 4650) (p 4715) (p 4752) (p 4753) (p 4783) (p 4790) (p 4807) (p 4904) (p 4972) (p 5085) (derived105434 p h) (derived106424 p h) (derived105373 p h) (derived105514 p h) (derived105423 p h) (derived106635 p h) (derived96374 p h) (derived93634 p h) (derived106634 p h) (derived103475 p h) (derived106636 p h) (derived96024 p h) (derived79283 p h) (derived94485 p h) (h 5209) (derived87995 p h) (derived91068 p h) (derived104473 p h) (derived103124 p h) (derived105882 p h) (derived68861 p h) (derived103792 p h) (derived81200 p h) (derived82874 p h) (derived95983 p h) (derived96403 p h) (derived96078 p h) (derived82973 p h) (derived96397 p h) (derived96927 p h) (derived95141 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived96969 p h) (h 17508) (derived96366 p h) (derived68719 p h) (derived83821 p h) (derived96367 p h) (derived90589 p h) (derived96486 p h) (derived96484 p h) (derived96428 p h) (derived82744 p h) (derived96406 p h) (derived96017 p h) (derived106640 p h) (derived106643 p h) (derived95461 p h) (derived75069 p h) (derived92871 p h) (derived96363 p h) (derived86580 p h) (h 33078) (derived94842 p h) (derived96360 p h) (derived88366 p h) (derived77955 p h) (derived106641 p h) (derived96303 p h) (derived75579 p h) (derived87781 p h) (derived77898 p h) (derived95906 p h) (derived78956 p h) (derived89912 p h) (derived103315 p h) (derived100709 p h)

theorem derived106645 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (¬ p 2295) ∨ (¬ p 2307) ∨ (p 2839) ∨ (¬ p 2850) ∨ (p 2608) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106645 (p 2156) (p 2177) (p 2210) (p 2230) (p 2248) (p 2255) (p 2274) (p 2295) (p 2307) (p 2331) (p 2363) (p 2406) (p 2427) (p 2440) (p 2459) (p 2493) (p 2553) (p 2563) (p 2573) (p 2608) (p 2619) (p 2651) (p 2656) (p 2663) (p 2668) (p 2727) (p 2839) (p 2850) (p 2881) (p 2891) (p 2911) (p 2922) (p 2982) (p 3016) (p 3096) (p 3105) (p 3146) (p 3201) (p 3369) (p 3379) (p 3389) (p 3422) (p 3582) (p 3741) (p 3743) (p 3747) (p 3920) (p 3948) (p 3955) (p 4001) (p 4138) (p 4210) (p 4281) (p 4389) (p 4509) (p 4559) (p 4564) (p 4712) (p 4715) (p 4753) (p 4814) (p 4905) (p 4972) (p 5059) (p 5104) (p 5190) (derived105367 p h) (derived105440 p h) (derived105514 p h) (derived105487 p h) (derived105392 p h) (derived105423 p h) (derived105995 p h) (derived105701 p h) (derived105422 p h) (derived105401 p h) (derived105365 p h) (derived103475 p h) (derived106636 p h) (derived96024 p h) (derived79283 p h) (derived94485 p h) (derived96367 p h) (derived91068 p h) (derived96428 p h) (derived79705 p h) (derived96464 p h) (derived96429 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived100245 p h) (derived95899 p h) (derived87424 p h) (h 5809) (derived87271 p h) (derived91051 p h) (derived80333 p h) (derived77577 p h) (derived104425 p h) (derived88131 p h) (derived91678 p h) (derived77267 p h) (derived96482 p h) (derived85491 p h) (derived95461 p h) (derived106365 p h) (derived75473 p h) (derived87777 p h) (derived78310 p h) (derived96409 p h) (derived96359 p h) (derived81631 p h) (derived81625 p h) (derived84778 p h) (derived84715 p h) (derived78596 p h) (derived87334 p h) (derived96313 p h) (derived78741 p h) (derived82403 p h) (derived102976 p h) (derived84582 p h)

theorem derived106646 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 2307) ∨ (p 2608) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106646 (p 2122) (p 2132) (p 2192) (p 2230) (p 2241) (p 2274) (p 2295) (p 2307) (p 2319) (p 2331) (p 2406) (p 2427) (p 2437) (p 2440) (p 2598) (p 2608) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2685) (p 2696) (p 2707) (p 2717) (p 2737) (p 2753) (p 2786) (p 2807) (p 2829) (p 2839) (p 2850) (p 2870) (p 2881) (p 3051) (p 3093) (p 3201) (p 3309) (p 3367) (p 3379) (p 3389) (p 3425) (p 3426) (p 3475) (p 3582) (p 3658) (p 3695) (p 3759) (p 3819) (p 3953) (p 3957) (p 3987) (p 4117) (p 4210) (p 4279) (p 4338) (p 4399) (p 4477) (p 4650) (p 4715) (p 4752) (p 4753) (p 4783) (p 4790) (p 4972) (p 5085) (derived105423 p h) (derived106424 p h) (derived105434 p h) (derived105373 p h) (derived105514 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived96969 p h) (h 17508) (derived103475 p h) (derived91068 p h) (derived104473 p h) (derived103124 p h) (derived106635 p h) (derived68861 p h) (derived103792 p h) (derived81200 p h) (derived96366 p h) (derived68719 p h) (derived83821 p h) (derived82874 p h) (derived95983 p h) (derived96367 p h) (derived90589 p h) (derived96486 p h) (derived96484 p h) (derived96428 p h) (derived82744 p h) (derived96374 p h) (derived93634 p h) (derived96406 p h) (derived96403 p h) (derived96017 p h) (derived96078 p h) (derived106634 p h) (derived95141 p h) (derived82973 p h) (derived96397 p h) (derived106645 p h) (derived96281 p h) (h 6623) (derived106644 p h) (derived96302 p h) (derived96303 p h) (derived102260 p h) (derived76147 p h) (derived76158 p h) (derived96469 p h) (h 33487) (derived106643 p h) (derived106641 p h) (derived75069 p h) (derived88366 p h) (derived92871 p h) (derived86580 p h)

theorem derived106647 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2274) ∨ (¬ p 3422) ∨ (¬ p 2437) ∨ (¬ p 3819) ∨ (¬ p 2779) ∨ (p 2241) ∨ (¬ p 2406) ∨ (¬ p 3873) ∨ (¬ p 3547) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106647 (p 2156) (p 2187) (p 2230) (p 2241) (p 2249) (p 2255) (p 2274) (p 2284) (p 2352) (p 2363) (p 2373) (p 2383) (p 2386) (p 2406) (p 2427) (p 2437) (p 2440) (p 2459) (p 2493) (p 2553) (p 2563) (p 2573) (p 2584) (p 2630) (p 2651) (p 2656) (p 2665) (p 2685) (p 2727) (p 2751) (p 2779) (p 2819) (p 2881) (p 2891) (p 2901) (p 2911) (p 2946) (p 2992) (p 3016) (p 3136) (p 3201) (p 3422) (p 3547) (p 3569) (p 3580) (p 3819) (p 3873) (p 3879) (p 4031) (p 4203) (p 4210) (p 4282) (p 4375) (p 4419) (p 4431) (p 4558) (p 4646) (p 4700) (p 4710) (p 4753) (p 4790) (p 5086) (p 5087) (derived106343 p h) (derived106424 p h) (derived106513 p h) (derived105367 p h) (derived105400 p h) (derived105514 p h) (derived105373 p h) (derived105534 p h) (derived96275 p h) (derived96016 p h) (derived100365 p h) (derived100363 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived98023 p h) (derived104425 p h) (derived96935 p h) (derived96934 p h) (h 5209) (derived87995 p h) (derived50095 p h) (derived82395 p h) (derived98028 p h) (derived83046 p h) (derived87285 p h) (derived100245 p h) (derived82296 p h) (derived96339 p h) (h 36523) (derived97247 p h) (derived69917 p h) (derived96305 p h) (derived96304 p h) (derived103124 p h) (derived102335 p h) (derived83857 p h) (derived104436 p h) (derived96428 p h) (derived102873 p h) (derived106486 p h) (derived53072 p h) (derived98274 p h) (derived72677 p h) (derived94484 p h) (derived106598 p h) (derived90965 p h) (derived98082 p h) (derived86248 p h) (derived83960 p h) (derived74841 p h) (derived43515 p h) (derived105091 p h)

theorem derived106648 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2307) ∨ (p 2608) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106648 (p 2132) (p 2156) (p 2166) (p 2177) (p 2192) (p 2230) (p 2241) (p 2246) (p 2248) (p 2249) (p 2255) (p 2274) (p 2307) (p 2319) (p 2331) (p 2341) (p 2373) (p 2406) (p 2427) (p 2437) (p 2440) (p 2459) (p 2470) (p 2481) (p 2531) (p 2553) (p 2563) (p 2573) (p 2584) (p 2608) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2667) (p 2685) (p 2696) (p 2707) (p 2727) (p 2737) (p 2751) (p 2753) (p 2774) (p 2779) (p 2786) (p 2797) (p 2807) (p 2829) (p 2850) (p 2881) (p 2891) (p 2901) (p 2911) (p 2946) (p 2992) (p 3005) (p 3016) (p 3019) (p 3093) (p 3136) (p 3146) (p 3166) (p 3201) (p 3309) (p 3379) (p 3399) (p 3422) (p 3547) (p 3569) (p 3571) (p 3580) (p 3660) (p 3819) (p 3873) (p 3879) (p 3948) (p 3953) (p 3960) (p 3987) (p 4031) (p 4117) (p 4210) (p 4282) (p 4337) (p 4338) (p 4401) (p 4419) (p 4431) (p 4434) (p 4489) (p 4518) (p 4558) (p 4700) (p 4752) (p 4753) (p 4790) (p 4814) (p 4845) (p 4969) (p 4972) (p 5008) (p 5086) (p 5087) (derived105367 p h) (derived105514 p h) (derived105365 p h) (derived105434 p h) (derived105469 p h) (derived106513 p h) (derived106424 p h) (derived106343 p h) (derived105400 p h) (derived106113 p h) (derived105390 p h) (derived105440 p h) (derived106144 p h) (derived105373 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101769 p h) (derived103124 p h) (derived105882 p h) (derived106635 p h) (derived68861 p h) (derived100753 p h) (derived95979 p h) (derived103475 p h) (derived91068 p h) (derived104473 p h) (derived103792 p h) (derived81200 p h) (derived96406 p h) (derived90544 p h) (derived96911 p h) (derived101098 p h) (derived90469 p h) (derived90912 p h) (derived96428 p h) (derived82744 p h) (derived96374 p h) (derived93634 p h) (derived106315 p h) (derived96975 p h) (derived100245 p h) (derived104436 p h) (derived96429 p h) (derived96408 p h) (derived96286 p h) (derived96449 p h) (h 11044) (derived96448 p h) (derived106414 p h) (derived100365 p h) (derived82296 p h) (derived96339 p h) (derived102873 p h) (derived106486 p h) (derived96016 p h) (derived100363 p h) (derived96969 p h) (h 17508) (derived106646 p h) (derived102335 p h) (derived66940 p h) (derived69917 p h) (h 6564) (derived83857 p h) (h 30182) (h 36523) (derived96304 p h) (derived96305 p h) (derived82329 p h) (derived97247 p h) (derived102333 p h) (derived98028 p h) (derived50095 p h) (derived98023 p h) (derived93347 p h) (derived79993 p h) (derived82395 p h) (derived78329 p h) (derived104425 p h) (h 6755) (derived102260 p h) (derived96934 p h) (derived106647 p h) (derived106604 p h) (derived103290 p h) (derived76001 p h) (derived78546 p h) (derived91680 p h) (derived89806 p h) (derived101940 p h) (derived87445 p h) (derived106602 p h) (derived96954 p h) (derived106603 p h) (derived106598 p h) (derived106599 p h) (derived78503 p h) (derived101604 p h)

theorem derived106649 (p : Nat → Prop) (h : Inputs p) :
    (p 2608) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106649 (p 2122) (p 2177) (p 2230) (p 2241) (p 2246) (p 2248) (p 2255) (p 2274) (p 2295) (p 2298) (p 2307) (p 2312) (p 2331) (p 2341) (p 2373) (p 2386) (p 2406) (p 2427) (p 2437) (p 2440) (p 2459) (p 2470) (p 2481) (p 2493) (p 2505) (p 2507) (p 2509) (p 2518) (p 2531) (p 2553) (p 2563) (p 2573) (p 2598) (p 2608) (p 2630) (p 2651) (p 2656) (p 2663) (p 2667) (p 2685) (p 2696) (p 2707) (p 2727) (p 2737) (p 2753) (p 2774) (p 2779) (p 2786) (p 2797) (p 2807) (p 2829) (p 2850) (p 2881) (p 2911) (p 2922) (p 2933) (p 2946) (p 3005) (p 3016) (p 3019) (p 3093) (p 3136) (p 3146) (p 3166) (p 3201) (p 3309) (p 3379) (p 3389) (p 3399) (p 3422) (p 3547) (p 3569) (p 3571) (p 3580) (p 3759) (p 3819) (p 3873) (p 3921) (p 3953) (p 3958) (p 3960) (p 3987) (p 4104) (p 4117) (p 4203) (p 4204) (p 4210) (p 4279) (p 4337) (p 4401) (p 4475) (p 4555) (p 4595) (p 4683) (p 4686) (p 4752) (p 4761) (p 4790) (p 4814) (p 4845) (p 4969) (p 4972) (p 5008) (p 5015) (p 5087) (p 5225) (derived106424 p h) (derived105367 p h) (derived105469 p h) (derived105365 p h) (derived105434 p h) (derived106234 p h) (derived105495 p h) (derived105440 p h) (derived105542 p h) (derived105378 p h) (derived96286 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived96448 p h) (derived106414 p h) (derived101769 p h) (derived102873 p h) (derived100245 p h) (derived103124 p h) (derived96408 p h) (derived96406 p h) (derived103475 p h) (derived96428 p h) (derived91068 p h) (derived104436 p h) (derived104473 p h) (derived96975 p h) (derived106635 p h) (derived96374 p h) (derived106315 p h) (derived68861 p h) (derived90589 p h) (derived90469 p h) (derived90544 p h) (derived93634 p h) (derived103792 p h) (derived100753 p h) (derived96483 p h) (derived90912 p h) (derived96911 p h) (derived95391 p h) (derived81200 p h) (derived95979 p h) (derived82874 p h) (derived95983 p h) (derived106648 p h) (derived101806 p h) (derived78668 p h) (derived91570 p h) (derived102030 p h) (derived103846 p h) (derived85220 p h) (derived101858 p h) (derived91057 p h) (derived90585 p h) (derived87416 p h) (derived90314 p h) (derived93816 p h) (derived100754 p h) (derived96943 p h) (derived96946 p h) (derived96935 p h) (derived106296 p h) (derived88066 p h) (h 11042) (derived85209 p h) (derived85233 p h) (derived85328 p h) (derived96281 p h) (h 6623) (h 7550) (derived96902 p h) (derived101604 p h) (derived104924 p h) (derived101272 p h) (derived87562 p h) (derived96305 p h) (derived66365 p h) (derived82329 p h) (derived87285 p h) (derived102335 p h) (derived106647 p h) (h 7556) (derived50095 p h) (h 5198) (derived78936 p h) (derived100361 p h) (derived81419 p h) (derived82395 p h) (derived90300 p h) (derived101940 p h) (derived96954 p h) (derived106593 p h) (derived87540 p h) (derived106603 p h) (derived89806 p h) (derived106602 p h)

theorem derived106650 (p : Nat → Prop) (h : Inputs p) :
    (p 2307) ∨ (¬ p 2608) ∨ (¬ p 3309) :=
  ElevenRUP.step106650 (p 2307) (p 2608) (p 3093) (p 3204) (p 3309) (p 4866) (p 5015) (derived106063 p h) (h 33892) (derived85272 p h) (derived101909 p h) (derived95391 p h)

theorem derived106651 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (¬ p 5373) ∨ (¬ p 2373) ∨ (¬ p 4210) ∨ (¬ p 2437) ∨ (p 2274) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106651 (p 2088) (p 2098) (p 2156) (p 2177) (p 2230) (p 2241) (p 2246) (p 2249) (p 2255) (p 2274) (p 2284) (p 2307) (p 2319) (p 2331) (p 2341) (p 2373) (p 2427) (p 2437) (p 2440) (p 2459) (p 2470) (p 2481) (p 2531) (p 2563) (p 2608) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2667) (p 2696) (p 2727) (p 2737) (p 2742) (p 2744) (p 2751) (p 2786) (p 2860) (p 2870) (p 2881) (p 2901) (p 2946) (p 2992) (p 3005) (p 3051) (p 3083) (p 3093) (p 3136) (p 3146) (p 3166) (p 3178) (p 3189) (p 3201) (p 3256) (p 3309) (p 3399) (p 3527) (p 3569) (p 3589) (p 3879) (p 3960) (p 3987) (p 4031) (p 4117) (p 4204) (p 4210) (p 4275) (p 4399) (p 4401) (p 4434) (p 4489) (p 4518) (p 4632) (p 4700) (p 4702) (p 4759) (p 4790) (p 4793) (p 4845) (p 4902) (p 4969) (p 4972) (p 5008) (p 5087) (p 5373) (derived106079 p h) (derived106343 p h) (derived106513 p h) (derived106424 p h) (derived105367 p h) (derived105469 p h) (derived106257 p h) (derived105373 p h) (derived105390 p h) (derived105438 p h) (derived106144 p h) (derived106113 p h) (derived106503 p h) (derived105456 p h) (derived87445 p h) (derived96954 p h) (derived101940 p h) (derived106649 p h) (derived106650 p h) (derived96969 p h) (derived96017 p h) (derived90849 p h) (derived96016 p h) (derived103380 p h) (h 23019) (derived85162 p h) (derived75069 p h) (derived82329 p h) (derived50095 p h) (derived100361 p h) (derived78300 p h) (derived78546 p h) (derived104279 p h) (derived89806 p h) (derived100363 p h) (derived75062 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101769 p h) (derived100365 p h) (derived100245 p h) (derived82296 p h) (derived85927 p h) (derived102873 p h) (derived103124 p h) (derived98067 p h) (derived84402 p h) (derived95979 p h) (derived42955 p h) (derived96922 p h) (derived69917 p h) (derived96305 p h) (derived78198 p h) (derived68388 p h) (h 6407) (derived102210 p h) (derived85906 p h) (derived96022 p h) (derived99814 p h) (derived105882 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived96448 p h) (derived106414 p h) (derived96873 p h) (derived80454 p h) (derived103290 p h) (derived81772 p h) (derived96975 p h) (derived106602 p h) (derived76302 p h) (derived76348 p h) (derived76378 p h) (derived76915 p h) (derived76794 p h) (derived100716 p h)

theorem derived106652 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (¬ p 2850) ∨ (¬ p 2437) ∨ (p 2274) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106652 (p 2156) (p 2166) (p 2192) (p 2230) (p 2241) (p 2255) (p 2274) (p 2284) (p 2331) (p 2373) (p 2406) (p 2437) (p 2440) (p 2493) (p 2505) (p 2563) (p 2573) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2727) (p 2797) (p 2807) (p 2850) (p 2901) (p 2946) (p 2992) (p 2995) (p 2996) (p 3051) (p 3093) (p 3136) (p 3309) (p 3379) (p 3579) (p 3641) (p 3660) (p 3819) (p 3879) (p 3948) (p 3987) (p 4031) (p 4104) (p 4117) (p 4210) (p 4275) (p 4281) (p 4282) (p 4336) (p 4338) (p 4355) (p 4518) (p 4555) (p 4632) (p 4700) (p 4702) (p 4790) (p 4814) (p 4972) (p 5373) (derived106079 p h) (derived105542 p h) (derived106113 p h) (derived105367 p h) (derived106424 p h) (derived106257 p h) (derived105373 p h) (derived105440 p h) (derived100363 p h) (derived103380 p h) (derived75062 p h) (derived79172 p h) (h 5209) (derived87995 p h) (derived102873 p h) (derived103124 p h) (derived98067 p h) (derived84339 p h) (derived102554 p h) (derived100365 p h) (derived100245 p h) (derived82296 p h) (derived90849 p h) (derived96016 p h) (h 23019) (derived85162 p h) (derived78198 p h) (derived85984 p h) (h 4117) (derived98897 p h) (derived93816 p h) (h 11042) (derived96339 p h) (derived79993 p h) (derived102260 p h) (derived76001 p h) (derived93347 p h) (derived87393 p h) (derived85906 p h) (derived105882 p h) (derived96927 p h) (derived101098 p h) (derived96449 p h) (derived95899 p h) (derived96428 p h) (derived96429 p h) (derived91680 p h) (derived79142 p h) (derived90965 p h) (derived87779 p h) (derived96943 p h) (derived96246 p h) (derived106651 p h) (derived85301 p h) (h 6473) (derived106574 p h)

theorem derived106653 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 2437) ∨ (p 2274) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106653 (p 2156) (p 2230) (p 2241) (p 2255) (p 2274) (p 2307) (p 2406) (p 2427) (p 2437) (p 2440) (p 2493) (p 2505) (p 2553) (p 2563) (p 2573) (p 2584) (p 2608) (p 2641) (p 2665) (p 2727) (p 2744) (p 2850) (p 2992) (p 3051) (p 3309) (p 3367) (p 3379) (p 3519) (p 3660) (p 3879) (p 4031) (p 4079) (p 4117) (p 4257) (p 4275) (p 4399) (p 4518) (p 4632) (p 4702) (p 5194) (derived106079 p h) (derived105367 p h) (derived106257 p h) (derived106113 p h) (derived105373 p h) (derived106503 p h) (derived105489 p h) (derived96017 p h) (derived90849 p h) (derived96016 p h) (derived103380 p h) (h 23019) (derived85162 p h) (derived75069 p h) (derived93347 p h) (derived87393 p h) (derived96934 p h) (derived100365 p h) (derived100245 p h) (derived82296 p h) (derived85906 p h) (derived106649 p h) (derived106650 p h) (derived48328 p h) (derived90608 p h) (derived106652 p h) (derived76848 p h) (derived91518 p h) (derived87993 p h) (derived85266 p h) (derived104196 p h) (derived96943 p h) (derived103895 p h) (derived78518 p h)

theorem derived106654 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (p 2274) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106654 (p 2156) (p 2166) (p 2192) (p 2220) (p 2230) (p 2255) (p 2274) (p 2307) (p 2373) (p 2427) (p 2437) (p 2440) (p 2563) (p 2598) (p 2608) (p 2619) (p 2630) (p 2665) (p 2696) (p 2727) (p 2737) (p 2839) (p 2850) (p 2881) (p 2962) (p 2992) (p 3051) (p 3054) (p 3309) (p 3362) (p 3569) (p 3589) (p 3698) (p 3759) (p 3879) (p 3988) (p 4031) (p 4117) (p 4119) (p 4204) (p 4275) (p 4282) (p 4338) (p 4399) (p 4518) (p 4632) (p 4700) (p 4730) (p 4752) (p 4790) (derived106424 p h) (derived106113 p h) (derived106257 p h) (derived105367 p h) (derived105373 p h) (derived105434 p h) (derived106074 p h) (derived100363 p h) (derived100365 p h) (derived100245 p h) (derived82296 p h) (derived96339 p h) (derived103380 p h) (derived79993 p h) (derived102260 p h) (derived76001 p h) (derived96016 p h) (h 23019) (derived98522 p h) (derived106649 p h) (derived106650 p h) (derived92445 p h) (derived96017 p h) (derived90849 p h) (derived85162 p h) (derived75069 p h) (derived82329 p h) (derived100361 p h) (derived99814 p h) (derived103124 p h) (derived42955 p h) (derived50095 p h) (derived87258 p h) (h 35121) (derived106653 p h) (derived102320 p h) (derived102190 p h) (h 5511) (derived81200 p h) (derived77779 p h) (derived84764 p h) (derived95983 p h) (derived83766 p h) (derived101922 p h) (derived102856 p h)

theorem derived106655 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (¬ p 2860) ∨ (¬ p 2284) ∨ (¬ p 2608) ∨ (¬ p 2992) ∨ (¬ p 2630) ∨ (¬ p 2230) :=
  ElevenRUP.step106655 (p 2230) (p 2241) (p 2284) (p 2598) (p 2608) (p 2630) (p 2696) (p 2737) (p 2839) (p 2850) (p 2860) (p 2992) (p 3136) (p 3362) (p 3589) (p 3698) (p 3759) (p 4730) (p 4752) (derived105434 p h) (derived106074 p h) (derived99814 p h) (derived102190 p h) (h 5511) (derived81200 p h) (derived95983 p h) (derived102891 p h) (derived101922 p h) (derived87107 p h) (derived102856 p h) (derived44740 p h) (derived83710 p h)

theorem derived106657 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 4969) ∨ (p 2437) ∨ (¬ p 5312) ∨ (¬ p 2427) ∨ (¬ p 2166) ∨ (¬ p 2641) ∨ (¬ p 2284) ∨ (p 2274) ∨ (¬ p 2608) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 3166) ∨ (¬ p 2331) ∨ (¬ p 2946) ∨ (¬ p 2230) :=
  ElevenRUP.step106657 (p 2088) (p 2098) (p 2156) (p 2166) (p 2187) (p 2230) (p 2241) (p 2246) (p 2274) (p 2284) (p 2295) (p 2307) (p 2331) (p 2373) (p 2396) (p 2427) (p 2437) (p 2459) (p 2553) (p 2563) (p 2573) (p 2584) (p 2608) (p 2641) (p 2665) (p 2744) (p 2807) (p 2881) (p 2911) (p 2946) (p 3016) (p 3051) (p 3073) (p 3093) (p 3146) (p 3156) (p 3166) (p 3178) (p 3256) (p 3309) (p 3399) (p 3449) (p 3527) (p 3537) (p 3544) (p 3589) (p 3631) (p 3660) (p 4031) (p 4117) (p 4275) (p 4336) (p 4416) (p 4452) (p 4518) (p 4555) (p 4632) (p 4668) (p 4669) (p 4718) (p 4902) (p 4969) (p 4973) (p 5312) (p 5316) (derived105542 p h) (derived106257 p h) (derived105373 p h) (derived105425 p h) (derived105835 p h) (derived105414 p h) (derived106113 p h) (derived105415 p h) (derived106503 p h) (derived105456 p h) (derived103380 p h) (derived93347 p h) (derived87393 p h) (derived96934 p h) (derived90849 p h) (derived96016 p h) (h 23019) (derived85162 p h) (derived98897 p h) (derived79172 p h) (derived106650 p h) (derived99814 p h) (derived96287 p h) (derived96873 p h) (derived104611 p h) (derived78503 p h) (derived79289 p h) (derived79409 p h) (derived79005 p h) (derived96975 p h) (derived85301 p h) (derived79039 p h) (derived103290 p h) (derived104446 p h) (derived95934 p h) (derived91631 p h) (derived96265 p h) (derived93161 p h) (derived106637 p h) (derived104091 p h) (derived85109 p h) (derived102269 p h) (derived76308 p h) (derived76302 p h) (derived89328 p h) (derived99036 p h) (derived76401 p h) (derived96209 p h) (derived76378 p h) (derived100716 p h)

theorem derived106658 (p : Nat → Prop) (h : Inputs p) :
    (p 2274) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106658 (p 2156) (p 2166) (p 2192) (p 2230) (p 2255) (p 2274) (p 2284) (p 2307) (p 2331) (p 2427) (p 2437) (p 2440) (p 2553) (p 2563) (p 2586) (p 2608) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2727) (p 2737) (p 2744) (p 2751) (p 2850) (p 2860) (p 2870) (p 2901) (p 2946) (p 2992) (p 3005) (p 3016) (p 3051) (p 3166) (p 3189) (p 3309) (p 3367) (p 3475) (p 3859) (p 3879) (p 3921) (p 4031) (p 4117) (p 4204) (p 4275) (p 4282) (p 4338) (p 4399) (p 4518) (p 4632) (p 4700) (p 4702) (p 4790) (p 4969) (p 4972) (p 5008) (p 5312) (derived106424 p h) (derived105367 p h) (derived105469 p h) (derived106257 p h) (derived106079 p h) (derived106113 p h) (derived105373 p h) (derived106503 p h) (derived106343 p h) (derived105372 p h) (derived106649 p h) (derived106650 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101769 p h) (derived105882 p h) (derived101098 p h) (derived100365 p h) (derived100245 p h) (derived82296 p h) (derived96339 p h) (derived102873 p h) (derived103124 p h) (derived96403 p h) (derived96017 p h) (derived96016 p h) (derived100363 p h) (derived90849 p h) (derived100361 p h) (derived103380 p h) (derived79993 p h) (derived75062 p h) (h 23019) (derived85906 p h) (derived102260 p h) (derived85927 p h) (derived85162 p h) (derived76001 p h) (derived96307 p h) (derived78198 p h) (derived75069 p h) (h 35299) (derived68388 p h) (h 6407) (derived106654 p h) (derived106655 p h) (derived48328 p h) (derived82950 p h) (derived100753 p h) (derived95979 p h) (derived106657 p h) (derived76963 p h) (derived75161 p h) (derived101858 p h)

theorem derived106659 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106659 (p 2098) (p 2132) (p 2156) (p 2177) (p 2187) (p 2230) (p 2241) (p 2245) (p 2255) (p 2264) (p 2274) (p 2284) (p 2307) (p 2319) (p 2331) (p 2352) (p 2383) (p 2386) (p 2406) (p 2427) (p 2437) (p 2440) (p 2493) (p 2504) (p 2505) (p 2563) (p 2573) (p 2584) (p 2608) (p 2651) (p 2656) (p 2663) (p 2665) (p 2696) (p 2707) (p 2717) (p 2727) (p 2737) (p 2742) (p 2744) (p 2774) (p 2779) (p 2786) (p 2807) (p 2829) (p 2850) (p 2881) (p 2911) (p 2922) (p 2933) (p 2934) (p 2946) (p 2957) (p 2992) (p 3016) (p 3063) (p 3093) (p 3309) (p 3362) (p 3366) (p 3367) (p 3379) (p 3389) (p 3399) (p 3422) (p 3425) (p 3519) (p 3527) (p 3547) (p 3589) (p 3660) (p 3741) (p 3819) (p 3872) (p 3873) (p 3879) (p 3923) (p 3987) (p 4079) (p 4112) (p 4117) (p 4133) (p 4203) (p 4376) (p 4424) (p 4555) (p 4752) (p 4753) (p 4782) (p 4804) (p 4807) (p 4814) (p 4898) (p 4972) (p 4992) (p 4996) (p 5052) (derived105367 p h) (derived105542 p h) (derived105473 p h) (derived105434 p h) (derived105514 p h) (derived106320 p h) (derived106503 p h) (derived105712 p h) (derived105440 p h) (derived105373 p h) (derived105455 p h) (derived106658 p h) (derived95964 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived106649 p h) (derived106650 p h) (derived96969 p h) (h 17508) (derived99814 p h) (derived87229 p h) (derived96286 p h) (derived102873 p h) (derived96894 p h) (derived100365 p h) (derived100245 p h) (derived82296 p h) (derived98897 p h) (h 6478) (derived83077 p h) (derived43275 p h) (derived42933 p h) (derived105098 p h) (derived105525 p h) (derived104425 p h) (derived87285 p h) (derived93347 p h) (h 5739) (derived78048 p h) (derived96976 p h) (derived104424 p h) (derived97347 p h) (derived81200 p h) (derived82531 p h) (derived96934 p h) (derived96935 p h) (derived53072 p h) (derived88131 p h) (h 27689) (derived87385 p h) (h 6755) (derived96922 p h) (derived102848 p h) (derived87271 p h) (h 23801) (derived97344 p h) (derived90472 p h) (derived87993 p h) (derived96390 p h) (derived88381 p h) (derived96911 p h) (derived91518 p h) (derived79669 p h) (derived76848 p h) (derived76856 p h) (derived96944 p h) (derived96943 p h) (derived106647 p h) (derived96902 p h) (derived96899 p h) (derived87318 p h) (derived96077 p h) (derived95506 p h) (derived76812 p h) (h 8334) (derived66420 p h) (h 8340) (derived83573 p h) (derived83960 p h) (derived74841 p h) (derived85918 p h) (derived76260 p h) (derived93490 p h) (derived74852 p h) (derived77952 p h) (derived77955 p h) (derived93166 p h) (derived100709 p h)

theorem derived106660 (p : Nat → Prop) (h : Inputs p) :
    (p 3093) ∨ (p 2098) ∨ (¬ p 3961) ∨ (p 3527) ∨ (p 2241) ∨ (¬ p 4424) ∨ (p 2860) ∨ (¬ p 3422) ∨ (¬ p 4969) ∨ (¬ p 4341) ∨ (¬ p 5312) ∨ (¬ p 2352) ∨ (¬ p 3587) ∨ (¬ p 2891) ∨ (¬ p 2573) ∨ (¬ p 2901) ∨ (p 3016) ∨ (p 2192) ∨ (¬ p 2608) ∨ (¬ p 4117) ∨ (¬ p 3178) ∨ (¬ p 2331) ∨ (¬ p 2946) :=
  ElevenRUP.step106660 (p 2088) (p 2098) (p 2192) (p 2210) (p 2241) (p 2246) (p 2331) (p 2352) (p 2363) (p 2459) (p 2493) (p 2573) (p 2608) (p 2744) (p 2860) (p 2891) (p 2901) (p 2946) (p 3016) (p 3073) (p 3093) (p 3178) (p 3246) (p 3256) (p 3379) (p 3399) (p 3422) (p 3434) (p 3519) (p 3527) (p 3544) (p 3587) (p 3957) (p 3961) (p 4117) (p 4133) (p 4341) (p 4376) (p 4416) (p 4424) (p 4558) (p 4668) (p 4669) (p 4969) (p 5206) (p 5214) (p 5312) (derived105492 p h) (derived105414 p h) (derived105400 p h) (derived105415 p h) (derived106320 p h) (derived106503 p h) (derived105712 p h) (derived102269 p h) (derived96975 p h) (derived96469 p h) (derived80393 p h) (derived77684 p h) (derived79891 p h) (derived85769 p h) (derived95923 p h) (derived97373 p h) (derived76302 p h) (derived91518 p h) (h 24141) (derived83372 p h) (derived99036 p h) (derived76816 p h) (derived96209 p h) (derived82385 p h) (derived100716 p h)

theorem derived106661 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3379) ∨ (p 2241) ∨ (¬ p 4257) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106661 (p 2230) (p 2241) (p 2440) (p 2744) (p 3379) (p 4079) (p 4257) (derived106503 p h) (derived87993 p h) (derived104196 p h)

theorem derived106662 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 3093) ∨ (¬ p 3425) ∨ (p 2241) ∨ (¬ p 4424) ∨ (p 2860) ∨ (¬ p 3422) ∨ (¬ p 4969) ∨ (¬ p 4341) ∨ (¬ p 5312) ∨ (¬ p 2352) ∨ (¬ p 3587) ∨ (¬ p 4988) ∨ (¬ p 4283) ∨ (¬ p 2891) ∨ (¬ p 2573) ∨ (¬ p 2901) ∨ (p 2156) ∨ (p 3016) ∨ (p 2192) ∨ (¬ p 2608) ∨ (¬ p 4117) ∨ (¬ p 3178) ∨ (¬ p 2331) ∨ (¬ p 2946) :=
  ElevenRUP.step106662 (p 2098) (p 2156) (p 2192) (p 2241) (p 2331) (p 2341) (p 2352) (p 2573) (p 2608) (p 2717) (p 2860) (p 2881) (p 2891) (p 2901) (p 2946) (p 3016) (p 3093) (p 3178) (p 3422) (p 3425) (p 3527) (p 3587) (p 3685) (p 3961) (p 4117) (p 4283) (p 4341) (p 4424) (p 4431) (p 4558) (p 4969) (p 4988) (p 5312) (derived105400 p h) (derived97247 p h) (derived85470 p h) (derived79938 p h) (derived91609 p h) (derived83327 p h) (derived106660 p h) (derived97921 p h) (h 17796)

theorem derived106663 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (p 2707) ∨ (¬ p 4257) ∨ (p 2860) ∨ (¬ p 3422) ∨ (¬ p 2427) ∨ (¬ p 2807) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106663 (p 2098) (p 2156) (p 2187) (p 2192) (p 2210) (p 2230) (p 2241) (p 2245) (p 2255) (p 2274) (p 2284) (p 2331) (p 2352) (p 2383) (p 2427) (p 2440) (p 2563) (p 2573) (p 2584) (p 2608) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2707) (p 2717) (p 2727) (p 2744) (p 2751) (p 2797) (p 2807) (p 2860) (p 2870) (p 2881) (p 2891) (p 2901) (p 2946) (p 2992) (p 3005) (p 3016) (p 3051) (p 3093) (p 3096) (p 3125) (p 3166) (p 3178) (p 3189) (p 3309) (p 3323) (p 3379) (p 3422) (p 3425) (p 3537) (p 3587) (p 3589) (p 3859) (p 3873) (p 3879) (p 3958) (p 4031) (p 4117) (p 4140) (p 4153) (p 4194) (p 4198) (p 4257) (p 4282) (p 4283) (p 4341) (p 4389) (p 4399) (p 4424) (p 4533) (p 4558) (p 4620) (p 4632) (p 4700) (p 4790) (p 4806) (p 4814) (p 4882) (p 4969) (p 4972) (p 4988) (p 5008) (p 5312) (derived106343 p h) (derived105367 p h) (derived105400 p h) (derived106424 p h) (derived105373 p h) (derived105378 p h) (derived105469 p h) (derived105440 p h) (derived106257 p h) (derived105394 p h) (derived105453 p h) (derived106503 p h) (derived96390 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101769 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived101272 p h) (derived96024 p h) (derived103124 p h) (derived96409 p h) (derived87394 p h) (derived87037 p h) (derived95238 p h) (derived75063 p h) (derived106658 p h) (derived95963 p h) (derived105882 p h) (derived101098 p h) (derived106276 p h) (derived97996 p h) (derived97962 p h) (derived92246 p h) (derived95979 p h) (h 31254) (derived96017 p h) (derived75064 p h) (derived96481 p h) (derived96016 p h) (derived78008 p h) (derived95235 p h) (derived75065 p h) (derived96399 p h) (derived100365 p h) (derived100245 p h) (derived82296 p h) (derived85926 p h) (derived96307 p h) (h 35299) (derived96934 p h) (derived83960 p h) (derived68388 p h) (derived102334 p h) (h 19331) (derived102490 p h) (derived102419 p h) (derived96339 p h) (h 36523) (derived103122 p h) (derived106649 p h) (derived99814 p h) (derived96873 p h) (derived102873 p h) (derived96976 p h) (derived88381 p h) (h 27689) (derived106661 p h) (derived103179 p h) (derived103381 p h) (derived106662 p h) (derived104103 p h) (derived106637 p h) (derived77954 p h) (derived93161 p h) (derived56542 p h)

theorem derived106664 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2850) ∨ (¬ p 2427) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106664 (p 2098) (p 2156) (p 2177) (p 2187) (p 2230) (p 2241) (p 2255) (p 2274) (p 2284) (p 2295) (p 2331) (p 2341) (p 2352) (p 2363) (p 2383) (p 2427) (p 2437) (p 2440) (p 2459) (p 2510) (p 2528) (p 2563) (p 2573) (p 2584) (p 2598) (p 2608) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2696) (p 2707) (p 2717) (p 2727) (p 2751) (p 2797) (p 2807) (p 2819) (p 2850) (p 2860) (p 2870) (p 2881) (p 2901) (p 2911) (p 2992) (p 3016) (p 3051) (p 3083) (p 3096) (p 3125) (p 3166) (p 3189) (p 3201) (p 3256) (p 3309) (p 3323) (p 3367) (p 3422) (p 3425) (p 3449) (p 3582) (p 3587) (p 3609) (p 3658) (p 3685) (p 3741) (p 3745) (p 3859) (p 3878) (p 3879) (p 3958) (p 4031) (p 4117) (p 4133) (p 4140) (p 4153) (p 4186) (p 4194) (p 4198) (p 4257) (p 4283) (p 4328) (p 4330) (p 4375) (p 4389) (p 4399) (p 4558) (p 4564) (p 4620) (p 4650) (p 4700) (p 4736) (p 4753) (p 4790) (p 4861) (p 4972) (p 4988) (p 5008) (derived105401 p h) (derived106343 p h) (derived105367 p h) (derived105469 p h) (derived106424 p h) (derived105373 p h) (derived105378 p h) (derived105400 p h) (derived106329 p h) (derived105431 p h) (derived105712 p h) (derived105514 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived101272 p h) (derived96024 p h) (derived103124 p h) (derived96409 p h) (derived87394 p h) (derived87037 p h) (derived96382 p h) (derived95238 p h) (h 31254) (derived96017 p h) (derived75064 p h) (derived96481 p h) (derived96016 p h) (derived106658 p h) (derived95963 p h) (derived78008 p h) (derived95235 p h) (derived75065 p h) (h 23561) (derived96379 p h) (derived96934 p h) (derived83960 p h) (derived96441 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101769 p h) (derived100365 p h) (derived100245 p h) (derived82296 p h) (derived75063 p h) (derived85926 p h) (derived96307 p h) (derived68388 p h) (derived102334 p h) (derived105882 p h) (derived101098 p h) (derived106276 p h) (derived97996 p h) (derived97962 p h) (h 19331) (derived102490 p h) (derived102419 p h) (derived95237 p h) (derived85941 p h) (derived97976 p h) (derived88131 p h) (derived96078 p h) (derived95141 p h) (derived106649 p h) (derived96367 p h) (derived48328 p h) (derived87796 p h) (h 6803) (derived81596 p h) (derived90608 p h) (derived96275 p h) (derived96302 p h) (derived76158 p h) (derived106663 p h) (derived45857 p h) (derived80612 p h) (derived43081 p h) (derived45324 p h) (derived104100 p h) (derived85470 p h) (derived102948 p h) (derived104829 p h) (derived91169 p h) (derived83327 p h) (derived77195 p h) (derived97015 p h) (derived97921 p h) (derived76147 p h) (derived93398 p h) (h 17796) (derived88615 p h) (derived75834 p h) (derived95243 p h) (derived74990 p h)

theorem derived106665 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2427) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106665 (p 2156) (p 2230) (p 2274) (p 2284) (p 2295) (p 2427) (p 2437) (p 2440) (p 2563) (p 2573) (p 2590) (p 2598) (p 2608) (p 2630) (p 2665) (p 2696) (p 2737) (p 2797) (p 2829) (p 2850) (p 3016) (p 3096) (p 3201) (p 3309) (p 3362) (p 3367) (p 3389) (p 3422) (p 3569) (p 3589) (p 3741) (p 3958) (p 4031) (p 4117) (p 4140) (p 4328) (p 4342) (p 4389) (p 4399) (p 4558) (p 4564) (p 4700) (p 4730) (p 4752) (p 4790) (derived106424 p h) (derived105378 p h) (derived105401 p h) (derived105373 p h) (derived105434 p h) (derived105400 p h) (derived106074 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived101272 p h) (derived96024 p h) (derived96017 p h) (derived75064 p h) (derived96409 p h) (derived96410 p h) (derived106658 p h) (derived95963 p h) (derived106649 p h) (derived99814 p h) (derived103124 p h) (derived96016 p h) (derived82329 p h) (derived88131 p h) (derived97976 p h) (derived87394 p h) (derived87271 p h) (derived87037 p h) (derived96382 p h) (derived42979 p h) (derived106664 p h) (derived81200 p h) (derived81039 p h) (derived77085 p h) (h 18663) (derived87134 p h) (derived101922 p h) (derived88468 p h) (derived102352 p h) (derived90444 p h)

theorem derived106666 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (¬ p 3367) ∨ (¬ p 4342) ∨ (¬ p 2696) ∨ (p 3016) ∨ (¬ p 2307) ∨ (¬ p 2608) ∨ (¬ p 2630) :=
  ElevenRUP.step106666 (p 2295) (p 2307) (p 2573) (p 2608) (p 2630) (p 2665) (p 2696) (p 2737) (p 2797) (p 2829) (p 3016) (p 3367) (p 3589) (p 4328) (p 4342) (p 4389) (p 4730) (derived105373 p h) (derived106074 p h) (derived96024 p h) (derived99814 p h) (derived104611 p h) (derived87037 p h) (derived90444 p h) (derived96382 p h) (derived42979 p h) (derived87134 p h)

theorem derived106668 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (¬ p 5284) ∨ (p 2417) ∨ (¬ p 4349) ∨ (p 2363) ∨ (p 2406) ∨ (p 3051) ∨ (p 2427) ∨ (p 2437) ∨ (¬ p 4031) ∨ (¬ p 2440) :=
  ElevenRUP.step106668 (p 2363) (p 2406) (p 2417) (p 2427) (p 2437) (p 2440) (p 2459) (p 2761) (p 2881) (p 3051) (p 3146) (p 3246) (p 3266) (p 3945) (p 4031) (p 4119) (p 4133) (p 4349) (p 5063) (p 5284) (derived105474 p h) (derived105712 p h) (derived87258 p h) (derived74491 p h) (derived78061 p h) (derived92417 p h) (derived92863 p h) (derived92817 p h) (derived50141 p h) (derived79611 p h)

theorem derived106669 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (¬ p 4349) ∨ (p 2363) ∨ (¬ p 3842) ∨ (p 2829) ∨ (¬ p 2797) ∨ (p 2737) ∨ (¬ p 2295) ∨ (¬ p 3654) ∨ (p 2573) ∨ (¬ p 5020) ∨ (¬ p 2774) ∨ (¬ p 3367) ∨ (¬ p 2241) ∨ (p 3201) ∨ (¬ p 2696) ∨ (p 3051) ∨ (p 2427) ∨ (p 2437) ∨ (¬ p 4031) ∨ (¬ p 2440) :=
  ElevenRUP.step106669 (p 2177) (p 2241) (p 2295) (p 2341) (p 2363) (p 2396) (p 2406) (p 2417) (p 2427) (p 2437) (p 2440) (p 2459) (p 2573) (p 2641) (p 2696) (p 2707) (p 2737) (p 2741) (p 2761) (p 2774) (p 2797) (p 2829) (p 2881) (p 2911) (p 3051) (p 3146) (p 3201) (p 3246) (p 3266) (p 3323) (p 3367) (p 3389) (p 3434) (p 3461) (p 3483) (p 3506) (p 3541) (p 3654) (p 3657) (p 3842) (p 3917) (p 4025) (p 4031) (p 4042) (p 4106) (p 4279) (p 4349) (p 4559) (p 4621) (p 4730) (p 4752) (p 4984) (p 5020) (p 5210) (p 5263) (p 5268) (p 5281) (p 5284) (p 5287) (derived105434 p h) (derived106074 p h) (derived105407 p h) (derived105701 p h) (derived96923 p h) (derived92232 p h) (derived42760 p h) (derived91157 p h) (derived43497 p h) (derived99791 p h) (derived81741 p h) (derived97816 p h) (derived96335 p h) (derived95654 p h) (derived96281 p h) (derived77747 p h) (derived74687 p h) (derived81303 p h) (derived101874 p h) (derived89683 p h) (derived74696 p h) (h 8962) (derived66454 p h) (h 8968) (derived79279 p h) (derived59407 p h) (derived94382 p h) (h 9008) (derived66456 p h) (h 9002) (derived106668 p h) (derived96358 p h) (derived100874 p h) (derived103030 p h) (derived104050 p h) (derived79616 p h) (derived82464 p h) (derived96417 p h) (derived81898 p h)

theorem derived106670 (p : Nat → Prop) (h : Inputs p) :
    (p 2737) ∨ (¬ p 2295) ∨ (p 2573) ∨ (¬ p 2774) ∨ (¬ p 3367) ∨ (¬ p 2241) ∨ (p 2850) ∨ (p 2427) ∨ (p 2437) ∨ (¬ p 3096) ∨ (¬ p 3589) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106670 (p 2177) (p 2187) (p 2230) (p 2241) (p 2253) (p 2264) (p 2295) (p 2331) (p 2352) (p 2363) (p 2373) (p 2396) (p 2406) (p 2427) (p 2437) (p 2440) (p 2441) (p 2470) (p 2573) (p 2577) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2696) (p 2737) (p 2741) (p 2742) (p 2774) (p 2797) (p 2819) (p 2829) (p 2850) (p 2881) (p 2911) (p 2982) (p 3051) (p 3096) (p 3146) (p 3166) (p 3189) (p 3201) (p 3237) (p 3256) (p 3286) (p 3343) (p 3367) (p 3389) (p 3541) (p 3564) (p 3589) (p 3654) (p 3683) (p 3693) (p 3842) (p 3845) (p 3848) (p 3852) (p 3987) (p 4001) (p 4031) (p 4156) (p 4327) (p 4328) (p 4349) (p 4399) (p 4404) (p 4426) (p 4509) (p 4559) (p 4715) (p 4752) (p 4790) (p 4972) (p 5008) (p 5020) (p 5046) (p 5172) (derived106424 p h) (derived105469 p h) (derived105373 p h) (derived105423 p h) (derived105392 p h) (derived105472 p h) (derived105434 p h) (derived105701 p h) (derived105381 p h) (derived96453 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived87403 p h) (derived96343 p h) (derived91402 p h) (derived96284 p h) (derived95146 p h) (derived87404 p h) (derived94352 p h) (derived87420 p h) (derived102520 p h) (derived87495 p h) (derived99791 p h) (derived105882 p h) (derived101098 p h) (derived96449 p h) (derived82153 p h) (h 31445) (derived95462 p h) (derived75827 p h) (derived81200 p h) (derived96017 p h) (derived75069 p h) (derived95461 p h) (derived101769 p h) (derived103124 p h) (derived96402 p h) (derived96016 p h) (derived96923 p h) (derived96922 p h) (derived104042 p h) (derived81312 p h) (derived81741 p h) (derived92232 p h) (derived96382 p h) (derived96383 p h) (derived43497 p h) (derived87406 p h) (derived42760 p h) (derived62016 p h) (derived90836 p h) (derived87134 p h) (derived87410 p h) (derived94414 p h) (derived90525 p h) (derived67255 p h) (derived86262 p h) (derived96789 p h) (derived45193 p h) (derived92012 p h) (derived102494 p h) (derived106669 p h) (derived104616 p h) (derived87447 p h) (derived104050 p h) (derived92936 p h) (derived87459 p h) (derived77508 p h)

theorem derived106671 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (p 2264) ∨ (¬ p 2122) ∨ (¬ p 2829) ∨ (¬ p 3693) ∨ (p 2850) ∨ (¬ p 4001) ∨ (¬ p 2608) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106671 (p 2122) (p 2177) (p 2230) (p 2264) (p 2363) (p 2396) (p 2440) (p 2470) (p 2608) (p 2819) (p 2829) (p 2850) (p 2881) (p 2911) (p 3146) (p 3389) (p 3693) (p 4001) (p 4138) (p 4327) (p 4404) (p 4559) (derived105381 p h) (derived105701 p h) (derived43080 p h) (derived87334 p h) (derived42876 p h) (derived87447 p h) (derived87421 p h) (derived92936 p h) (derived90368 p h) (derived77508 p h) (derived42665 p h) (derived87459 p h) (derived104050 p h)

theorem derived106672 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (p 2363) ∨ (p 2911) ∨ (¬ p 4279) ∨ (p 3461) ∨ (p 2396) ∨ (p 3201) ∨ (p 2437) :=
  ElevenRUP.step106672 (p 2341) (p 2363) (p 2396) (p 2437) (p 2459) (p 2761) (p 2881) (p 2911) (p 3146) (p 3201) (p 3246) (p 3266) (p 3461) (p 3657) (p 4025) (p 4042) (p 4279) (p 4559) (p 4730) (derived106074 p h) (derived105701 p h) (derived89683 p h) (derived91157 p h) (derived96358 p h) (derived100859 p h) (derived103030 p h) (derived104050 p h) (derived79616 p h) (derived82464 p h) (derived96417 p h) (derived81898 p h)

theorem derived106673 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (p 2850) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106673 (p 2088) (p 2122) (p 2177) (p 2187) (p 2230) (p 2241) (p 2255) (p 2264) (p 2274) (p 2284) (p 2295) (p 2307) (p 2331) (p 2352) (p 2363) (p 2373) (p 2383) (p 2396) (p 2406) (p 2417) (p 2427) (p 2437) (p 2440) (p 2441) (p 2459) (p 2553) (p 2563) (p 2573) (p 2577) (p 2590) (p 2598) (p 2608) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2696) (p 2707) (p 2717) (p 2727) (p 2737) (p 2761) (p 2774) (p 2797) (p 2807) (p 2819) (p 2829) (p 2850) (p 2860) (p 2870) (p 2881) (p 2911) (p 2982) (p 2992) (p 3005) (p 3016) (p 3051) (p 3093) (p 3096) (p 3136) (p 3146) (p 3166) (p 3180) (p 3201) (p 3237) (p 3246) (p 3256) (p 3266) (p 3286) (p 3297) (p 3309) (p 3322) (p 3323) (p 3343) (p 3362) (p 3367) (p 3389) (p 3422) (p 3426) (p 3434) (p 3461) (p 3483) (p 3537) (p 3564) (p 3589) (p 3609) (p 3654) (p 3670) (p 3693) (p 3755) (p 3872) (p 3879) (p 3917) (p 3945) (p 3958) (p 3987) (p 4001) (p 4031) (p 4117) (p 4119) (p 4133) (p 4279) (p 4281) (p 4342) (p 4399) (p 4456) (p 4509) (p 4650) (p 4700) (p 4710) (p 4711) (p 4715) (p 4752) (p 4753) (p 4790) (p 4802) (p 4841) (p 4889) (p 4972) (p 5008) (p 5046) (p 5063) (p 5107) (p 5172) (p 5221) (p 5263) (p 5268) (p 5338) (p 5339) (derived105469 p h) (derived105514 p h) (derived105367 p h) (derived105796 p h) (derived105423 p h) (derived105392 p h) (derived105434 p h) (derived105378 p h) (derived105373 p h) (derived105472 p h) (derived106424 p h) (derived105655 p h) (derived105712 p h) (derived105474 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived96409 p h) (derived103124 p h) (derived106649 p h) (derived106650 p h) (derived101272 p h) (derived81200 p h) (derived96410 p h) (h 18663) (derived102352 p h) (derived81039 p h) (derived101922 p h) (derived88478 p h) (derived106666 p h) (derived87403 p h) (derived96343 p h) (derived91402 p h) (derived96284 p h) (derived95146 p h) (derived96842 p h) (derived87404 p h) (derived94352 p h) (derived87416 p h) (derived94484 p h) (derived87420 p h) (derived102520 p h) (derived87495 p h) (derived86377 p h) (derived100365 p h) (derived100245 p h) (derived82296 p h) (derived99814 p h) (derived102891 p h) (derived87107 p h) (derived105882 p h) (derived80454 p h) (derived106665 p h) (derived95462 p h) (derived75827 p h) (derived106658 p h) (derived95964 p h) (derived96017 p h) (derived75069 p h) (derived92871 p h) (derived86611 p h) (derived95794 p h) (derived95461 p h) (derived96078 p h) (derived95141 p h) (derived101769 p h) (derived96874 p h) (derived101098 p h) (derived96449 p h) (derived95899 p h) (derived96016 p h) (derived106670 p h) (derived68861 p h) (derived42979 p h) (derived102194 p h) (derived101573 p h) (derived84404 p h) (derived59224 p h) (derived96484 p h) (derived42876 p h) (derived43080 p h) (h 8962) (derived88279 p h) (derived89193 p h) (derived66454 p h) (derived100923 p h) (derived97923 p h) (derived97060 p h) (h 8968) (derived43676 p h) (derived106671 p h) (derived96281 p h) (derived74717 p h) (derived74687 p h) (derived74768 p h) (derived74696 p h) (h 15402) (derived84981 p h) (derived102850 p h) (derived90280 p h) (derived42665 p h) (derived96437 p h) (derived74985 p h) (derived102524 p h) (derived102523 p h) (derived68607 p h) (derived102495 p h) (derived106672 p h) (derived87258 p h) (derived74491 p h) (derived78061 p h) (derived92417 p h) (derived92863 p h) (derived82478 p h) (derived87023 p h) (derived94247 p h) (derived79611 p h) (derived92817 p h) (derived93774 p h) (derived94974 p h) (derived94066 p h) (derived96689 p h) (derived102704 p h)

theorem derived106674 (p : Nat → Prop) (h : Inputs p) :
    (p 2850) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106674 (p 2177) (p 2230) (p 2241) (p 2255) (p 2284) (p 2295) (p 2307) (p 2363) (p 2383) (p 2437) (p 2440) (p 2459) (p 2470) (p 2528) (p 2553) (p 2563) (p 2573) (p 2590) (p 2598) (p 2608) (p 2630) (p 2665) (p 2668) (p 2696) (p 2727) (p 2850) (p 2911) (p 3016) (p 3093) (p 3309) (p 3325) (p 3362) (p 3367) (p 3389) (p 3422) (p 3589) (p 3875) (p 3920) (p 3958) (p 4117) (p 4153) (p 4194) (p 4342) (p 4700) (p 4710) (p 4752) (p 4790) (p 4972) (p 4973) (derived106424 p h) (derived105367 p h) (derived105378 p h) (derived105434 p h) (derived105373 p h) (derived105835 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived101272 p h) (derived96410 p h) (derived95238 p h) (h 31254) (derived106649 p h) (derived106650 p h) (derived99814 p h) (derived100245 p h) (derived103124 p h) (derived105882 p h) (derived81200 p h) (derived81039 p h) (h 18663) (derived102891 p h) (derived101922 p h) (derived102352 p h) (derived80454 p h) (derived88478 p h) (derived106666 p h) (derived87416 p h) (derived94484 p h) (derived94485 p h) (derived106673 p h) (derived85222 p h) (derived74725 p h) (derived87447 p h) (derived92937 p h) (derived75336 p h) (derived96473 p h) (derived42698 p h) (derived78280 p h) (derived85313 p h) (derived77535 p h) (derived79490 p h) (derived87461 p h)

theorem derived106675 (p : Nat → Prop) (h : Inputs p) :
    (p 2668) ∨ (¬ p 2383) ∨ (p 2363) ∨ (¬ p 3693) ∨ (p 2284) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106675 (p 2156) (p 2187) (p 2190) (p 2230) (p 2284) (p 2363) (p 2383) (p 2440) (p 2470) (p 2563) (p 2665) (p 2668) (p 3016) (p 3146) (p 3693) (p 3958) (p 4031) (p 4153) (p 4194) (p 4399) (p 4564) (p 4700) (p 4973) (derived105378 p h) (derived105401 p h) (derived105835 p h) (derived105373 p h) (derived96017 p h) (derived100363 p h) (derived75062 p h) (derived75064 p h) (derived96016 p h) (derived85437 p h) (derived93561 p h) (derived101272 p h) (derived95238 p h) (h 31254) (derived78783 p h) (derived77535 p h) (derived87459 p h)

theorem derived106676 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) ∨ (¬ p 2177) ∨ (¬ p 2668) ∨ (p 2573) ∨ (¬ p 2850) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106676 (p 2122) (p 2177) (p 2230) (p 2241) (p 2255) (p 2295) (p 2331) (p 2406) (p 2440) (p 2573) (p 2577) (p 2598) (p 2608) (p 2641) (p 2651) (p 2656) (p 2663) (p 2668) (p 2727) (p 2786) (p 2829) (p 2850) (p 3093) (p 3309) (p 3362) (p 3367) (p 3422) (p 3987) (p 4117) (p 4257) (p 4281) (p 4715) (p 4753) (p 4972) (p 5214) (p 5220) (derived105367 p h) (derived105514 p h) (derived105423 p h) (derived105492 p h) (derived77577 p h) (derived97817 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived102520 p h) (h 27723) (derived106649 p h) (derived100245 p h) (derived95899 p h) (derived85302 p h) (derived77749 p h) (derived43080 p h) (derived68719 p h) (derived90608 p h) (derived85222 p h) (derived43081 p h) (derived93774 p h) (derived102967 p h) (derived81070 p h)

theorem derived106677 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2668) ∨ (p 2573) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106677 (p 2166) (p 2177) (p 2192) (p 2210) (p 2230) (p 2241) (p 2246) (p 2255) (p 2284) (p 2295) (p 2307) (p 2331) (p 2373) (p 2406) (p 2437) (p 2440) (p 2563) (p 2573) (p 2577) (p 2608) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2727) (p 2744) (p 2786) (p 2850) (p 3093) (p 3096) (p 3309) (p 3362) (p 3379) (p 3589) (p 3987) (p 4079) (p 4117) (p 4509) (p 4700) (p 4813) (p 4814) (p 4905) (p 4972) (derived105367 p h) (derived105392 p h) (derived105373 p h) (derived105995 p h) (derived106503 p h) (derived105440 p h) (derived106649 p h) (derived99814 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived102520 p h) (h 27723) (h 23097) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived103122 p h) (derived96409 p h) (derived87404 p h) (derived80065 p h) (derived106674 p h) (derived106650 p h) (derived100245 p h) (derived95901 p h) (derived106676 p h) (derived80454 p h) (derived106634 p h) (derived96975 p h) (derived93844 p h) (derived80972 p h) (derived91131 p h) (derived103179 p h)

theorem derived106678 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 3389) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106678 (p 2177) (p 2230) (p 2255) (p 2284) (p 2307) (p 2363) (p 2373) (p 2383) (p 2427) (p 2437) (p 2440) (p 2459) (p 2470) (p 2518) (p 2528) (p 2553) (p 2563) (p 2573) (p 2577) (p 2608) (p 2665) (p 2668) (p 2727) (p 2881) (p 2911) (p 2922) (p 2930) (p 3096) (p 3309) (p 3389) (p 3527) (p 3693) (p 3920) (p 4001) (p 4117) (p 4281) (p 4370) (p 4404) (p 4509) (p 4559) (p 4683) (p 4686) (p 4700) (p 4712) (p 5307) (derived105367 p h) (derived105392 p h) (derived105373 p h) (derived105701 p h) (derived105376 p h) (derived105422 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived96409 p h) (derived106649 p h) (derived106650 p h) (derived103066 p h) (derived94485 p h) (h 5809) (derived87404 p h) (derived94352 p h) (derived102520 p h) (derived106665 p h) (derived95461 p h) (derived87421 p h) (derived100245 p h) (derived95899 p h) (derived87424 p h) (derived87454 p h) (derived103030 p h) (derived87415 p h) (derived92936 p h) (derived106675 p h) (derived106677 p h) (derived74502 p h) (derived81432 p h) (derived87461 p h) (h 7556) (derived77506 p h) (derived66365 p h) (derived96266 p h) (h 7549) (derived77503 p h)

theorem derived106679 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2668) ∨ (¬ p 2363) ∨ (p 2972) ∨ (¬ p 3362) ∨ (¬ p 2850) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106679 (p 2088) (p 2156) (p 2210) (p 2230) (p 2241) (p 2246) (p 2255) (p 2284) (p 2307) (p 2331) (p 2352) (p 2363) (p 2406) (p 2440) (p 2563) (p 2598) (p 2608) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2696) (p 2727) (p 2737) (p 2744) (p 2797) (p 2811) (p 2819) (p 2829) (p 2850) (p 2972) (p 2992) (p 3005) (p 3016) (p 3146) (p 3166) (p 3189) (p 3256) (p 3309) (p 3362) (p 3379) (p 3879) (p 3958) (p 4117) (p 4389) (p 4399) (p 4417) (p 4509) (p 4700) (p 4715) (p 4790) (p 4814) (p 4972) (p 5008) (p 5059) (p 5214) (derived106424 p h) (derived105367 p h) (derived105469 p h) (derived105378 p h) (derived105392 p h) (derived105373 p h) (derived105423 p h) (derived105492 p h) (derived106503 p h) (derived105440 p h) (derived96017 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived75064 p h) (derived106649 p h) (derived106650 p h) (derived104414 p h) (derived102934 p h) (derived96313 p h) (derived101272 p h) (derived96024 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101769 p h) (derived105882 p h) (derived101098 p h) (derived100365 p h) (derived100245 p h) (derived82296 p h) (derived103124 p h) (derived96398 p h) (derived78655 p h) (h 6804) (derived77762 p h) (derived42665 p h) (derived68861 p h) (derived100753 p h) (derived94054 p h) (derived45537 p h) (derived91165 p h) (derived100536 p h) (derived82874 p h) (derived91998 p h) (derived81070 p h) (derived45324 p h) (derived96975 p h) (derived91131 p h) (derived75484 p h) (derived103179 p h)

theorem derived106680 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (p 2668) ∨ (¬ p 4079) ∨ (p 3389) ∨ (p 2437) ∨ (¬ p 3819) ∨ (¬ p 2307) ∨ (¬ p 2608) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106680 (p 2230) (p 2241) (p 2255) (p 2295) (p 2307) (p 2331) (p 2352) (p 2383) (p 2396) (p 2406) (p 2417) (p 2437) (p 2440) (p 2449) (p 2493) (p 2497) (p 2553) (p 2573) (p 2577) (p 2598) (p 2608) (p 2651) (p 2656) (p 2663) (p 2668) (p 2727) (p 2744) (p 2922) (p 3093) (p 3367) (p 3379) (p 3389) (p 3516) (p 3589) (p 3819) (p 3905) (p 3920) (p 3987) (p 4079) (p 4156) (p 4281) (p 4327) (p 4644) (p 4715) (p 4752) (p 4813) (p 4972) (p 5197) (p 5201) (derived105367 p h) (derived105434 p h) (derived106503 p h) (derived105423 p h) (derived105411 p h) (derived105381 p h) (derived100245 p h) (derived95899 p h) (derived87424 p h) (derived103066 p h) (derived94485 p h) (derived80333 p h) (derived101912 p h) (h 5809) (derived102520 p h) (derived102519 p h) (derived99814 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived96449 p h) (derived95901 p h) (derived97347 p h) (derived81759 p h) (derived93844 p h) (derived91131 p h) (derived95981 p h) (derived79695 p h) (derived79658 p h) (derived88187 p h) (h 15909) (derived87491 p h) (derived87489 p h) (derived106634 p h) (derived95142 p h) (derived96453 p h) (derived84977 p h) (derived84975 p h)

theorem derived106681 (p : Nat → Prop) (h : Inputs p) :
    (p 2598) ∨ (¬ p 3527) ∨ (p 3389) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106681 (p 2098) (p 2132) (p 2192) (p 2220) (p 2230) (p 2241) (p 2255) (p 2264) (p 2284) (p 2307) (p 2319) (p 2331) (p 2341) (p 2363) (p 2373) (p 2427) (p 2437) (p 2440) (p 2553) (p 2563) (p 2573) (p 2577) (p 2598) (p 2608) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2685) (p 2696) (p 2717) (p 2727) (p 2786) (p 2807) (p 2850) (p 2870) (p 2972) (p 2982) (p 3051) (p 3093) (p 3096) (p 3212) (p 3309) (p 3362) (p 3366) (p 3367) (p 3389) (p 3399) (p 3425) (p 3475) (p 3527) (p 3546) (p 3589) (p 3819) (p 3920) (p 3987) (p 4031) (p 4032) (p 4079) (p 4117) (p 4136) (p 4399) (p 4452) (p 4509) (p 4650) (p 4700) (p 4715) (p 4753) (p 4782) (p 4783) (p 4790) (p 4793) (p 4807) (p 4814) (p 4972) (p 5046) (p 5089) (p 5092) (derived105514 p h) (derived106424 p h) (derived105392 p h) (derived105472 p h) (derived105423 p h) (derived105373 p h) (derived105440 p h) (derived105367 p h) (derived105438 p h) (derived106649 p h) (derived104279 p h) (derived96287 p h) (derived105882 p h) (derived100245 p h) (derived106650 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived96969 p h) (h 17508) (derived99814 p h) (derived103066 p h) (derived94485 p h) (h 5809) (derived102520 p h) (h 27723) (h 23097) (derived106674 p h) (derived96016 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived103122 p h) (derived96017 p h) (derived96409 p h) (derived87403 p h) (derived92102 p h) (h 8577) (derived66432 p h) (h 8571) (derived76702 p h) (derived106678 p h) (derived106679 p h) (derived106680 p h) (derived80454 p h) (derived92594 p h) (derived102388 p h) (derived87404 p h) (derived78956 p h) (derived96078 p h) (derived95141 p h) (derived103124 p h) (derived96403 p h) (derived82966 p h) (derived96397 p h) (derived106665 p h) (derived75069 p h) (derived92871 p h) (derived96363 p h) (derived105525 p h) (derived87229 p h) (derived82947 p h) (derived81017 p h) (derived104671 p h) (derived89905 p h) (derived94842 p h) (derived103315 p h) (derived77955 p h) (derived89912 p h) (derived100709 p h)

theorem derived106682 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2774) ∨ (¬ p 2742) ∨ (¬ p 3309) ∨ (¬ p 3093) ∨ (¬ p 2406) ∨ (¬ p 2440) ∨ (¬ p 3347) ∨ (p 2493) ∨ (p 2573) ∨ (¬ p 2274) ∨ (¬ p 2696) ∨ (¬ p 2911) ∨ (¬ p 2641) ∨ (¬ p 2230) ∨ (¬ p 4001) ∨ (¬ p 2122) :=
  ElevenRUP.step106682 (p 2122) (p 2230) (p 2274) (p 2406) (p 2440) (p 2493) (p 2573) (p 2641) (p 2696) (p 2742) (p 2774) (p 2797) (p 2911) (p 3093) (p 3309) (p 3347) (p 4001) (p 4564) (p 4644) (p 4712) (p 4715) (p 4973) (derived105423 p h) (derived105411 p h) (derived105422 p h) (derived105401 p h) (derived105835 p h) (derived104717 p h) (derived93905 p h)

theorem derived106683 (p : Nat → Prop) (h : Inputs p) :
    (p 3367) ∨ (¬ p 2598) ∨ (¬ p 2911) ∨ (¬ p 2641) ∨ (¬ p 2406) ∨ (¬ p 3347) ∨ (¬ p 3093) ∨ (p 2493) ∨ (p 2573) ∨ (¬ p 2850) ∨ (¬ p 4001) ∨ (¬ p 2274) ∨ (¬ p 3309) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106683 (p 2122) (p 2230) (p 2274) (p 2406) (p 2440) (p 2493) (p 2573) (p 2598) (p 2630) (p 2641) (p 2696) (p 2737) (p 2742) (p 2774) (p 2850) (p 2911) (p 3093) (p 3309) (p 3347) (p 3367) (p 3422) (p 3475) (p 3590) (p 4001) (p 4257) (p 4715) (p 4753) (p 4790) (p 5220) (derived106424 p h) (derived105514 p h) (derived105423 p h) (derived82874 p h) (derived77577 p h) (derived97817 p h) (derived77749 p h) (derived103124 p h) (derived96403 p h) (derived90608 p h) (derived90607 p h) (derived82950 p h) (derived72349 p h) (derived96922 p h) (derived106682 p h)

theorem derived106684 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2406) ∨ (p 3389) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106684 (p 2122) (p 2177) (p 2192) (p 2230) (p 2241) (p 2255) (p 2274) (p 2284) (p 2307) (p 2319) (p 2331) (p 2363) (p 2406) (p 2417) (p 2427) (p 2437) (p 2440) (p 2493) (p 2553) (p 2563) (p 2573) (p 2577) (p 2598) (p 2608) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2717) (p 2727) (p 2786) (p 2829) (p 2850) (p 2911) (p 2922) (p 2926) (p 2972) (p 2982) (p 3093) (p 3096) (p 3201) (p 3212) (p 3309) (p 3347) (p 3362) (p 3363) (p 3367) (p 3379) (p 3389) (p 3399) (p 3422) (p 3426) (p 3434) (p 3527) (p 3589) (p 3686) (p 3819) (p 3920) (p 3987) (p 4001) (p 4031) (p 4032) (p 4079) (p 4117) (p 4281) (p 4399) (p 4452) (p 4503) (p 4644) (p 4700) (p 4715) (p 4753) (p 4814) (p 4972) (p 5046) (p 5089) (p 5092) (p 5220) (derived105472 p h) (derived105373 p h) (derived105440 p h) (derived105367 p h) (derived105514 p h) (derived106530 p h) (derived105411 p h) (derived105423 p h) (derived106649 p h) (derived106650 p h) (derived103066 p h) (derived94485 p h) (h 5809) (derived77577 p h) (derived97817 p h) (derived106674 p h) (derived105882 p h) (derived100245 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived96969 p h) (h 17508) (derived99814 p h) (derived102520 p h) (h 27723) (h 23097) (derived96016 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived103122 p h) (derived96017 p h) (derived96409 p h) (derived87403 p h) (derived92102 p h) (h 8577) (derived66432 p h) (h 8571) (derived76702 p h) (derived106678 p h) (derived106679 p h) (derived106680 p h) (derived80454 p h) (derived77749 p h) (derived96484 p h) (derived95899 p h) (h 6473) (derived101933 p h) (derived96287 p h) (derived92594 p h) (derived87424 p h) (derived80333 p h) (derived101937 p h) (derived106665 p h) (derived95461 p h) (derived106658 p h) (derived93774 p h) (derived91051 p h) (derived91138 p h) (derived68915 p h) (derived106681 p h) (derived99643 p h) (derived75821 p h) (derived101932 p h) (derived88891 p h) (derived89614 p h) (derived106683 p h) (derived68719 p h) (derived43080 p h) (derived89193 p h)

theorem derived106685 (p : Nat → Prop) (h : Inputs p) :
    (p 3389) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106685 (p 2230) (p 2307) (p 2331) (p 2406) (p 2437) (p 2440) (p 2553) (p 2573) (p 2577) (p 2598) (p 2608) (p 2651) (p 2656) (p 2663) (p 2786) (p 2850) (p 3309) (p 3362) (p 3367) (p 3389) (p 3920) (p 3987) (p 4117) (p 4257) (p 4972) (p 5214) (derived105492 p h) (derived106674 p h) (derived106649 p h) (derived106650 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived103066 p h) (derived94485 p h) (h 5809) (derived102520 p h) (h 27723) (derived106684 p h) (derived87765 p h) (derived81070 p h) (derived90608 p h) (derived87813 p h)

theorem derived106686 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2264) ∨ (¬ p 2295) ∨ (¬ p 2241) ∨ (p 2996) ∨ (¬ p 2331) :=
  ElevenRUP.step106686 (p 2177) (p 2241) (p 2253) (p 2264) (p 2295) (p 2331) (p 2641) (p 2996) (p 4156) (derived96453 p h) (derived82153 p h) (derived82087 p h) (derived43081 p h) (derived90836 p h)

theorem derived106687 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2641) ∨ (p 2098) ∨ (¬ p 4138) ∨ (¬ p 2573) ∨ (¬ p 3189) ∨ (¬ p 4969) ∨ (p 2132) ∨ (¬ p 2241) ∨ (¬ p 4257) ∨ (p 2406) ∨ (p 2870) ∨ (¬ p 4984) ∨ (p 3016) ∨ (¬ p 4194) ∨ (¬ p 2307) ∨ (¬ p 4117) ∨ (¬ p 3178) ∨ (¬ p 4031) :=
  ElevenRUP.step106687 (p 2088) (p 2098) (p 2132) (p 2241) (p 2295) (p 2307) (p 2319) (p 2363) (p 2383) (p 2396) (p 2406) (p 2573) (p 2641) (p 2665) (p 2668) (p 2870) (p 2881) (p 3016) (p 3178) (p 3189) (p 3246) (p 3256) (p 3516) (p 4031) (p 4117) (p 4138) (p 4194) (p 4257) (p 4559) (p 4669) (p 4736) (p 4969) (p 4984) (derived105373 p h) (derived105701 p h) (derived105431 p h) (derived105415 p h) (derived104611 p h) (derived42760 p h) (derived96969 p h) (derived104414 p h) (derived45324 p h) (derived100716 p h) (derived75065 p h) (derived79361 p h) (derived86664 p h) (derived78550 p h) (derived78064 p h)

theorem derived106688 (p : Nat → Prop) (h : Inputs p) :
    (p 2668) ∨ (p 2363) ∨ (¬ p 4138) ∨ (¬ p 2295) ∨ (p 3051) ∨ (¬ p 4031) ∨ (¬ p 2440) :=
  ElevenRUP.step106688 (p 2295) (p 2363) (p 2440) (p 2459) (p 2668) (p 2881) (p 3051) (p 4031) (p 4138) (p 4559) (derived105701 p h) (derived79363 p h) (derived79361 p h) (derived92862 p h)

theorem derived106689 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2641) ∨ (p 2406) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106689 (p 2088) (p 2098) (p 2132) (p 2177) (p 2230) (p 2241) (p 2255) (p 2264) (p 2284) (p 2295) (p 2307) (p 2319) (p 2331) (p 2341) (p 2363) (p 2396) (p 2406) (p 2427) (p 2437) (p 2440) (p 2441) (p 2459) (p 2563) (p 2573) (p 2577) (p 2598) (p 2608) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2685) (p 2696) (p 2717) (p 2727) (p 2737) (p 2786) (p 2807) (p 2850) (p 2870) (p 2881) (p 2911) (p 2922) (p 2927) (p 2992) (p 2996) (p 3005) (p 3016) (p 3051) (p 3073) (p 3166) (p 3178) (p 3189) (p 3201) (p 3246) (p 3256) (p 3309) (p 3323) (p 3362) (p 3367) (p 3379) (p 3389) (p 3425) (p 3449) (p 3475) (p 3527) (p 3544) (p 3547) (p 3552) (p 3685) (p 3740) (p 3759) (p 3819) (p 3858) (p 3859) (p 3879) (p 3958) (p 3987) (p 4031) (p 4079) (p 4112) (p 4117) (p 4133) (p 4136) (p 4138) (p 4153) (p 4194) (p 4257) (p 4279) (p 4330) (p 4396) (p 4399) (p 4559) (p 4650) (p 4700) (p 4736) (p 4753) (p 4783) (p 4790) (p 4813) (p 4911) (p 4969) (p 4972) (p 4984) (p 5008) (p 5085) (p 5214) (derived105469 p h) (derived105492 p h) (derived105378 p h) (derived105367 p h) (derived106424 p h) (derived105373 p h) (derived105514 p h) (derived105712 p h) (derived105701 p h) (derived106329 p h) (derived105431 p h) (derived106665 p h) (derived96017 p h) (derived75069 p h) (derived92871 p h) (derived96363 p h) (derived106674 p h) (derived106649 p h) (derived87765 p h) (h 5209) (derived87995 p h) (derived90608 p h) (derived87813 p h) (derived104671 p h) (derived94842 p h) (derived106685 p h) (derived95983 p h) (h 6623) (derived96303 p h) (derived96281 p h) (derived105882 p h) (derived96927 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived106650 p h) (derived96969 p h) (h 17508) (derived96078 p h) (derived95141 p h) (derived103124 p h) (derived96403 p h) (derived82966 p h) (derived96397 p h) (derived96076 p h) (derived100245 p h) (derived48358 p h) (derived95901 p h) (derived79657 p h) (derived87993 p h) (derived93844 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived101272 p h) (derived81070 p h) (h 27723) (derived102520 p h) (derived104611 p h) (derived106686 p h) (derived89912 p h) (derived76884 p h) (derived97921 p h) (h 17796) (derived96077 p h) (derived95462 p h) (derived88773 p h) (derived76660 p h) (derived85136 p h) (derived102269 p h) (derived96452 p h) (derived76676 p h) (derived87334 p h) (derived77171 p h) (derived101769 p h) (derived100365 p h) (derived82296 p h) (derived82947 p h) (derived100536 p h) (derived96307 p h) (derived80612 p h) (derived102575 p h) (derived82950 p h) (derived100753 p h) (derived95979 p h) (derived96335 p h) (derived95238 p h) (h 31254) (derived96286 p h) (h 26523) (derived96873 p h) (derived96016 p h) (derived42760 p h) (derived102221 p h) (derived106687 p h) (derived92012 p h) (derived100716 p h) (derived96782 p h) (derived106688 p h) (derived86735 p h) (derived100859 p h) (derived99044 p h) (derived79319 p h) (derived88615 p h)

theorem derived106690 (p : Nat → Prop) (h : Inputs p) :
    (p 2406) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106690 (p 2132) (p 2230) (p 2241) (p 2253) (p 2255) (p 2264) (p 2284) (p 2295) (p 2307) (p 2319) (p 2331) (p 2341) (p 2406) (p 2427) (p 2437) (p 2440) (p 2563) (p 2573) (p 2577) (p 2598) (p 2608) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2685) (p 2696) (p 2717) (p 2727) (p 2786) (p 2807) (p 2850) (p 2870) (p 2881) (p 2992) (p 2996) (p 3016) (p 3051) (p 3166) (p 3189) (p 3201) (p 3309) (p 3362) (p 3367) (p 3379) (p 3389) (p 3425) (p 3475) (p 3740) (p 3759) (p 3819) (p 3879) (p 3958) (p 3987) (p 4079) (p 4117) (p 4136) (p 4257) (p 4279) (p 4280) (p 4399) (p 4550) (p 4650) (p 4700) (p 4736) (p 4753) (p 4783) (p 4790) (p 4813) (p 4972) (p 5008) (p 5085) (p 5214) (derived105469 p h) (derived105378 p h) (derived106424 p h) (derived105367 p h) (derived105373 p h) (derived105492 p h) (derived105514 p h) (derived105599 p h) (derived105431 p h) (derived96076 p h) (derived100245 p h) (derived106685 p h) (derived48358 p h) (derived96281 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived96078 p h) (derived95141 p h) (derived103124 p h) (derived96403 p h) (derived106674 p h) (derived82966 p h) (derived96397 p h) (derived106665 p h) (derived96017 p h) (derived75069 p h) (derived92871 p h) (derived96363 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived101272 p h) (derived105882 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived106649 p h) (derived106650 p h) (derived96969 p h) (h 17508) (derived101769 p h) (derived100365 p h) (derived82296 p h) (derived95901 p h) (derived79657 p h) (derived87765 p h) (derived87993 p h) (derived90608 p h) (derived93844 p h) (derived87813 p h) (derived82153 p h) (derived95983 p h) (derived82947 p h) (derived104671 p h) (derived81070 p h) (h 6623) (derived100536 p h) (derived94842 p h) (h 27723) (derived96303 p h) (derived102520 p h) (derived104611 p h) (derived106686 p h) (derived102508 p h) (derived89912 p h) (derived76884 p h) (derived106689 p h) (derived82044 p h) (derived86704 p h)

theorem derived106691 (p : Nat → Prop) (h : Inputs p) :
    (p 2881) ∨ (p 2098) ∨ (p 2132) ∨ (¬ p 2922) ∨ (¬ p 3379) ∨ (¬ p 2241) ∨ (¬ p 4969) ∨ (¬ p 3189) ∨ (¬ p 2295) ∨ (¬ p 2641) ∨ (p 2870) ∨ (p 2427) ∨ (p 2437) ∨ (¬ p 2307) ∨ (¬ p 4117) ∨ (¬ p 3178) ∨ (¬ p 2440) :=
  ElevenRUP.step106691 (p 2088) (p 2098) (p 2132) (p 2241) (p 2295) (p 2307) (p 2363) (p 2417) (p 2427) (p 2437) (p 2440) (p 2459) (p 2641) (p 2668) (p 2870) (p 2881) (p 2922) (p 3178) (p 3189) (p 3246) (p 3256) (p 3379) (p 4117) (p 4133) (p 4668) (p 4669) (p 4736) (p 4969) (derived105414 p h) (derived105712 p h) (derived105431 p h) (derived105415 p h) (derived74491 p h) (derived86694 p h) (derived86735 p h) (derived78061 p h) (derived79363 p h) (derived86664 p h) (derived104414 p h) (derived100716 p h)

theorem derived106692 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2573) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106692 (p 2098) (p 2132) (p 2177) (p 2230) (p 2241) (p 2253) (p 2255) (p 2264) (p 2274) (p 2284) (p 2295) (p 2307) (p 2331) (p 2341) (p 2352) (p 2363) (p 2396) (p 2406) (p 2427) (p 2437) (p 2440) (p 2493) (p 2553) (p 2563) (p 2573) (p 2584) (p 2598) (p 2608) (p 2619) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2696) (p 2717) (p 2727) (p 2737) (p 2797) (p 2850) (p 2870) (p 2881) (p 2911) (p 2922) (p 2996) (p 3005) (p 3016) (p 3051) (p 3146) (p 3166) (p 3178) (p 3189) (p 3201) (p 3246) (p 3309) (p 3367) (p 3379) (p 3389) (p 3422) (p 3425) (p 3564) (p 3658) (p 3685) (p 3740) (p 3958) (p 4042) (p 4079) (p 4112) (p 4117) (p 4210) (p 4277) (p 4279) (p 4281) (p 4330) (p 4389) (p 4396) (p 4399) (p 4559) (p 4700) (p 4736) (p 4752) (p 4753) (p 4790) (p 4969) (p 4972) (p 4976) (p 5008) (p 5085) (derived105367 p h) (derived106424 p h) (derived105469 p h) (derived105465 p h) (derived105373 p h) (derived105434 p h) (derived105514 p h) (derived105380 p h) (derived105378 p h) (derived106329 p h) (derived105431 p h) (derived105701 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived101272 p h) (derived106649 p h) (derived106650 p h) (derived104611 p h) (derived106674 p h) (derived87796 p h) (derived67191 p h) (derived96303 p h) (derived96302 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101769 p h) (derived96024 p h) (derived103124 p h) (derived87037 p h) (derived92245 p h) (derived95979 p h) (derived96934 p h) (derived78503 p h) (derived42845 p h) (derived42979 p h) (derived100245 p h) (derived95899 p h) (derived105882 p h) (derived101098 p h) (derived106690 p h) (derived93774 p h) (derived86142 p h) (derived96428 p h) (derived96076 p h) (derived106685 p h) (derived48358 p h) (derived96281 p h) (derived106665 p h) (derived96017 p h) (derived75069 p h) (derived92871 p h) (derived96077 p h) (derived106658 p h) (derived96873 p h) (derived82153 p h) (h 6473) (derived106686 p h) (derived43081 p h) (derived42760 p h) (h 21856) (derived77171 p h) (derived104829 p h) (derived102221 p h) (derived91440 p h) (derived91051 p h) (derived82874 p h) (derived82744 p h) (derived76884 p h) (derived76147 p h) (derived97921 p h) (h 17796) (derived106691 p h) (derived96358 p h) (derived88799 p h) (derived103032 p h) (derived100859 p h) (derived86687 p h) (derived51609 p h) (derived77030 p h) (derived84638 p h) (derived104050 p h)

theorem derived106693 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2573) ∨ (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106693 (p 2098) (p 2132) (p 2136) (p 2192) (p 2210) (p 2230) (p 2241) (p 2245) (p 2264) (p 2284) (p 2295) (p 2307) (p 2319) (p 2331) (p 2341) (p 2406) (p 2427) (p 2437) (p 2440) (p 2553) (p 2563) (p 2573) (p 2584) (p 2608) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2685) (p 2707) (p 2717) (p 2744) (p 2786) (p 2807) (p 2850) (p 2881) (p 2891) (p 3016) (p 3051) (p 3201) (p 3309) (p 3367) (p 3369) (p 3379) (p 3399) (p 3422) (p 3425) (p 3475) (p 3527) (p 3537) (p 3589) (p 3658) (p 3819) (p 3873) (p 3958) (p 3987) (p 4117) (p 4377) (p 4399) (p 4424) (p 4558) (p 4650) (p 4700) (p 4753) (p 4783) (p 4790) (p 4793) (p 4806) (p 4807) (p 4814) (p 4972) (p 4976) (p 4984) (p 5052) (p 5206) (derived105378 p h) (derived106170 p h) (derived106424 p h) (derived105373 p h) (derived105465 p h) (derived105514 p h) (derived105473 p h) (derived105440 p h) (derived105400 p h) (derived105438 p h) (derived106503 p h) (derived106690 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived96078 p h) (derived95141 p h) (derived103124 p h) (derived96403 p h) (derived106674 p h) (derived82966 p h) (derived96397 p h) (derived106649 p h) (derived96017 p h) (derived106665 p h) (derived75069 p h) (derived97408 p h) (derived96335 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived101272 p h) (derived103122 p h) (derived105882 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived106650 p h) (derived96969 p h) (h 17508) (derived99814 p h) (derived96934 p h) (derived104611 p h) (derived87796 p h) (derived78503 p h) (derived67191 p h) (derived42845 p h) (derived96302 p h) (derived76158 p h) (derived96390 p h) (derived106692 p h) (derived96976 p h) (derived104424 p h) (derived91131 p h) (derived88381 p h) (h 27689) (derived102521 p h) (derived103179 p h) (h 11411) (derived79891 p h) (derived92724 p h) (h 18942) (derived76306 p h) (derived91527 p h) (derived93490 p h) (derived89912 p h) (derived77954 p h) (derived77955 p h) (derived56542 p h) (derived100709 p h) (derived93161 p h)

theorem derived106694 (p : Nat → Prop) (h : Inputs p) :
    (p 2241) ∨ (¬ p 2295) ∨ (p 2166) ∨ (p 2573) ∨ (¬ p 2406) ∨ (¬ p 3389) ∨ (p 2891) ∨ (p 2437) ∨ (¬ p 2608) ∨ (¬ p 2331) ∨ (¬ p 2440) :=
  ElevenRUP.step106694 (p 2166) (p 2177) (p 2210) (p 2241) (p 2246) (p 2295) (p 2331) (p 2406) (p 2437) (p 2440) (p 2573) (p 2608) (p 2744) (p 2881) (p 2891) (p 2911) (p 2922) (p 2933) (p 2934) (p 3379) (p 3389) (p 3399) (p 3527) (p 4715) (p 4814) (p 4905) (derived105423 p h) (derived105995 p h) (derived106503 p h) (derived105440 p h) (derived74682 p h) (derived96899 p h) (derived96902 p h) (derived96975 p h) (derived91131 p h) (derived103179 p h) (derived95506 p h) (derived92724 p h) (derived80972 p h) (derived76306 p h) (derived74687 p h) (derived76260 p h)

theorem derived106695 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) ∨ (p 2717) ∨ (p 2341) ∨ (p 2363) ∨ (¬ p 3323) ∨ (p 2396) ∨ (¬ p 2241) ∨ (p 2737) ∨ (p 2707) ∨ (p 2619) ∨ (¬ p 2641) ∨ (¬ p 4210) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106695 (p 2132) (p 2230) (p 2241) (p 2341) (p 2363) (p 2396) (p 2440) (p 2459) (p 2619) (p 2641) (p 2696) (p 2707) (p 2717) (p 2737) (p 2742) (p 2881) (p 3146) (p 3323) (p 3425) (p 3959) (p 4210) (p 4330) (p 4559) (p 4736) (p 4752) (p 4753) (derived105701 p h) (derived105431 p h) (derived105514 p h) (derived105434 p h) (derived106329 p h) (derived96922 p h) (derived103030 p h) (derived104050 p h) (derived88615 p h) (derived81823 p h) (derived102506 p h) (derived82744 p h) (derived86043 p h)

theorem derived106696 (p : Nat → Prop) (h : Inputs p) :
    (p 2437) ∨ (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106696 (p 2132) (p 2143) (p 2166) (p 2177) (p 2192) (p 2230) (p 2241) (p 2255) (p 2284) (p 2295) (p 2331) (p 2341) (p 2352) (p 2363) (p 2373) (p 2396) (p 2406) (p 2427) (p 2437) (p 2440) (p 2459) (p 2493) (p 2497) (p 2553) (p 2563) (p 2573) (p 2577) (p 2608) (p 2619) (p 2630) (p 2641) (p 2651) (p 2656) (p 2663) (p 2665) (p 2668) (p 2707) (p 2717) (p 2727) (p 2737) (p 2761) (p 2786) (p 2839) (p 2850) (p 2870) (p 2881) (p 2891) (p 2911) (p 2922) (p 2933) (p 2972) (p 2982) (p 3051) (p 3063) (p 3093) (p 3096) (p 3146) (p 3166) (p 3189) (p 3201) (p 3237) (p 3246) (p 3256) (p 3266) (p 3286) (p 3309) (p 3319) (p 3323) (p 3343) (p 3362) (p 3367) (p 3389) (p 3422) (p 3461) (p 3475) (p 3506) (p 3564) (p 3582) (p 3658) (p 3695) (p 3842) (p 3845) (p 3848) (p 3852) (p 3923) (p 3945) (p 3948) (p 3987) (p 4031) (p 4117) (p 4119) (p 4133) (p 4210) (p 4279) (p 4281) (p 4349) (p 4377) (p 4399) (p 4443) (p 4452) (p 4509) (p 4700) (p 4710) (p 4715) (p 4736) (p 4753) (p 4759) (p 4790) (p 4814) (p 4972) (p 4973) (p 4992) (p 4996) (p 5008) (p 5046) (p 5063) (p 5085) (p 5172) (p 5281) (p 5284) (p 5287) (derived106424 p h) (derived105367 p h) (derived105469 p h) (derived105440 p h) (derived106170 p h) (derived105472 p h) (derived105392 p h) (derived105835 p h) (derived105423 p h) (derived105373 p h) (derived105514 p h) (derived105431 p h) (derived105474 p h) (derived105712 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived103122 p h) (derived96409 p h) (derived106649 p h) (derived96287 p h) (derived105882 p h) (h 5209) (derived87995 p h) (derived96927 p h) (derived101098 p h) (derived96449 p h) (h 11044) (derived101769 p h) (derived100245 p h) (derived95899 p h) (derived103124 p h) (derived96403 p h) (derived96017 p h) (derived96016 p h) (derived106665 p h) (derived75069 p h) (derived97408 p h) (derived92871 p h) (derived106674 p h) (derived96366 p h) (derived96367 p h) (derived106685 p h) (derived96281 p h) (derived106690 p h) (derived96428 p h) (derived96429 p h) (derived93774 p h) (derived96022 p h) (derived106693 p h) (derived102520 p h) (derived105078 p h) (derived77577 p h) (derived87420 p h) (derived87416 p h) (derived74710 p h) (derived87404 p h) (derived87403 p h) (derived74682 p h) (h 27723) (derived101912 p h) (derived81625 p h) (derived94484 p h) (derived96302 p h) (derived96303 p h) (derived77139 p h) (derived80065 p h) (derived96343 p h) (derived91679 p h) (derived96902 p h) (derived88755 p h) (derived91125 p h) (derived74717 p h) (derived76158 p h) (derived83821 p h) (derived82950 p h) (derived91402 p h) (derived86142 p h) (derived41298 p h) (derived96284 p h) (h 8334) (derived95146 p h) (derived66420 p h) (derived62016 p h) (h 8340) (derived94414 p h) (derived67255 p h) (derived96789 p h) (derived106694 p h) (derived80454 p h) (derived43081 p h) (derived42760 p h) (derived83528 p h) (derived92598 p h) (derived79435 p h) (derived106679 p h) (derived91440 p h) (derived42948 p h) (derived92012 p h) (derived76884 p h) (derived94382 p h) (derived102494 p h) (h 9008) (derived66456 p h) (h 9002) (derived106695 p h) (derived87258 p h) (derived74491 p h) (derived86735 p h) (derived87658 p h) (derived92417 p h) (derived92863 p h) (derived96981 p h) (derived99270 p h) (derived50141 p h) (derived92923 p h) (derived79611 p h)

theorem derived106697 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3309) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106697 (p 2230) (p 2284) (p 2437) (p 2440) (p 2553) (p 2563) (p 2665) (p 3016) (p 3309) (p 3581) (p 3958) (p 4117) (p 4700) (derived105373 p h) (derived105378 p h) (derived100363 p h) (derived106659 p h) (derived75062 p h) (derived101272 p h) (derived106696 p h) (derived103131 p h) (derived103891 p h) (derived102249 p h)

theorem derived106698 (p : Nat → Prop) (h : Inputs p) :
    (p 2363) ∨ (p 2307) ∨ (p 3323) ∨ (¬ p 3955) ∨ (¬ p 2778) ∨ (¬ p 2459) ∨ (¬ p 2437) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106698 (p 2230) (p 2307) (p 2363) (p 2427) (p 2437) (p 2440) (p 2459) (p 2528) (p 2563) (p 2630) (p 2778) (p 2901) (p 3083) (p 3323) (p 3569) (p 3879) (p 3955) (p 4419) (p 4420) (p 4558) (p 4700) (p 4790) (derived106424 p h) (derived105400 p h) (derived105707 p h) (derived100365 p h) (derived100363 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived98028 p h) (derived103124 p h) (derived106486 p h) (derived101303 p h) (derived104921 p h) (derived98046 p h)

theorem derived106699 (p : Nat → Prop) (h : Inputs p) :
    (p 2528) ∨ (¬ p 2363) ∨ (p 2307) ∨ (p 2177) ∨ (p 2774) ∨ (¬ p 2459) ∨ (¬ p 3573) ∨ (¬ p 2437) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106699 (p 2122) (p 2177) (p 2230) (p 2307) (p 2363) (p 2437) (p 2440) (p 2459) (p 2528) (p 2630) (p 2774) (p 2778) (p 2819) (p 3083) (p 3573) (p 4419) (p 4420) (p 4596) (p 4790) (p 5225) (derived106424 p h) (derived105495 p h) (derived105707 p h) (derived96910 p h) (derived103124 p h) (derived106486 p h) (derived106461 p h) (derived98046 p h) (derived86229 p h) (derived97853 p h) (derived90338 p h)

theorem derived106700 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3083) ∨ (¬ p 2528) ∨ (¬ p 2850) ∨ (¬ p 2531) ∨ (¬ p 2440) :=
  ElevenRUP.step106700 (p 2440) (p 2528) (p 2531) (p 2850) (p 3083) (p 3146) (derived47239 p h) (derived101326 p h)

theorem derived106701 (p : Nat → Prop) (h : Inputs p) :
    (p 3146) ∨ (p 2819) ∨ (¬ p 3256) ∨ (¬ p 4460) ∨ (¬ p 3990) ∨ (¬ p 5379) ∨ (p 2307) ∨ (p 2177) ∨ (p 2774) ∨ (¬ p 3166) :=
  ElevenRUP.step106701 (p 2122) (p 2177) (p 2307) (p 2774) (p 2778) (p 2819) (p 3146) (p 3166) (p 3256) (p 3483) (p 3917) (p 3990) (p 4433) (p 4460) (p 4786) (p 4902) (p 5263) (p 5268) (p 5379) (derived105456 p h) (derived106425 p h) (derived106150 p h) (derived96910 p h) (derived86469 p h) (derived90210 p h) (derived98340 p h) (h 8968) (h 8962) (derived66454 p h)

theorem derived106702 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2122) ∨ (p 3266) ∨ (¬ p 3146) ∨ (p 2819) ∨ (p 3083) ∨ (¬ p 4695) ∨ (p 2307) ∨ (¬ p 3204) ∨ (p 3323) ∨ (¬ p 2778) ∨ (¬ p 3953) ∨ (¬ p 3425) ∨ (¬ p 3366) ∨ (¬ p 2246) ∨ (¬ p 4022) ∨ (¬ p 3156) ∨ (¬ p 2373) ∨ (¬ p 3016) ∨ (¬ p 5119) ∨ (p 2449) ∨ (¬ p 4846) ∨ (¬ p 4067) ∨ (p 3309) ∨ (¬ p 2782) ∨ (¬ p 2663) ∨ (¬ p 4419) ∨ (¬ p 2230) ∨ (¬ p 3879) :=
  ElevenRUP.step106702 (p 2122) (p 2230) (p 2246) (p 2307) (p 2311) (p 2312) (p 2373) (p 2396) (p 2449) (p 2470) (p 2663) (p 2744) (p 2761) (p 2778) (p 2782) (p 2819) (p 3016) (p 3083) (p 3146) (p 3156) (p 3204) (p 3266) (p 3309) (p 3323) (p 3343) (p 3366) (p 3425) (p 3426) (p 3434) (p 3461) (p 3483) (p 3516) (p 3670) (p 3879) (p 3917) (p 3953) (p 3969) (p 4022) (p 4067) (p 4149) (p 4231) (p 4419) (p 4434) (p 4604) (p 4638) (p 4695) (p 4786) (p 4846) (p 5118) (p 5119) (p 5225) (p 5228) (p 5263) (p 5268) (p 5568) (p 6148) (p 6149) (derived106144 p h) (derived106293 p h) (derived105495 p h) (derived105482 p h) (derived106503 p h) (derived105409 p h) (derived106425 p h) (derived101806 p h) (derived101808 p h) (derived87445 p h) (derived96484 p h) (derived90389 p h) (derived90346 p h) (derived87570 p h) (h 8962) (derived89622 p h) (derived66454 p h) (derived102624 p h) (h 8967) (h 8968) (derived90258 p h) (derived90233 p h) (derived74650 p h) (derived95844 p h) (derived76654 p h) (derived94246 p h) (h 14391) (derived102159 p h) (derived66623 p h) (h 14398)

theorem derived106703 (p : Nat → Prop) (h : Inputs p) :
    (p 2717) ∨ (¬ p 2608) ∨ (¬ p 3581) ∨ (¬ p 2437) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106703 (p 2088) (p 2098) (p 2122) (p 2132) (p 2156) (p 2177) (p 2210) (p 2230) (p 2241) (p 2245) (p 2246) (p 2249) (p 2255) (p 2274) (p 2284) (p 2295) (p 2307) (p 2331) (p 2363) (p 2373) (p 2383) (p 2396) (p 2417) (p 2427) (p 2437) (p 2440) (p 2449) (p 2459) (p 2470) (p 2481) (p 2493) (p 2504) (p 2505) (p 2528) (p 2531) (p 2563) (p 2573) (p 2584) (p 2608) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2667) (p 2685) (p 2707) (p 2717) (p 2727) (p 2737) (p 2742) (p 2744) (p 2751) (p 2761) (p 2774) (p 2778) (p 2782) (p 2786) (p 2797) (p 2807) (p 2819) (p 2829) (p 2850) (p 2860) (p 2870) (p 2881) (p 2891) (p 2901) (p 2911) (p 2922) (p 2946) (p 2982) (p 2992) (p 2996) (p 3005) (p 3016) (p 3019) (p 3083) (p 3093) (p 3115) (p 3125) (p 3136) (p 3146) (p 3156) (p 3166) (p 3178) (p 3201) (p 3204) (p 3256) (p 3266) (p 3309) (p 3319) (p 3323) (p 3343) (p 3366) (p 3379) (p 3425) (p 3461) (p 3483) (p 3487) (p 3564) (p 3569) (p 3571) (p 3573) (p 3579) (p 3580) (p 3581) (p 3582) (p 3589) (p 3654) (p 3680) (p 3685) (p 3819) (p 3873) (p 3879) (p 3917) (p 3923) (p 3953) (p 3955) (p 3969) (p 3987) (p 3990) (p 4022) (p 4031) (p 4067) (p 4104) (p 4108) (p 4117) (p 4149) (p 4170) (p 4186) (p 4187) (p 4203) (p 4204) (p 4276) (p 4282) (p 4322) (p 4377) (p 4419) (p 4431) (p 4434) (p 4460) (p 4558) (p 4636) (p 4646) (p 4669) (p 4695) (p 4700) (p 4782) (p 4790) (p 4800) (p 4814) (p 4845) (p 4846) (p 4882) (p 4969) (p 4972) (p 5008) (p 5020) (p 5043) (p 5052) (p 5086) (p 5118) (p 5119) (p 5225) (p 5263) (p 5268) (p 5379) (p 5396) (p 5401) (p 5568) (p 6148) (p 6149) (derived105534 p h) (derived105469 p h) (derived105471 p h) (derived105440 p h) (derived106144 p h) (derived105473 p h) (derived105453 p h) (derived105373 p h) (derived106343 p h) (derived106513 p h) (derived106424 p h) (derived105400 p h) (derived105367 p h) (derived106170 p h) (derived105495 p h) (derived105415 p h) (derived105516 p h) (derived105482 p h) (derived106503 p h) (derived99814 p h) (h 5209) (derived87995 p h) (derived102335 p h) (h 6564) (derived105525 p h) (derived102554 p h) (derived100245 p h) (derived95900 p h) (derived87700 p h) (derived88750 p h) (derived96943 p h) (derived96016 p h) (derived100365 p h) (derived100363 p h) (derived66940 p h) (h 30182) (derived82329 p h) (derived98023 p h) (derived104425 p h) (derived96934 p h) (derived96944 p h) (derived105882 p h) (derived96927 p h) (derived101098 p h) (derived102873 p h) (derived103124 p h) (derived98067 p h) (derived84343 p h) (derived93816 p h) (h 11042) (derived82316 p h) (derived103131 p h) (derived101604 p h) (derived106579 p h) (derived104473 p h) (derived96448 p h) (derived106414 p h) (derived42955 p h) (derived96922 p h) (derived97365 p h) (derived90472 p h) (derived96910 p h) (derived96374 p h) (derived91521 p h) (h 22317) (h 27689) (derived69917 p h) (derived96304 p h) (derived82296 p h) (derived103160 p h) (derived106697 p h) (derived83591 p h) (derived103584 p h) (derived100361 p h) (h 6407) (derived82997 p h) (derived106655 p h) (derived96367 p h) (derived104424 p h) (derived81620 p h) (derived88381 p h) (derived87229 p h) (derived83857 p h) (derived96339 p h) (h 36523) (derived97247 p h) (derived102333 p h) (derived96449 p h) (h 11044) (derived50095 p h) (derived82395 p h) (derived106599 p h) (derived96975 p h) (derived98028 p h) (derived87285 p h) (derived78936 p h) (derived87445 p h) (derived96954 p h) (derived103179 p h) (derived61403 p h) (derived103484 p h) (derived79502 p h) (derived90153 p h) (derived92090 p h) (derived93048 p h) (derived79039 p h) (derived101940 p h) (derived91169 p h) (h 32074) (derived101769 p h) (derived84349 p h) (derived95979 p h) (derived106361 p h) (derived102587 p h) (derived86542 p h) (derived106413 p h) (derived98805 p h) (derived106500 p h) (derived96873 p h) (derived106486 p h) (derived97921 p h) (derived97920 p h) (h 17796) (derived89839 p h) (derived78596 p h) (derived91736 p h) (derived80377 p h) (derived98513 p h) (derived101909 p h) (derived102428 p h) (derived84192 p h) (derived79782 p h) (derived93637 p h) (derived80827 p h) (derived93717 p h) (derived102542 p h) (derived106698 p h) (derived90097 p h) (derived106699 p h) (derived96004 p h) (derived76917 p h) (derived96490 p h) (derived100716 p h) (derived106700 p h) (derived76927 p h) (derived106701 p h) (derived43227 p h) (derived101827 p h) (h 9314) (derived66468 p h) (h 9308) (derived106702 p h) (derived86382 p h) (derived90211 p h) (derived91160 p h) (derived96034 p h) (derived75837 p h) (h 8968) (derived81906 p h) (derived74650 p h) (derived66454 p h) (derived58790 p h) (h 8962) (h 14391) (derived86368 p h) (derived66623 p h) (h 14398)

theorem derived106704 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2608) ∨ (¬ p 3581) ∨ (¬ p 2437) ∨ (¬ p 4117) ∨ (¬ p 2230) ∨ (¬ p 2440) :=
  ElevenRUP.step106704 (p 2132) (p 2156) (p 2230) (p 2241) (p 2245) (p 2249) (p 2255) (p 2264) (p 2274) (p 2284) (p 2295) (p 2331) (p 2341) (p 2417) (p 2427) (p 2437) (p 2440) (p 2449) (p 2459) (p 2493) (p 2504) (p 2505) (p 2573) (p 2584) (p 2608) (p 2630) (p 2651) (p 2656) (p 2663) (p 2665) (p 2667) (p 2685) (p 2707) (p 2717) (p 2727) (p 2744) (p 2751) (p 2786) (p 2797) (p 2807) (p 2850) (p 2860) (p 2870) (p 2881) (p 2891) (p 2901) (p 2911) (p 2922) (p 2946) (p 2992) (p 2996) (p 3016) (p 3019) (p 3136) (p 3201) (p 3309) (p 3379) (p 3399) (p 3425) (p 3487) (p 3527) (p 3569) (p 3571) (p 3579) (p 3580) (p 3581) (p 3582) (p 3587) (p 3589) (p 3819) (p 3820) (p 3873) (p 3879) (p 3945) (p 3987) (p 4031) (p 4104) (p 4108) (p 4117) (p 4204) (p 4282) (p 4431) (p 4558) (p 4646) (p 4700) (p 4782) (p 4783) (p 4790) (p 4793) (p 4794) (p 4882) (p 4972) (p 5052) (p 5086) (derived106343 p h) (derived106513 p h) (derived105453 p h) (derived105367 p h) (derived105373 p h) (derived105400 p h) (derived106424 p h) (derived105534 p h) (derived105473 p h) (derived106503 p h) (derived105438 p h) (derived61403 p h) (derived102335 p h) (derived86542 p h) (derived103124 p h) (derived83857 p h) (h 5209) (derived87995 p h) (h 6564) (derived96927 p h) (derived105882 p h) (derived101098 p h) (derived96448 p h) (derived103131 p h) (derived101604 p h) (derived100363 p h) (derived66940 p h) (derived102873 p h) (derived98067 p h) (derived84343 p h) (derived96016 p h) (derived100365 p h) (h 30182) (derived82329 p h) (derived98023 p h) (derived104425 p h) (derived96934 p h) (derived100245 p h) (derived82296 p h) (derived96339 p h) (h 36523) (derived97247 p h) (derived102333 p h) (derived96449 p h) (h 11044) (derived105525 p h) (derived102554 p h) (derived95900 p h) (derived87700 p h) (derived88750 p h) (derived96943 p h) (derived96944 p h) (derived93816 p h) (h 11042) (derived82316 p h) (derived106579 p h) (derived50095 p h) (derived82395 p h) (derived104473 p h) (derived106599 p h) (derived92417 p h) (derived100136 p h) (derived91521 p h) (h 22317) (h 27689) (derived106697 p h) (derived83591 p h) (derived103584 p h) (derived100361 p h) (derived82997 p h) (derived103160 p h) (h 6407) (derived96397 p h) (derived69917 p h) (derived96304 p h) (derived102334 p h) (derived99814 p h) (derived106521 p h) (derived106655 p h) (derived104424 p h) (derived96367 p h) (derived81620 p h) (derived88381 p h) (derived96165 p h) (derived89912 p h) (derived104279 p h) (derived106703 p h) (derived92563 p h) (derived89229 p h)

end ElevenLogic
