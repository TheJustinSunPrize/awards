import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory000
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule2652 (p158 p164 : Prop) : (¬ p164) ∨ ((p158 ∨ p164)) := by
  classical
  tauto

theorem initial2652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 164)) ∨ (meaning t m 2257) := by
  exact rule2652 (meaning t m 158) (meaning t m 164)

theorem rule2669 (p2257 p2258 : Prop) (h : (p2257 ↔ p2258)) : (¬ p2257) ∨ (p2258) := by
  classical
  tauto

theorem initial2669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2257)) ∨ (meaning t m 2258) := by
  have source := ElevenTheory.theory80 t (m.theta 3 7) (m.theta 3 8) (m.theta 7 8)
  exact rule2669 (meaning t m 2257) (meaning t m 2258) source

theorem rule2671 (p170 p176 : Prop) : (¬ p170) ∨ ((p170 ∨ p176)) := by
  classical
  tauto

theorem initial2671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 170)) ∨ (meaning t m 2267) := by
  exact rule2671 (meaning t m 170) (meaning t m 176)

theorem rule2672 (p170 p176 : Prop) : (¬ p176) ∨ ((p170 ∨ p176)) := by
  classical
  tauto

theorem initial2672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 176)) ∨ (meaning t m 2267) := by
  exact rule2672 (meaning t m 170) (meaning t m 176)

theorem rule2689 (p2267 p2268 : Prop) (h : (p2267 ↔ p2268)) : (¬ p2267) ∨ (p2268) := by
  classical
  tauto

theorem initial2689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2267)) ∨ (meaning t m 2268) := by
  have source := ElevenTheory.theory81 t (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule2689 (meaning t m 2267) (meaning t m 2268) source

theorem rule2691 (p182 p188 : Prop) : (¬ p182) ∨ ((p182 ∨ p188)) := by
  classical
  tauto

theorem initial2691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 182)) ∨ (meaning t m 2277) := by
  exact rule2691 (meaning t m 182) (meaning t m 188)

theorem rule2692 (p182 p188 : Prop) : (¬ p188) ∨ ((p182 ∨ p188)) := by
  classical
  tauto

theorem initial2692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 188)) ∨ (meaning t m 2277) := by
  exact rule2692 (meaning t m 182) (meaning t m 188)

theorem rule2709 (p2277 p2278 : Prop) (h : (p2277 ↔ p2278)) : (¬ p2277) ∨ (p2278) := by
  classical
  tauto

theorem initial2709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2277)) ∨ (meaning t m 2278) := by
  have source := ElevenTheory.theory82 t (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule2709 (meaning t m 2277) (meaning t m 2278) source

theorem rule2711 (p2033 p2287 : Prop) (h : ((¬ p2033) ↔ (¬ p2287))) : (p2033) ∨ (¬ p2287) := by
  classical
  tauto

theorem initial2711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2033) ∨ (¬ (meaning t m 2287)) := by
  have source := ElevenTheory.theory83 t (m.theta 3 6)
  exact rule2711 (meaning t m 2033) (meaning t m 2287) source

theorem rule2713 (p194 p200 : Prop) : (¬ p194) ∨ ((p194 ∨ p200)) := by
  classical
  tauto

theorem initial2713 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 194)) ∨ (meaning t m 2288) := by
  exact rule2713 (meaning t m 194) (meaning t m 200)

theorem rule2714 (p194 p200 : Prop) : (¬ p200) ∨ ((p194 ∨ p200)) := by
  classical
  tauto

theorem initial2714 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 200)) ∨ (meaning t m 2288) := by
  exact rule2714 (meaning t m 194) (meaning t m 200)

theorem rule2731 (p2288 p2289 : Prop) (h : (p2288 ↔ p2289)) : (¬ p2288) ∨ (p2289) := by
  classical
  tauto

theorem initial2731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2288)) ∨ (meaning t m 2289) := by
  have source := ElevenTheory.theory84 t (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule2731 (meaning t m 2288) (meaning t m 2289) source

theorem rule2733 (p2264 p2298 p2299 : Prop) (h : (¬ p2264) ∨ (¬ p2298) ∨ (¬ p2299)) : (¬ p2264) ∨ (¬ p2298) ∨ (¬ p2299) := by
  classical
  tauto

theorem initial2733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2299)) := by
  have source := ElevenTheory.theory85 (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule2733 (meaning t m 2264) (meaning t m 2298) (meaning t m 2299) source

theorem rule2734 (p206 p212 : Prop) : (¬ p206) ∨ ((p206 ∨ p212)) := by
  classical
  tauto

theorem initial2734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 206)) ∨ (meaning t m 2300) := by
  exact rule2734 (meaning t m 206) (meaning t m 212)

theorem rule2735 (p206 p212 : Prop) : (¬ p212) ∨ ((p206 ∨ p212)) := by
  classical
  tauto

theorem initial2735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 212)) ∨ (meaning t m 2300) := by
  exact rule2735 (meaning t m 206) (meaning t m 212)

theorem rule2752 (p2300 p2301 : Prop) (h : (p2300 ↔ p2301)) : (¬ p2300) ∨ (p2301) := by
  classical
  tauto

theorem initial2752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2300)) ∨ (meaning t m 2301) := by
  have source := ElevenTheory.theory86 t (m.theta 0 6) (m.theta 0 7) (m.theta 6 7)
  exact rule2752 (meaning t m 2300) (meaning t m 2301) source

theorem rule2754 (p2311 p2312 p2313 p2314 p2315 : Prop) : (¬ (p2311 ∧ p2312 ∧ p2313 ∧ p2314 ∧ p2315)) ∨ (p2311) := by
  classical
  tauto

theorem initial2754 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2310)) ∨ (meaning t m 2311) := by
  exact rule2754 (meaning t m 2311) (meaning t m 2312) (meaning t m 2313) (meaning t m 2314) (meaning t m 2315)

theorem rule2755 (p2311 p2312 p2313 p2314 p2315 : Prop) : (¬ (p2311 ∧ p2312 ∧ p2313 ∧ p2314 ∧ p2315)) ∨ (p2312) := by
  classical
  tauto

theorem initial2755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2310)) ∨ (meaning t m 2312) := by
  exact rule2755 (meaning t m 2311) (meaning t m 2312) (meaning t m 2313) (meaning t m 2314) (meaning t m 2315)

theorem rule2756 (p2311 p2312 p2313 p2314 p2315 : Prop) : (¬ (p2311 ∧ p2312 ∧ p2313 ∧ p2314 ∧ p2315)) ∨ (p2313) := by
  classical
  tauto

theorem initial2756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2310)) ∨ (meaning t m 2313) := by
  exact rule2756 (meaning t m 2311) (meaning t m 2312) (meaning t m 2313) (meaning t m 2314) (meaning t m 2315)

theorem rule2758 (p2311 p2312 p2313 p2314 p2315 : Prop) : (¬ (p2311 ∧ p2312 ∧ p2313 ∧ p2314 ∧ p2315)) ∨ (p2315) := by
  classical
  tauto

theorem initial2758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2310)) ∨ (meaning t m 2315) := by
  exact rule2758 (meaning t m 2311) (meaning t m 2312) (meaning t m 2313) (meaning t m 2314) (meaning t m 2315)

theorem rule2761 (p2311 p2312 p2313 p2314 p2315 : Prop) : (p2311) ∨ (((¬ p2315) ∨ (¬ p2311) ∨ (¬ p2312) ∨ (¬ p2313) ∨ (¬ p2314))) := by
  classical
  tauto

theorem initial2761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2311) ∨ (meaning t m 2316) := by
  exact rule2761 (meaning t m 2311) (meaning t m 2312) (meaning t m 2313) (meaning t m 2314) (meaning t m 2315)

theorem rule2762 (p2311 p2312 p2313 p2314 p2315 : Prop) : (p2312) ∨ (((¬ p2315) ∨ (¬ p2311) ∨ (¬ p2312) ∨ (¬ p2313) ∨ (¬ p2314))) := by
  classical
  tauto

theorem initial2762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2312) ∨ (meaning t m 2316) := by
  exact rule2762 (meaning t m 2311) (meaning t m 2312) (meaning t m 2313) (meaning t m 2314) (meaning t m 2315)

theorem rule2766 (p2310 p2316 : Prop) (h : (p2310 ↔ (¬ p2316))) : (¬ p2310) ∨ (¬ p2316) := by
  classical
  tauto

theorem initial2766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2310)) ∨ (¬ (meaning t m 2316)) := by
  have source := ElevenTheory.theory87 t (m.theta 0 6) (m.theta 0 7) (m.theta 6 7)
  exact rule2766 (meaning t m 2310) (meaning t m 2316) source

theorem rule2768 (p2307 p2318 p2319 p2320 p2321 : Prop) : (¬ (p2318 ∧ p2319 ∧ p2307 ∧ p2320 ∧ p2321)) ∨ (p2318) := by
  classical
  tauto

theorem initial2768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2317)) ∨ (meaning t m 2318) := by
  exact rule2768 (meaning t m 2307) (meaning t m 2318) (meaning t m 2319) (meaning t m 2320) (meaning t m 2321)

theorem rule2769 (p2307 p2318 p2319 p2320 p2321 : Prop) : (¬ (p2318 ∧ p2319 ∧ p2307 ∧ p2320 ∧ p2321)) ∨ (p2319) := by
  classical
  tauto

theorem initial2769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2317)) ∨ (meaning t m 2319) := by
  exact rule2769 (meaning t m 2307) (meaning t m 2318) (meaning t m 2319) (meaning t m 2320) (meaning t m 2321)

theorem rule2770 (p2307 p2318 p2319 p2320 p2321 : Prop) : (p2307) ∨ (¬ (p2318 ∧ p2319 ∧ p2307 ∧ p2320 ∧ p2321)) := by
  classical
  tauto

theorem initial2770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2307) ∨ (¬ (meaning t m 2317)) := by
  exact rule2770 (meaning t m 2307) (meaning t m 2318) (meaning t m 2319) (meaning t m 2320) (meaning t m 2321)

theorem rule2772 (p2307 p2318 p2319 p2320 p2321 : Prop) : (¬ (p2318 ∧ p2319 ∧ p2307 ∧ p2320 ∧ p2321)) ∨ (p2321) := by
  classical
  tauto

theorem initial2772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2317)) ∨ (meaning t m 2321) := by
  exact rule2772 (meaning t m 2307) (meaning t m 2318) (meaning t m 2319) (meaning t m 2320) (meaning t m 2321)

theorem rule2774 (p2307 p2318 p2319 p2320 p2321 : Prop) : (p2318) ∨ (((¬ p2318) ∨ (¬ p2320) ∨ (¬ p2321) ∨ (¬ p2307) ∨ (¬ p2319))) := by
  classical
  tauto

theorem initial2774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2318) ∨ (meaning t m 2322) := by
  exact rule2774 (meaning t m 2307) (meaning t m 2318) (meaning t m 2319) (meaning t m 2320) (meaning t m 2321)

theorem rule2778 (p2307 p2318 p2319 p2320 p2321 : Prop) : (p2319) ∨ (((¬ p2318) ∨ (¬ p2320) ∨ (¬ p2321) ∨ (¬ p2307) ∨ (¬ p2319))) := by
  classical
  tauto

theorem initial2778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2319) ∨ (meaning t m 2322) := by
  exact rule2778 (meaning t m 2307) (meaning t m 2318) (meaning t m 2319) (meaning t m 2320) (meaning t m 2321)

theorem rule2780 (p2317 p2322 : Prop) (h : (p2317 ↔ (¬ p2322))) : (¬ p2317) ∨ (¬ p2322) := by
  classical
  tauto

theorem initial2780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2317)) ∨ (¬ (meaning t m 2322)) := by
  have source := ElevenTheory.theory88 t (m.theta 0 6) (m.theta 0 7) (m.theta 6 7)
  exact rule2780 (meaning t m 2317) (meaning t m 2322) source

theorem rule2782 (p2034 p2323 : Prop) (h : ((¬ p2034) ↔ (¬ p2323))) : (p2034) ∨ (¬ p2323) := by
  classical
  tauto

theorem initial2782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2034) ∨ (¬ (meaning t m 2323)) := by
  have source := ElevenTheory.theory89 t (m.theta 0 3)
  exact rule2782 (meaning t m 2034) (meaning t m 2323) source

theorem rule2784 (p218 p224 : Prop) : (¬ p218) ∨ ((p218 ∨ p224)) := by
  classical
  tauto

theorem initial2784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 218)) ∨ (meaning t m 2324) := by
  exact rule2784 (meaning t m 218) (meaning t m 224)

theorem rule2785 (p218 p224 : Prop) : (¬ p224) ∨ ((p218 ∨ p224)) := by
  classical
  tauto

theorem initial2785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 224)) ∨ (meaning t m 2324) := by
  exact rule2785 (meaning t m 218) (meaning t m 224)

theorem rule2802 (p2324 p2325 : Prop) (h : (p2324 ↔ p2325)) : (¬ p2324) ∨ (p2325) := by
  classical
  tauto

theorem initial2802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2324)) ∨ (meaning t m 2325) := by
  have source := ElevenTheory.theory90 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 6)
  exact rule2802 (meaning t m 2324) (meaning t m 2325) source

theorem rule2804 (p230 p236 : Prop) : (¬ p230) ∨ ((p230 ∨ p236)) := by
  classical
  tauto

theorem initial2804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 230)) ∨ (meaning t m 2334) := by
  exact rule2804 (meaning t m 230) (meaning t m 236)

theorem rule2805 (p230 p236 : Prop) : (¬ p236) ∨ ((p230 ∨ p236)) := by
  classical
  tauto

theorem initial2805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 236)) ∨ (meaning t m 2334) := by
  exact rule2805 (meaning t m 230) (meaning t m 236)

theorem rule2822 (p2334 p2335 : Prop) (h : (p2334 ↔ p2335)) : (¬ p2334) ∨ (p2335) := by
  classical
  tauto

theorem initial2822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2334)) ∨ (meaning t m 2335) := by
  have source := ElevenTheory.theory91 t (m.theta 0 7) (m.theta 0 8) (m.theta 7 8)
  exact rule2822 (meaning t m 2334) (meaning t m 2335) source

theorem rule2824 (p2299 p2312 p2341 : Prop) (h : (¬ p2312) ∨ (¬ p2341) ∨ (¬ p2299)) : (¬ p2299) ∨ (¬ p2312) ∨ (¬ p2341) := by
  classical
  tauto

theorem initial2824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2341)) := by
  have source := ElevenTheory.theory92 (m.theta 0 7) (m.theta 6 7) (m.theta 7 8)
  exact rule2824 (meaning t m 2299) (meaning t m 2312) (meaning t m 2341) source

theorem rule2825 (p2035 p2344 : Prop) (h : ((¬ p2035) ↔ (¬ p2344))) : (p2035) ∨ (¬ p2344) := by
  classical
  tauto

theorem initial2825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2035) ∨ (¬ (meaning t m 2344)) := by
  have source := ElevenTheory.theory93 t (m.theta 0 6)
  exact rule2825 (meaning t m 2035) (meaning t m 2344) source

theorem rule2827 (p242 p248 : Prop) : (¬ p242) ∨ ((p242 ∨ p248)) := by
  classical
  tauto

theorem initial2827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 242)) ∨ (meaning t m 2345) := by
  exact rule2827 (meaning t m 242) (meaning t m 248)

theorem rule2828 (p242 p248 : Prop) : (¬ p248) ∨ ((p242 ∨ p248)) := by
  classical
  tauto

theorem initial2828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 248)) ∨ (meaning t m 2345) := by
  exact rule2828 (meaning t m 242) (meaning t m 248)

theorem rule2845 (p2345 p2346 : Prop) (h : (p2345 ↔ p2346)) : (¬ p2345) ∨ (p2346) := by
  classical
  tauto

theorem initial2845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2345)) ∨ (meaning t m 2346) := by
  have source := ElevenTheory.theory94 t (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule2845 (meaning t m 2345) (meaning t m 2346) source

theorem rule2847 (p2036 p2355 : Prop) (h : ((¬ p2036) ↔ (¬ p2355))) : (p2036) ∨ (¬ p2355) := by
  classical
  tauto

theorem initial2847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2036) ∨ (¬ (meaning t m 2355)) := by
  have source := ElevenTheory.theory95 t (m.theta 3 7)
  exact rule2847 (meaning t m 2036) (meaning t m 2355) source

theorem rule2849 (p254 p260 : Prop) : (¬ p254) ∨ ((p254 ∨ p260)) := by
  classical
  tauto

theorem initial2849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 254)) ∨ (meaning t m 2356) := by
  exact rule2849 (meaning t m 254) (meaning t m 260)

theorem rule2850 (p254 p260 : Prop) : (¬ p260) ∨ ((p254 ∨ p260)) := by
  classical
  tauto

theorem initial2850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 260)) ∨ (meaning t m 2356) := by
  exact rule2850 (meaning t m 254) (meaning t m 260)

theorem rule2867 (p2356 p2357 : Prop) (h : (p2356 ↔ p2357)) : (¬ p2356) ∨ (p2357) := by
  classical
  tauto

theorem initial2867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2356)) ∨ (meaning t m 2357) := by
  have source := ElevenTheory.theory96 t (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule2867 (meaning t m 2356) (meaning t m 2357) source

theorem rule2869 (p266 p272 : Prop) : (¬ p266) ∨ ((p266 ∨ p272)) := by
  classical
  tauto

theorem initial2869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 266)) ∨ (meaning t m 2366) := by
  exact rule2869 (meaning t m 266) (meaning t m 272)

theorem rule2870 (p266 p272 : Prop) : (¬ p272) ∨ ((p266 ∨ p272)) := by
  classical
  tauto

theorem initial2870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 272)) ∨ (meaning t m 2366) := by
  exact rule2870 (meaning t m 266) (meaning t m 272)

theorem rule2887 (p2366 p2367 : Prop) (h : (p2366 ↔ p2367)) : (¬ p2366) ∨ (p2367) := by
  classical
  tauto

theorem initial2887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2366)) ∨ (meaning t m 2367) := by
  have source := ElevenTheory.theory97 t (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule2887 (meaning t m 2366) (meaning t m 2367) source

theorem rule2889 (p278 p284 : Prop) : (¬ p278) ∨ ((p278 ∨ p284)) := by
  classical
  tauto

theorem initial2889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 278)) ∨ (meaning t m 2376) := by
  exact rule2889 (meaning t m 278) (meaning t m 284)

theorem rule2890 (p278 p284 : Prop) : (¬ p284) ∨ ((p278 ∨ p284)) := by
  classical
  tauto

theorem initial2890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 284)) ∨ (meaning t m 2376) := by
  exact rule2890 (meaning t m 278) (meaning t m 284)

theorem rule2907 (p2376 p2377 : Prop) (h : (p2376 ↔ p2377)) : (¬ p2376) ∨ (p2377) := by
  classical
  tauto

theorem initial2907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2376)) ∨ (meaning t m 2377) := by
  have source := ElevenTheory.theory98 t (m.theta 0 6) (m.theta 0 8) (m.theta 6 8)
  exact rule2907 (meaning t m 2376) (meaning t m 2377) source

theorem rule2909 (p2352 p2386 p2387 : Prop) (h : (¬ p2386) ∨ (¬ p2352) ∨ (¬ p2387)) : (¬ p2352) ∨ (¬ p2386) ∨ (¬ p2387) := by
  classical
  tauto

theorem initial2909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2387)) := by
  have source := ElevenTheory.theory99 (m.theta 0 6) (m.theta 4 6) (m.theta 6 8)
  exact rule2909 (meaning t m 2352) (meaning t m 2386) (meaning t m 2387) source

theorem rule2910 (p2037 p2388 : Prop) (h : ((¬ p2037) ↔ (¬ p2388))) : (p2037) ∨ (¬ p2388) := by
  classical
  tauto

theorem initial2910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2037) ∨ (¬ (meaning t m 2388)) := by
  have source := ElevenTheory.theory100 t (m.theta 3 5)
  exact rule2910 (meaning t m 2037) (meaning t m 2388) source

theorem rule2912 (p290 p296 : Prop) : (¬ p290) ∨ ((p290 ∨ p296)) := by
  classical
  tauto

theorem initial2912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 290)) ∨ (meaning t m 2389) := by
  exact rule2912 (meaning t m 290) (meaning t m 296)

theorem rule2913 (p290 p296 : Prop) : (¬ p296) ∨ ((p290 ∨ p296)) := by
  classical
  tauto

theorem initial2913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 296)) ∨ (meaning t m 2389) := by
  exact rule2913 (meaning t m 290) (meaning t m 296)

theorem rule2930 (p2389 p2390 : Prop) (h : (p2389 ↔ p2390)) : (¬ p2389) ∨ (p2390) := by
  classical
  tauto

theorem initial2930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2389)) ∨ (meaning t m 2390) := by
  have source := ElevenTheory.theory101 t (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule2930 (meaning t m 2389) (meaning t m 2390) source

theorem rule2932 (p302 p308 : Prop) : (¬ p302) ∨ ((p302 ∨ p308)) := by
  classical
  tauto

theorem initial2932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 302)) ∨ (meaning t m 2399) := by
  exact rule2932 (meaning t m 302) (meaning t m 308)

theorem rule2933 (p302 p308 : Prop) : (¬ p308) ∨ ((p302 ∨ p308)) := by
  classical
  tauto

theorem initial2933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 308)) ∨ (meaning t m 2399) := by
  exact rule2933 (meaning t m 302) (meaning t m 308)

theorem rule2950 (p2399 p2400 : Prop) (h : (p2399 ↔ p2400)) : (¬ p2399) ∨ (p2400) := by
  classical
  tauto

theorem initial2950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2399)) ∨ (meaning t m 2400) := by
  have source := ElevenTheory.theory102 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5)
  exact rule2950 (meaning t m 2399) (meaning t m 2400) source

theorem rule2952 (p2038 p2409 : Prop) (h : ((¬ p2038) ↔ (¬ p2409))) : (p2038) ∨ (¬ p2409) := by
  classical
  tauto

theorem initial2952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2038) ∨ (¬ (meaning t m 2409)) := by
  have source := ElevenTheory.theory103 t (m.theta 1 4)
  exact rule2952 (meaning t m 2038) (meaning t m 2409) source

theorem rule2954 (p314 p320 : Prop) : (¬ p314) ∨ ((p314 ∨ p320)) := by
  classical
  tauto

theorem initial2954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 314)) ∨ (meaning t m 2410) := by
  exact rule2954 (meaning t m 314) (meaning t m 320)

theorem rule2955 (p314 p320 : Prop) : (¬ p320) ∨ ((p314 ∨ p320)) := by
  classical
  tauto

theorem initial2955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 320)) ∨ (meaning t m 2410) := by
  exact rule2955 (meaning t m 314) (meaning t m 320)

theorem rule2972 (p2410 p2411 : Prop) (h : (p2410 ↔ p2411)) : (¬ p2410) ∨ (p2411) := by
  classical
  tauto

theorem initial2972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2410)) ∨ (meaning t m 2411) := by
  have source := ElevenTheory.theory104 t (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule2972 (meaning t m 2410) (meaning t m 2411) source

theorem rule2974 (p326 p332 : Prop) : (¬ p326) ∨ ((p326 ∨ p332)) := by
  classical
  tauto

theorem initial2974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 326)) ∨ (meaning t m 2420) := by
  exact rule2974 (meaning t m 326) (meaning t m 332)

theorem rule2975 (p326 p332 : Prop) : (¬ p332) ∨ ((p326 ∨ p332)) := by
  classical
  tauto

theorem initial2975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 332)) ∨ (meaning t m 2420) := by
  exact rule2975 (meaning t m 326) (meaning t m 332)

theorem rule2992 (p2420 p2421 : Prop) (h : (p2420 ↔ p2421)) : (¬ p2420) ∨ (p2421) := by
  classical
  tauto

theorem initial2992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2420)) ∨ (meaning t m 2421) := by
  have source := ElevenTheory.theory105 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule2992 (meaning t m 2420) (meaning t m 2421) source

theorem rule2994 (p338 p344 : Prop) : (¬ p338) ∨ ((p338 ∨ p344)) := by
  classical
  tauto

theorem initial2994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 338)) ∨ (meaning t m 2430) := by
  exact rule2994 (meaning t m 338) (meaning t m 344)

theorem rule2995 (p338 p344 : Prop) : (¬ p344) ∨ ((p338 ∨ p344)) := by
  classical
  tauto

theorem initial2995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 344)) ∨ (meaning t m 2430) := by
  exact rule2995 (meaning t m 338) (meaning t m 344)

theorem rule3012 (p2430 p2431 : Prop) (h : (p2430 ↔ p2431)) : (¬ p2430) ∨ (p2431) := by
  classical
  tauto

theorem initial3012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2430)) ∨ (meaning t m 2431) := by
  have source := ElevenTheory.theory106 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule3012 (meaning t m 2430) (meaning t m 2431) source

theorem rule3014 (p2437 p2440 p2441 : Prop) (h : (¬ p2440) ∨ (¬ p2441) ∨ (¬ p2437)) : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2441) := by
  classical
  tauto

theorem initial3014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2441)) := by
  have source := ElevenTheory.theory107 (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule3014 (meaning t m 2437) (meaning t m 2440) (meaning t m 2441) source

theorem rule3015 (p350 p356 : Prop) : (¬ p350) ∨ ((p350 ∨ p356)) := by
  classical
  tauto

theorem initial3015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 350)) ∨ (meaning t m 2442) := by
  exact rule3015 (meaning t m 350) (meaning t m 356)

theorem rule3016 (p350 p356 : Prop) : (¬ p356) ∨ ((p350 ∨ p356)) := by
  classical
  tauto

theorem initial3016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 356)) ∨ (meaning t m 2442) := by
  exact rule3016 (meaning t m 350) (meaning t m 356)

theorem rule3033 (p2442 p2443 : Prop) (h : (p2442 ↔ p2443)) : (¬ p2442) ∨ (p2443) := by
  classical
  tauto

theorem initial3033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2442)) ∨ (meaning t m 2443) := by
  have source := ElevenTheory.theory108 t (m.theta 3 7) (m.theta 3 9) (m.theta 7 9)
  exact rule3033 (meaning t m 2442) (meaning t m 2443) source

theorem rule3035 (p362 p368 : Prop) : (¬ p362) ∨ ((p362 ∨ p368)) := by
  classical
  tauto

theorem initial3035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 362)) ∨ (meaning t m 2452) := by
  exact rule3035 (meaning t m 362) (meaning t m 368)

theorem rule3036 (p362 p368 : Prop) : (¬ p368) ∨ ((p362 ∨ p368)) := by
  classical
  tauto

theorem initial3036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 368)) ∨ (meaning t m 2452) := by
  exact rule3036 (meaning t m 362) (meaning t m 368)

theorem rule3053 (p2452 p2453 : Prop) (h : (p2452 ↔ p2453)) : (¬ p2452) ∨ (p2453) := by
  classical
  tauto

theorem initial3053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2452)) ∨ (meaning t m 2453) := by
  have source := ElevenTheory.theory109 t (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule3053 (meaning t m 2452) (meaning t m 2453) source

theorem rule3055 (p2039 p2462 : Prop) (h : ((¬ p2039) ↔ (¬ p2462))) : (p2039) ∨ (¬ p2462) := by
  classical
  tauto

theorem initial3055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2039) ∨ (¬ (meaning t m 2462)) := by
  have source := ElevenTheory.theory110 t (m.theta 7 9)
  exact rule3055 (meaning t m 2039) (meaning t m 2462) source

theorem rule3057 (p374 p380 : Prop) : (¬ p374) ∨ ((p374 ∨ p380)) := by
  classical
  tauto

theorem initial3057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 374)) ∨ (meaning t m 2463) := by
  exact rule3057 (meaning t m 374) (meaning t m 380)

theorem rule3058 (p374 p380 : Prop) : (¬ p380) ∨ ((p374 ∨ p380)) := by
  classical
  tauto

theorem initial3058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 380)) ∨ (meaning t m 2463) := by
  exact rule3058 (meaning t m 374) (meaning t m 380)

theorem rule3075 (p2463 p2464 : Prop) (h : (p2463 ↔ p2464)) : (¬ p2463) ∨ (p2464) := by
  classical
  tauto

theorem initial3075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2463)) ∨ (meaning t m 2464) := by
  have source := ElevenTheory.theory111 t (m.theta 0 4) (m.theta 0 8) (m.theta 4 8)
  exact rule3075 (meaning t m 2463) (meaning t m 2464) source

theorem rule3077 (p2474 p2475 p2476 p2477 p2478 : Prop) : (¬ (p2474 ∧ p2475 ∧ p2476 ∧ p2477 ∧ p2478)) ∨ (p2474) := by
  classical
  tauto

theorem initial3077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2473)) ∨ (meaning t m 2474) := by
  exact rule3077 (meaning t m 2474) (meaning t m 2475) (meaning t m 2476) (meaning t m 2477) (meaning t m 2478)

theorem rule3078 (p2474 p2475 p2476 p2477 p2478 : Prop) : (¬ (p2474 ∧ p2475 ∧ p2476 ∧ p2477 ∧ p2478)) ∨ (p2475) := by
  classical
  tauto

theorem initial3078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2473)) ∨ (meaning t m 2475) := by
  exact rule3078 (meaning t m 2474) (meaning t m 2475) (meaning t m 2476) (meaning t m 2477) (meaning t m 2478)

theorem rule3079 (p2474 p2475 p2476 p2477 p2478 : Prop) : (¬ (p2474 ∧ p2475 ∧ p2476 ∧ p2477 ∧ p2478)) ∨ (p2476) := by
  classical
  tauto

theorem initial3079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2473)) ∨ (meaning t m 2476) := by
  exact rule3079 (meaning t m 2474) (meaning t m 2475) (meaning t m 2476) (meaning t m 2477) (meaning t m 2478)

theorem rule3081 (p2474 p2475 p2476 p2477 p2478 : Prop) : (¬ (p2474 ∧ p2475 ∧ p2476 ∧ p2477 ∧ p2478)) ∨ (p2478) := by
  classical
  tauto

theorem initial3081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2473)) ∨ (meaning t m 2478) := by
  exact rule3081 (meaning t m 2474) (meaning t m 2475) (meaning t m 2476) (meaning t m 2477) (meaning t m 2478)

theorem rule3083 (p2474 p2475 p2476 p2477 p2478 : Prop) : (p2478) ∨ (((¬ p2478) ∨ (¬ p2477) ∨ (¬ p2475) ∨ (¬ p2476) ∨ (¬ p2474))) := by
  classical
  tauto

theorem initial3083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2478) ∨ (meaning t m 2479) := by
  exact rule3083 (meaning t m 2474) (meaning t m 2475) (meaning t m 2476) (meaning t m 2477) (meaning t m 2478)

theorem rule3085 (p2474 p2475 p2476 p2477 p2478 : Prop) : (p2475) ∨ (((¬ p2478) ∨ (¬ p2477) ∨ (¬ p2475) ∨ (¬ p2476) ∨ (¬ p2474))) := by
  classical
  tauto

theorem initial3085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2475) ∨ (meaning t m 2479) := by
  exact rule3085 (meaning t m 2474) (meaning t m 2475) (meaning t m 2476) (meaning t m 2477) (meaning t m 2478)

theorem rule3087 (p2474 p2475 p2476 p2477 p2478 : Prop) : (p2474) ∨ (((¬ p2478) ∨ (¬ p2477) ∨ (¬ p2475) ∨ (¬ p2476) ∨ (¬ p2474))) := by
  classical
  tauto

theorem initial3087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2474) ∨ (meaning t m 2479) := by
  exact rule3087 (meaning t m 2474) (meaning t m 2475) (meaning t m 2476) (meaning t m 2477) (meaning t m 2478)

theorem rule3089 (p2473 p2479 : Prop) (h : (p2473 ↔ (¬ p2479))) : (¬ p2473) ∨ (¬ p2479) := by
  classical
  tauto

theorem initial3089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2473)) ∨ (¬ (meaning t m 2479)) := by
  have source := ElevenTheory.theory112 t (m.theta 0 4) (m.theta 0 8) (m.theta 4 8)
  exact rule3089 (meaning t m 2473) (meaning t m 2479) source

theorem rule3091 (p2470 p2481 p2482 p2483 p2484 : Prop) : (¬ (p2481 ∧ p2482 ∧ p2470 ∧ p2483 ∧ p2484)) ∨ (p2481) := by
  classical
  tauto

theorem initial3091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2480)) ∨ (meaning t m 2481) := by
  exact rule3091 (meaning t m 2470) (meaning t m 2481) (meaning t m 2482) (meaning t m 2483) (meaning t m 2484)

theorem rule3092 (p2470 p2481 p2482 p2483 p2484 : Prop) : (¬ (p2481 ∧ p2482 ∧ p2470 ∧ p2483 ∧ p2484)) ∨ (p2482) := by
  classical
  tauto

theorem initial3092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2480)) ∨ (meaning t m 2482) := by
  exact rule3092 (meaning t m 2470) (meaning t m 2481) (meaning t m 2482) (meaning t m 2483) (meaning t m 2484)

theorem rule3093 (p2470 p2481 p2482 p2483 p2484 : Prop) : (p2470) ∨ (¬ (p2481 ∧ p2482 ∧ p2470 ∧ p2483 ∧ p2484)) := by
  classical
  tauto

theorem initial3093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2470) ∨ (¬ (meaning t m 2480)) := by
  exact rule3093 (meaning t m 2470) (meaning t m 2481) (meaning t m 2482) (meaning t m 2483) (meaning t m 2484)

theorem rule3095 (p2470 p2481 p2482 p2483 p2484 : Prop) : (¬ (p2481 ∧ p2482 ∧ p2470 ∧ p2483 ∧ p2484)) ∨ (p2484) := by
  classical
  tauto

theorem initial3095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2480)) ∨ (meaning t m 2484) := by
  exact rule3095 (meaning t m 2470) (meaning t m 2481) (meaning t m 2482) (meaning t m 2483) (meaning t m 2484)

theorem rule3100 (p2470 p2481 p2482 p2483 p2484 : Prop) : (p2481) ∨ (((¬ p2470) ∨ (¬ p2483) ∨ (¬ p2484) ∨ (¬ p2481) ∨ (¬ p2482))) := by
  classical
  tauto

theorem initial3100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2481) ∨ (meaning t m 2485) := by
  exact rule3100 (meaning t m 2470) (meaning t m 2481) (meaning t m 2482) (meaning t m 2483) (meaning t m 2484)

theorem rule3101 (p2470 p2481 p2482 p2483 p2484 : Prop) : (p2482) ∨ (((¬ p2470) ∨ (¬ p2483) ∨ (¬ p2484) ∨ (¬ p2481) ∨ (¬ p2482))) := by
  classical
  tauto

theorem initial3101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2482) ∨ (meaning t m 2485) := by
  exact rule3101 (meaning t m 2470) (meaning t m 2481) (meaning t m 2482) (meaning t m 2483) (meaning t m 2484)

theorem rule3103 (p2480 p2485 : Prop) (h : (p2480 ↔ (¬ p2485))) : (¬ p2480) ∨ (¬ p2485) := by
  classical
  tauto

theorem initial3103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2480)) ∨ (¬ (meaning t m 2485)) := by
  have source := ElevenTheory.theory113 t (m.theta 0 4) (m.theta 0 8) (m.theta 4 8)
  exact rule3103 (meaning t m 2480) (meaning t m 2485) source

theorem rule3105 (p386 p392 : Prop) : (¬ p386) ∨ ((p386 ∨ p392)) := by
  classical
  tauto

theorem initial3105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 386)) ∨ (meaning t m 2486) := by
  exact rule3105 (meaning t m 386) (meaning t m 392)

theorem rule3106 (p386 p392 : Prop) : (¬ p392) ∨ ((p386 ∨ p392)) := by
  classical
  tauto

theorem initial3106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 392)) ∨ (meaning t m 2486) := by
  exact rule3106 (meaning t m 386) (meaning t m 392)

theorem rule3123 (p2486 p2487 : Prop) (h : (p2486 ↔ p2487)) : (¬ p2486) ∨ (p2487) := by
  classical
  tauto

theorem initial3123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2486)) ∨ (meaning t m 2487) := by
  have source := ElevenTheory.theory114 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 6)
  exact rule3123 (meaning t m 2486) (meaning t m 2487) source

theorem rule3125 (p2497 p2498 p2499 p2500 p2501 : Prop) : (¬ (p2497 ∧ p2498 ∧ p2499 ∧ p2500 ∧ p2501)) ∨ (p2497) := by
  classical
  tauto

theorem initial3125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2496)) ∨ (meaning t m 2497) := by
  exact rule3125 (meaning t m 2497) (meaning t m 2498) (meaning t m 2499) (meaning t m 2500) (meaning t m 2501)

theorem rule3126 (p2497 p2498 p2499 p2500 p2501 : Prop) : (¬ (p2497 ∧ p2498 ∧ p2499 ∧ p2500 ∧ p2501)) ∨ (p2498) := by
  classical
  tauto

theorem initial3126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2496)) ∨ (meaning t m 2498) := by
  exact rule3126 (meaning t m 2497) (meaning t m 2498) (meaning t m 2499) (meaning t m 2500) (meaning t m 2501)

theorem rule3127 (p2497 p2498 p2499 p2500 p2501 : Prop) : (¬ (p2497 ∧ p2498 ∧ p2499 ∧ p2500 ∧ p2501)) ∨ (p2499) := by
  classical
  tauto

theorem initial3127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2496)) ∨ (meaning t m 2499) := by
  exact rule3127 (meaning t m 2497) (meaning t m 2498) (meaning t m 2499) (meaning t m 2500) (meaning t m 2501)

theorem rule3128 (p2497 p2498 p2499 p2500 p2501 : Prop) : (¬ (p2497 ∧ p2498 ∧ p2499 ∧ p2500 ∧ p2501)) ∨ (p2500) := by
  classical
  tauto

theorem initial3128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2496)) ∨ (meaning t m 2500) := by
  exact rule3128 (meaning t m 2497) (meaning t m 2498) (meaning t m 2499) (meaning t m 2500) (meaning t m 2501)

theorem rule3129 (p2497 p2498 p2499 p2500 p2501 : Prop) : (¬ (p2497 ∧ p2498 ∧ p2499 ∧ p2500 ∧ p2501)) ∨ (p2501) := by
  classical
  tauto

theorem initial3129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2496)) ∨ (meaning t m 2501) := by
  exact rule3129 (meaning t m 2497) (meaning t m 2498) (meaning t m 2499) (meaning t m 2500) (meaning t m 2501)

theorem rule3131 (p2497 p2498 p2499 p2500 p2501 : Prop) : (p2501) ∨ (((¬ p2501) ∨ (¬ p2500) ∨ (¬ p2497) ∨ (¬ p2498) ∨ (¬ p2499))) := by
  classical
  tauto

theorem initial3131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2501) ∨ (meaning t m 2502) := by
  exact rule3131 (meaning t m 2497) (meaning t m 2498) (meaning t m 2499) (meaning t m 2500) (meaning t m 2501)

theorem rule3132 (p2497 p2498 p2499 p2500 p2501 : Prop) : (p2500) ∨ (((¬ p2501) ∨ (¬ p2500) ∨ (¬ p2497) ∨ (¬ p2498) ∨ (¬ p2499))) := by
  classical
  tauto

theorem initial3132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2500) ∨ (meaning t m 2502) := by
  exact rule3132 (meaning t m 2497) (meaning t m 2498) (meaning t m 2499) (meaning t m 2500) (meaning t m 2501)

theorem rule3133 (p2497 p2498 p2499 p2500 p2501 : Prop) : (p2497) ∨ (((¬ p2501) ∨ (¬ p2500) ∨ (¬ p2497) ∨ (¬ p2498) ∨ (¬ p2499))) := by
  classical
  tauto

theorem initial3133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2497) ∨ (meaning t m 2502) := by
  exact rule3133 (meaning t m 2497) (meaning t m 2498) (meaning t m 2499) (meaning t m 2500) (meaning t m 2501)

theorem rule3134 (p2497 p2498 p2499 p2500 p2501 : Prop) : (p2498) ∨ (((¬ p2501) ∨ (¬ p2500) ∨ (¬ p2497) ∨ (¬ p2498) ∨ (¬ p2499))) := by
  classical
  tauto

theorem initial3134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2498) ∨ (meaning t m 2502) := by
  exact rule3134 (meaning t m 2497) (meaning t m 2498) (meaning t m 2499) (meaning t m 2500) (meaning t m 2501)

theorem rule3137 (p2496 p2502 : Prop) (h : (p2496 ↔ (¬ p2502))) : (¬ p2496) ∨ (¬ p2502) := by
  classical
  tauto

theorem initial3137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2496)) ∨ (¬ (meaning t m 2502)) := by
  have source := ElevenTheory.theory115 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 6)
  exact rule3137 (meaning t m 2496) (meaning t m 2502) source

theorem rule3139 (p2493 p2504 p2505 p2506 p2507 : Prop) : (¬ (p2504 ∧ p2505 ∧ p2493 ∧ p2506 ∧ p2507)) ∨ (p2504) := by
  classical
  tauto

theorem initial3139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2503)) ∨ (meaning t m 2504) := by
  exact rule3139 (meaning t m 2493) (meaning t m 2504) (meaning t m 2505) (meaning t m 2506) (meaning t m 2507)

theorem rule3140 (p2493 p2504 p2505 p2506 p2507 : Prop) : (¬ (p2504 ∧ p2505 ∧ p2493 ∧ p2506 ∧ p2507)) ∨ (p2505) := by
  classical
  tauto

theorem initial3140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2503)) ∨ (meaning t m 2505) := by
  exact rule3140 (meaning t m 2493) (meaning t m 2504) (meaning t m 2505) (meaning t m 2506) (meaning t m 2507)

theorem rule3141 (p2493 p2504 p2505 p2506 p2507 : Prop) : (p2493) ∨ (¬ (p2504 ∧ p2505 ∧ p2493 ∧ p2506 ∧ p2507)) := by
  classical
  tauto

theorem initial3141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2493) ∨ (¬ (meaning t m 2503)) := by
  exact rule3141 (meaning t m 2493) (meaning t m 2504) (meaning t m 2505) (meaning t m 2506) (meaning t m 2507)

theorem rule3142 (p2493 p2504 p2505 p2506 p2507 : Prop) : (¬ (p2504 ∧ p2505 ∧ p2493 ∧ p2506 ∧ p2507)) ∨ (p2506) := by
  classical
  tauto

theorem initial3142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2503)) ∨ (meaning t m 2506) := by
  exact rule3142 (meaning t m 2493) (meaning t m 2504) (meaning t m 2505) (meaning t m 2506) (meaning t m 2507)

theorem rule3143 (p2493 p2504 p2505 p2506 p2507 : Prop) : (¬ (p2504 ∧ p2505 ∧ p2493 ∧ p2506 ∧ p2507)) ∨ (p2507) := by
  classical
  tauto

theorem initial3143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2503)) ∨ (meaning t m 2507) := by
  exact rule3143 (meaning t m 2493) (meaning t m 2504) (meaning t m 2505) (meaning t m 2506) (meaning t m 2507)

theorem rule3145 (p2493 p2504 p2505 p2506 p2507 : Prop) : (p2505) ∨ (((¬ p2505) ∨ (¬ p2504) ∨ (¬ p2493) ∨ (¬ p2506) ∨ (¬ p2507))) := by
  classical
  tauto

theorem initial3145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2505) ∨ (meaning t m 2508) := by
  exact rule3145 (meaning t m 2493) (meaning t m 2504) (meaning t m 2505) (meaning t m 2506) (meaning t m 2507)

theorem rule3146 (p2493 p2504 p2505 p2506 p2507 : Prop) : (p2504) ∨ (((¬ p2505) ∨ (¬ p2504) ∨ (¬ p2493) ∨ (¬ p2506) ∨ (¬ p2507))) := by
  classical
  tauto

theorem initial3146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2504) ∨ (meaning t m 2508) := by
  exact rule3146 (meaning t m 2493) (meaning t m 2504) (meaning t m 2505) (meaning t m 2506) (meaning t m 2507)

theorem rule3148 (p2493 p2504 p2505 p2506 p2507 : Prop) : (p2506) ∨ (((¬ p2505) ∨ (¬ p2504) ∨ (¬ p2493) ∨ (¬ p2506) ∨ (¬ p2507))) := by
  classical
  tauto

theorem initial3148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2506) ∨ (meaning t m 2508) := by
  exact rule3148 (meaning t m 2493) (meaning t m 2504) (meaning t m 2505) (meaning t m 2506) (meaning t m 2507)

theorem rule3149 (p2493 p2504 p2505 p2506 p2507 : Prop) : (p2507) ∨ (((¬ p2505) ∨ (¬ p2504) ∨ (¬ p2493) ∨ (¬ p2506) ∨ (¬ p2507))) := by
  classical
  tauto

theorem initial3149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2507) ∨ (meaning t m 2508) := by
  exact rule3149 (meaning t m 2493) (meaning t m 2504) (meaning t m 2505) (meaning t m 2506) (meaning t m 2507)

theorem rule3151 (p2503 p2508 : Prop) (h : (p2503 ↔ (¬ p2508))) : (¬ p2503) ∨ (¬ p2508) := by
  classical
  tauto

theorem initial3151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2503)) ∨ (¬ (meaning t m 2508)) := by
  have source := ElevenTheory.theory116 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 6)
  exact rule3151 (meaning t m 2503) (meaning t m 2508) source

theorem rule3153 (p2493 p2509 p2510 : Prop) (h : (¬ p2509) ∨ (¬ p2510) ∨ (¬ p2493)) : (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2510) := by
  classical
  tauto

theorem initial3153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2510)) := by
  have source := ElevenTheory.theory117 (m.theta 1 4) (m.theta 4 6) (m.theta 4 8)
  exact rule3153 (meaning t m 2493) (meaning t m 2509) (meaning t m 2510) source

theorem rule3154 (p398 p404 : Prop) : (¬ p398) ∨ ((p398 ∨ p404)) := by
  classical
  tauto

theorem initial3154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 398)) ∨ (meaning t m 2511) := by
  exact rule3154 (meaning t m 398) (meaning t m 404)

theorem rule3155 (p398 p404 : Prop) : (¬ p404) ∨ ((p398 ∨ p404)) := by
  classical
  tauto

theorem initial3155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 404)) ∨ (meaning t m 2511) := by
  exact rule3155 (meaning t m 398) (meaning t m 404)

theorem rule3172 (p2511 p2512 : Prop) (h : (p2511 ↔ p2512)) : (¬ p2511) ∨ (p2512) := by
  classical
  tauto

theorem initial3172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2511)) ∨ (meaning t m 2512) := by
  have source := ElevenTheory.theory118 t (m.theta 1 4) (m.theta 1 8) (m.theta 4 8)
  exact rule3172 (meaning t m 2511) (meaning t m 2512) source

theorem rule3174 (p410 p416 : Prop) : (¬ p410) ∨ ((p410 ∨ p416)) := by
  classical
  tauto

theorem initial3174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 410)) ∨ (meaning t m 2521) := by
  exact rule3174 (meaning t m 410) (meaning t m 416)

theorem rule3175 (p410 p416 : Prop) : (¬ p416) ∨ ((p410 ∨ p416)) := by
  classical
  tauto

theorem initial3175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 416)) ∨ (meaning t m 2521) := by
  exact rule3175 (meaning t m 410) (meaning t m 416)

theorem rule3192 (p2521 p2522 : Prop) (h : (p2521 ↔ p2522)) : (¬ p2521) ∨ (p2522) := by
  classical
  tauto

theorem initial3192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2521)) ∨ (meaning t m 2522) := by
  have source := ElevenTheory.theory119 t (m.theta 4 8) (m.theta 4 9) (m.theta 8 9)
  exact rule3192 (meaning t m 2521) (meaning t m 2522) source

theorem rule3194 (p2531 p2532 p2533 p2534 : Prop) (h : (¬ p2531) ∨ (¬ p2532) ∨ (¬ p2533) ∨ (¬ p2534)) : (¬ p2531) ∨ (¬ p2532) ∨ (¬ p2533) ∨ (¬ p2534) := by
  classical
  tauto

theorem initial3194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 2534)) := by
  have source := ElevenTheory.theory120 (m.theta 4 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule3194 (meaning t m 2531) (meaning t m 2532) (meaning t m 2533) (meaning t m 2534) source

theorem rule3195 (p422 p428 : Prop) : (¬ p422) ∨ ((p422 ∨ p428)) := by
  classical
  tauto

theorem initial3195 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 422)) ∨ (meaning t m 2535) := by
  exact rule3195 (meaning t m 422) (meaning t m 428)

theorem rule3196 (p422 p428 : Prop) : (¬ p428) ∨ ((p422 ∨ p428)) := by
  classical
  tauto

theorem initial3196 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 428)) ∨ (meaning t m 2535) := by
  exact rule3196 (meaning t m 422) (meaning t m 428)

theorem rule3213 (p2535 p2536 : Prop) (h : (p2535 ↔ p2536)) : (¬ p2535) ∨ (p2536) := by
  classical
  tauto

theorem initial3213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2535)) ∨ (meaning t m 2536) := by
  have source := ElevenTheory.theory121 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule3213 (meaning t m 2535) (meaning t m 2536) source

theorem rule3215 (p2040 p2545 : Prop) (h : ((¬ p2040) ↔ (¬ p2545))) : (p2040) ∨ (¬ p2545) := by
  classical
  tauto

theorem initial3215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2040) ∨ (¬ (meaning t m 2545)) := by
  have source := ElevenTheory.theory122 t (m.theta 3 4)
  exact rule3215 (meaning t m 2040) (meaning t m 2545) source

theorem rule3217 (p434 p440 : Prop) : (¬ p434) ∨ ((p434 ∨ p440)) := by
  classical
  tauto

theorem initial3217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 434)) ∨ (meaning t m 2546) := by
  exact rule3217 (meaning t m 434) (meaning t m 440)

theorem rule3218 (p434 p440 : Prop) : (¬ p440) ∨ ((p434 ∨ p440)) := by
  classical
  tauto

theorem initial3218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 440)) ∨ (meaning t m 2546) := by
  exact rule3218 (meaning t m 434) (meaning t m 440)

theorem rule3235 (p2546 p2547 : Prop) (h : (p2546 ↔ p2547)) : (¬ p2546) ∨ (p2547) := by
  classical
  tauto

theorem initial3235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2546)) ∨ (meaning t m 2547) := by
  have source := ElevenTheory.theory123 t (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule3235 (meaning t m 2546) (meaning t m 2547) source

theorem rule3237 (p446 p452 : Prop) : (¬ p446) ∨ ((p446 ∨ p452)) := by
  classical
  tauto

theorem initial3237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 446)) ∨ (meaning t m 2556) := by
  exact rule3237 (meaning t m 446) (meaning t m 452)

theorem rule3238 (p446 p452 : Prop) : (¬ p452) ∨ ((p446 ∨ p452)) := by
  classical
  tauto

theorem initial3238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 452)) ∨ (meaning t m 2556) := by
  exact rule3238 (meaning t m 446) (meaning t m 452)

theorem rule3255 (p2556 p2557 : Prop) (h : (p2556 ↔ p2557)) : (¬ p2556) ∨ (p2557) := by
  classical
  tauto

theorem initial3255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2556)) ∨ (meaning t m 2557) := by
  have source := ElevenTheory.theory124 t (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule3255 (meaning t m 2556) (meaning t m 2557) source

theorem rule3257 (p458 p464 : Prop) : (¬ p458) ∨ ((p458 ∨ p464)) := by
  classical
  tauto

theorem initial3257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 458)) ∨ (meaning t m 2566) := by
  exact rule3257 (meaning t m 458) (meaning t m 464)

theorem rule3258 (p458 p464 : Prop) : (¬ p464) ∨ ((p458 ∨ p464)) := by
  classical
  tauto

theorem initial3258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 464)) ∨ (meaning t m 2566) := by
  exact rule3258 (meaning t m 458) (meaning t m 464)

theorem rule3275 (p2566 p2567 : Prop) (h : (p2566 ↔ p2567)) : (¬ p2566) ∨ (p2567) := by
  classical
  tauto

theorem initial3275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2566)) ∨ (meaning t m 2567) := by
  have source := ElevenTheory.theory125 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6)
  exact rule3275 (meaning t m 2566) (meaning t m 2567) source

theorem rule3277 (p2577 p2578 p2579 p2580 p2581 : Prop) : (¬ (p2577 ∧ p2578 ∧ p2579 ∧ p2580 ∧ p2581)) ∨ (p2577) := by
  classical
  tauto

theorem initial3277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2576)) ∨ (meaning t m 2577) := by
  exact rule3277 (meaning t m 2577) (meaning t m 2578) (meaning t m 2579) (meaning t m 2580) (meaning t m 2581)

theorem rule3278 (p2577 p2578 p2579 p2580 p2581 : Prop) : (¬ (p2577 ∧ p2578 ∧ p2579 ∧ p2580 ∧ p2581)) ∨ (p2578) := by
  classical
  tauto

theorem initial3278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2576)) ∨ (meaning t m 2578) := by
  exact rule3278 (meaning t m 2577) (meaning t m 2578) (meaning t m 2579) (meaning t m 2580) (meaning t m 2581)

theorem rule3279 (p2577 p2578 p2579 p2580 p2581 : Prop) : (¬ (p2577 ∧ p2578 ∧ p2579 ∧ p2580 ∧ p2581)) ∨ (p2579) := by
  classical
  tauto

theorem initial3279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2576)) ∨ (meaning t m 2579) := by
  exact rule3279 (meaning t m 2577) (meaning t m 2578) (meaning t m 2579) (meaning t m 2580) (meaning t m 2581)

theorem rule3281 (p2577 p2578 p2579 p2580 p2581 : Prop) : (¬ (p2577 ∧ p2578 ∧ p2579 ∧ p2580 ∧ p2581)) ∨ (p2581) := by
  classical
  tauto

theorem initial3281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2576)) ∨ (meaning t m 2581) := by
  exact rule3281 (meaning t m 2577) (meaning t m 2578) (meaning t m 2579) (meaning t m 2580) (meaning t m 2581)

theorem rule3284 (p2577 p2578 p2579 p2580 p2581 : Prop) : (p2577) ∨ (((¬ p2581) ∨ (¬ p2577) ∨ (¬ p2579) ∨ (¬ p2580) ∨ (¬ p2578))) := by
  classical
  tauto

theorem initial3284 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2577) ∨ (meaning t m 2582) := by
  exact rule3284 (meaning t m 2577) (meaning t m 2578) (meaning t m 2579) (meaning t m 2580) (meaning t m 2581)

theorem rule3287 (p2577 p2578 p2579 p2580 p2581 : Prop) : (p2578) ∨ (((¬ p2581) ∨ (¬ p2577) ∨ (¬ p2579) ∨ (¬ p2580) ∨ (¬ p2578))) := by
  classical
  tauto

theorem initial3287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2578) ∨ (meaning t m 2582) := by
  exact rule3287 (meaning t m 2577) (meaning t m 2578) (meaning t m 2579) (meaning t m 2580) (meaning t m 2581)

theorem rule3289 (p2576 p2582 : Prop) (h : (p2576 ↔ (¬ p2582))) : (¬ p2576) ∨ (¬ p2582) := by
  classical
  tauto

theorem initial3289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2576)) ∨ (¬ (meaning t m 2582)) := by
  have source := ElevenTheory.theory126 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6)
  exact rule3289 (meaning t m 2576) (meaning t m 2582) source

theorem rule3291 (p2386 p2573 p2584 p2585 p2586 : Prop) : (p2386) ∨ (¬ (p2386 ∧ p2584 ∧ p2573 ∧ p2585 ∧ p2586)) := by
  classical
  tauto

theorem initial3291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2386) ∨ (¬ (meaning t m 2583)) := by
  exact rule3291 (meaning t m 2386) (meaning t m 2573) (meaning t m 2584) (meaning t m 2585) (meaning t m 2586)

theorem rule3292 (p2386 p2573 p2584 p2585 p2586 : Prop) : (¬ (p2386 ∧ p2584 ∧ p2573 ∧ p2585 ∧ p2586)) ∨ (p2584) := by
  classical
  tauto

theorem initial3292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2583)) ∨ (meaning t m 2584) := by
  exact rule3292 (meaning t m 2386) (meaning t m 2573) (meaning t m 2584) (meaning t m 2585) (meaning t m 2586)

theorem rule3293 (p2386 p2573 p2584 p2585 p2586 : Prop) : (p2573) ∨ (¬ (p2386 ∧ p2584 ∧ p2573 ∧ p2585 ∧ p2586)) := by
  classical
  tauto

theorem initial3293 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2573) ∨ (¬ (meaning t m 2583)) := by
  exact rule3293 (meaning t m 2386) (meaning t m 2573) (meaning t m 2584) (meaning t m 2585) (meaning t m 2586)

theorem rule3295 (p2386 p2573 p2584 p2585 p2586 : Prop) : (¬ (p2386 ∧ p2584 ∧ p2573 ∧ p2585 ∧ p2586)) ∨ (p2586) := by
  classical
  tauto

theorem initial3295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2583)) ∨ (meaning t m 2586) := by
  exact rule3295 (meaning t m 2386) (meaning t m 2573) (meaning t m 2584) (meaning t m 2585) (meaning t m 2586)

theorem rule3297 (p2386 p2573 p2584 p2585 p2586 : Prop) : (p2584) ∨ (((¬ p2584) ∨ (¬ p2573) ∨ (¬ p2386) ∨ (¬ p2586) ∨ (¬ p2585))) := by
  classical
  tauto

theorem initial3297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2584) ∨ (meaning t m 2587) := by
  exact rule3297 (meaning t m 2386) (meaning t m 2573) (meaning t m 2584) (meaning t m 2585) (meaning t m 2586)

theorem rule3299 (p2386 p2573 p2584 p2585 p2586 : Prop) : (p2386) ∨ (((¬ p2584) ∨ (¬ p2573) ∨ (¬ p2386) ∨ (¬ p2586) ∨ (¬ p2585))) := by
  classical
  tauto

theorem initial3299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2386) ∨ (meaning t m 2587) := by
  exact rule3299 (meaning t m 2386) (meaning t m 2573) (meaning t m 2584) (meaning t m 2585) (meaning t m 2586)

theorem rule3303 (p2583 p2587 : Prop) (h : (p2583 ↔ (¬ p2587))) : (¬ p2583) ∨ (¬ p2587) := by
  classical
  tauto

theorem initial3303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2583)) ∨ (¬ (meaning t m 2587)) := by
  have source := ElevenTheory.theory127 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6)
  exact rule3303 (meaning t m 2583) (meaning t m 2587) source

theorem rule3305 (p2318 p2319 p2578 p2588 : Prop) (h : (¬ p2318) ∨ (¬ p2578) ∨ (¬ p2319) ∨ (¬ p2588)) : (¬ p2318) ∨ (¬ p2319) ∨ (¬ p2578) ∨ (¬ p2588) := by
  classical
  tauto

theorem initial3305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 2588)) := by
  have source := ElevenTheory.theory128 (m.theta 0 6) (m.theta 0 7) (m.theta 4 6) (m.theta 6 7)
  exact rule3305 (meaning t m 2318) (meaning t m 2319) (meaning t m 2578) (meaning t m 2588) source

theorem rule3306 (p2573 p2589 p2590 : Prop) (h : (¬ p2589) ∨ (¬ p2590) ∨ (¬ p2573)) : (¬ p2573) ∨ (¬ p2589) ∨ (¬ p2590) := by
  classical
  tauto

theorem initial3306 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2590)) := by
  have source := ElevenTheory.theory129 (m.theta 0 4) (m.theta 4 5) (m.theta 4 6)
  exact rule3306 (meaning t m 2573) (meaning t m 2589) (meaning t m 2590) source

theorem rule3307 (p470 p476 : Prop) : (¬ p470) ∨ ((p470 ∨ p476)) := by
  classical
  tauto

theorem initial3307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 470)) ∨ (meaning t m 2591) := by
  exact rule3307 (meaning t m 470) (meaning t m 476)

theorem rule3308 (p470 p476 : Prop) : (¬ p476) ∨ ((p470 ∨ p476)) := by
  classical
  tauto

theorem initial3308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 476)) ∨ (meaning t m 2591) := by
  exact rule3308 (meaning t m 470) (meaning t m 476)

theorem rule3325 (p2591 p2592 : Prop) (h : (p2591 ↔ p2592)) : (¬ p2591) ∨ (p2592) := by
  classical
  tauto

theorem initial3325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2591)) ∨ (meaning t m 2592) := by
  have source := ElevenTheory.theory130 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4)
  exact rule3325 (meaning t m 2591) (meaning t m 2592) source

theorem rule3327 (p482 p488 : Prop) : (¬ p482) ∨ ((p482 ∨ p488)) := by
  classical
  tauto

theorem initial3327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 482)) ∨ (meaning t m 2601) := by
  exact rule3327 (meaning t m 482) (meaning t m 488)

theorem rule3328 (p482 p488 : Prop) : (¬ p488) ∨ ((p482 ∨ p488)) := by
  classical
  tauto

theorem initial3328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 488)) ∨ (meaning t m 2601) := by
  exact rule3328 (meaning t m 482) (meaning t m 488)

theorem rule3345 (p2601 p2602 : Prop) (h : (p2601 ↔ p2602)) : (¬ p2601) ∨ (p2602) := by
  classical
  tauto

theorem initial3345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2601)) ∨ (meaning t m 2602) := by
  have source := ElevenTheory.theory131 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2)
  exact rule3345 (meaning t m 2601) (meaning t m 2602) source

theorem rule3347 (p2041 p2611 : Prop) (h : ((¬ p2041) ↔ (¬ p2611))) : (p2041) ∨ (¬ p2611) := by
  classical
  tauto

theorem initial3347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2041) ∨ (¬ (meaning t m 2611)) := by
  have source := ElevenTheory.theory132 t (m.theta 0 2)
  exact rule3347 (meaning t m 2041) (meaning t m 2611) source

theorem rule3349 (p494 p500 : Prop) : (¬ p494) ∨ ((p494 ∨ p500)) := by
  classical
  tauto

theorem initial3349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 494)) ∨ (meaning t m 2612) := by
  exact rule3349 (meaning t m 494) (meaning t m 500)

theorem rule3350 (p494 p500 : Prop) : (¬ p500) ∨ ((p494 ∨ p500)) := by
  classical
  tauto

theorem initial3350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 500)) ∨ (meaning t m 2612) := by
  exact rule3350 (meaning t m 494) (meaning t m 500)

theorem rule3367 (p2612 p2613 : Prop) (h : (p2612 ↔ p2613)) : (¬ p2612) ∨ (p2613) := by
  classical
  tauto

theorem initial3367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2612)) ∨ (meaning t m 2613) := by
  have source := ElevenTheory.theory133 t (m.theta 2 5) (m.theta 2 8) (m.theta 5 8)
  exact rule3367 (meaning t m 2612) (meaning t m 2613) source

theorem rule3369 (p2042 p2622 : Prop) (h : ((¬ p2042) ↔ (¬ p2622))) : (p2042) ∨ (¬ p2622) := by
  classical
  tauto

theorem initial3369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2042) ∨ (¬ (meaning t m 2622)) := by
  have source := ElevenTheory.theory134 t (m.theta 2 3)
  exact rule3369 (meaning t m 2042) (meaning t m 2622) source

theorem rule3371 (p506 p512 : Prop) : (¬ p506) ∨ ((p506 ∨ p512)) := by
  classical
  tauto

theorem initial3371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 506)) ∨ (meaning t m 2623) := by
  exact rule3371 (meaning t m 506) (meaning t m 512)

theorem rule3372 (p506 p512 : Prop) : (¬ p512) ∨ ((p506 ∨ p512)) := by
  classical
  tauto

theorem initial3372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 512)) ∨ (meaning t m 2623) := by
  exact rule3372 (meaning t m 506) (meaning t m 512)

theorem rule3389 (p2623 p2624 : Prop) (h : (p2623 ↔ p2624)) : (¬ p2623) ∨ (p2624) := by
  classical
  tauto

theorem initial3389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2623)) ∨ (meaning t m 2624) := by
  have source := ElevenTheory.theory135 t (m.theta 2 3) (m.theta 2 4) (m.theta 3 4)
  exact rule3389 (meaning t m 2623) (meaning t m 2624) source

theorem rule3391 (p2043 p2633 : Prop) (h : ((¬ p2043) ↔ (¬ p2633))) : (p2043) ∨ (¬ p2633) := by
  classical
  tauto

theorem initial3391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2043) ∨ (¬ (meaning t m 2633)) := by
  have source := ElevenTheory.theory136 t (m.theta 7 8)
  exact rule3391 (meaning t m 2043) (meaning t m 2633) source

theorem rule3393 (p518 p524 : Prop) : (¬ p518) ∨ ((p518 ∨ p524)) := by
  classical
  tauto

theorem initial3393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 518)) ∨ (meaning t m 2634) := by
  exact rule3393 (meaning t m 518) (meaning t m 524)

theorem rule3394 (p518 p524 : Prop) : (¬ p524) ∨ ((p518 ∨ p524)) := by
  classical
  tauto

theorem initial3394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 524)) ∨ (meaning t m 2634) := by
  exact rule3394 (meaning t m 518) (meaning t m 524)

theorem rule3411 (p2634 p2635 : Prop) (h : (p2634 ↔ p2635)) : (¬ p2634) ∨ (p2635) := by
  classical
  tauto

theorem initial3411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2634)) ∨ (meaning t m 2635) := by
  have source := ElevenTheory.theory137 t (m.theta 1 3) (m.theta 1 6) (m.theta 3 6)
  exact rule3411 (meaning t m 2634) (meaning t m 2635) source

theorem rule3413 (p530 p536 : Prop) : (¬ p530) ∨ ((p530 ∨ p536)) := by
  classical
  tauto

theorem initial3413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 530)) ∨ (meaning t m 2644) := by
  exact rule3413 (meaning t m 530) (meaning t m 536)

theorem rule3414 (p530 p536 : Prop) : (¬ p536) ∨ ((p530 ∨ p536)) := by
  classical
  tauto

theorem initial3414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 536)) ∨ (meaning t m 2644) := by
  exact rule3414 (meaning t m 530) (meaning t m 536)

theorem rule3431 (p2644 p2645 : Prop) (h : (p2644 ↔ p2645)) : (¬ p2644) ∨ (p2645) := by
  classical
  tauto

theorem initial3431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2644)) ∨ (meaning t m 2645) := by
  have source := ElevenTheory.theory138 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4)
  exact rule3431 (meaning t m 2644) (meaning t m 2645) source

theorem rule3433 (p2655 p2656 p2657 p2658 p2659 : Prop) : (¬ (p2655 ∧ p2656 ∧ p2657 ∧ p2658 ∧ p2659)) ∨ (p2655) := by
  classical
  tauto

theorem initial3433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2654)) ∨ (meaning t m 2655) := by
  exact rule3433 (meaning t m 2655) (meaning t m 2656) (meaning t m 2657) (meaning t m 2658) (meaning t m 2659)

theorem rule3434 (p2655 p2656 p2657 p2658 p2659 : Prop) : (¬ (p2655 ∧ p2656 ∧ p2657 ∧ p2658 ∧ p2659)) ∨ (p2656) := by
  classical
  tauto

theorem initial3434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2654)) ∨ (meaning t m 2656) := by
  exact rule3434 (meaning t m 2655) (meaning t m 2656) (meaning t m 2657) (meaning t m 2658) (meaning t m 2659)

theorem rule3435 (p2655 p2656 p2657 p2658 p2659 : Prop) : (¬ (p2655 ∧ p2656 ∧ p2657 ∧ p2658 ∧ p2659)) ∨ (p2657) := by
  classical
  tauto

theorem initial3435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2654)) ∨ (meaning t m 2657) := by
  exact rule3435 (meaning t m 2655) (meaning t m 2656) (meaning t m 2657) (meaning t m 2658) (meaning t m 2659)

theorem rule3437 (p2655 p2656 p2657 p2658 p2659 : Prop) : (¬ (p2655 ∧ p2656 ∧ p2657 ∧ p2658 ∧ p2659)) ∨ (p2659) := by
  classical
  tauto

theorem initial3437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2654)) ∨ (meaning t m 2659) := by
  exact rule3437 (meaning t m 2655) (meaning t m 2656) (meaning t m 2657) (meaning t m 2658) (meaning t m 2659)

theorem rule3439 (p2655 p2656 p2657 p2658 p2659 : Prop) : (p2659) ∨ (((¬ p2659) ∨ (¬ p2658) ∨ (¬ p2656) ∨ (¬ p2655) ∨ (¬ p2657))) := by
  classical
  tauto

theorem initial3439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2659) ∨ (meaning t m 2660) := by
  exact rule3439 (meaning t m 2655) (meaning t m 2656) (meaning t m 2657) (meaning t m 2658) (meaning t m 2659)

theorem rule3441 (p2655 p2656 p2657 p2658 p2659 : Prop) : (p2656) ∨ (((¬ p2659) ∨ (¬ p2658) ∨ (¬ p2656) ∨ (¬ p2655) ∨ (¬ p2657))) := by
  classical
  tauto

theorem initial3441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2656) ∨ (meaning t m 2660) := by
  exact rule3441 (meaning t m 2655) (meaning t m 2656) (meaning t m 2657) (meaning t m 2658) (meaning t m 2659)

theorem rule3442 (p2655 p2656 p2657 p2658 p2659 : Prop) : (p2655) ∨ (((¬ p2659) ∨ (¬ p2658) ∨ (¬ p2656) ∨ (¬ p2655) ∨ (¬ p2657))) := by
  classical
  tauto

theorem initial3442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2655) ∨ (meaning t m 2660) := by
  exact rule3442 (meaning t m 2655) (meaning t m 2656) (meaning t m 2657) (meaning t m 2658) (meaning t m 2659)

theorem rule3445 (p2654 p2660 : Prop) (h : (p2654 ↔ (¬ p2660))) : (¬ p2654) ∨ (¬ p2660) := by
  classical
  tauto

theorem initial3445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2654)) ∨ (¬ (meaning t m 2660)) := by
  have source := ElevenTheory.theory139 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4)
  exact rule3445 (meaning t m 2654) (meaning t m 2660) source

theorem rule3447 (p2651 p2662 p2663 p2664 p2665 : Prop) : (¬ (p2662 ∧ p2663 ∧ p2651 ∧ p2664 ∧ p2665)) ∨ (p2662) := by
  classical
  tauto

theorem initial3447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2661)) ∨ (meaning t m 2662) := by
  exact rule3447 (meaning t m 2651) (meaning t m 2662) (meaning t m 2663) (meaning t m 2664) (meaning t m 2665)

theorem rule3448 (p2651 p2662 p2663 p2664 p2665 : Prop) : (¬ (p2662 ∧ p2663 ∧ p2651 ∧ p2664 ∧ p2665)) ∨ (p2663) := by
  classical
  tauto

theorem initial3448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2661)) ∨ (meaning t m 2663) := by
  exact rule3448 (meaning t m 2651) (meaning t m 2662) (meaning t m 2663) (meaning t m 2664) (meaning t m 2665)

theorem rule3449 (p2651 p2662 p2663 p2664 p2665 : Prop) : (p2651) ∨ (¬ (p2662 ∧ p2663 ∧ p2651 ∧ p2664 ∧ p2665)) := by
  classical
  tauto

theorem initial3449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2651) ∨ (¬ (meaning t m 2661)) := by
  exact rule3449 (meaning t m 2651) (meaning t m 2662) (meaning t m 2663) (meaning t m 2664) (meaning t m 2665)

theorem rule3450 (p2651 p2662 p2663 p2664 p2665 : Prop) : (¬ (p2662 ∧ p2663 ∧ p2651 ∧ p2664 ∧ p2665)) ∨ (p2664) := by
  classical
  tauto

theorem initial3450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2661)) ∨ (meaning t m 2664) := by
  exact rule3450 (meaning t m 2651) (meaning t m 2662) (meaning t m 2663) (meaning t m 2664) (meaning t m 2665)

theorem rule3451 (p2651 p2662 p2663 p2664 p2665 : Prop) : (¬ (p2662 ∧ p2663 ∧ p2651 ∧ p2664 ∧ p2665)) ∨ (p2665) := by
  classical
  tauto

theorem initial3451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2661)) ∨ (meaning t m 2665) := by
  exact rule3451 (meaning t m 2651) (meaning t m 2662) (meaning t m 2663) (meaning t m 2664) (meaning t m 2665)

theorem rule3453 (p2651 p2662 p2663 p2664 p2665 : Prop) : (p2663) ∨ (((¬ p2663) ∨ (¬ p2651) ∨ (¬ p2662) ∨ (¬ p2665) ∨ (¬ p2664))) := by
  classical
  tauto

theorem initial3453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2663) ∨ (meaning t m 2666) := by
  exact rule3453 (meaning t m 2651) (meaning t m 2662) (meaning t m 2663) (meaning t m 2664) (meaning t m 2665)

theorem rule3455 (p2651 p2662 p2663 p2664 p2665 : Prop) : (p2662) ∨ (((¬ p2663) ∨ (¬ p2651) ∨ (¬ p2662) ∨ (¬ p2665) ∨ (¬ p2664))) := by
  classical
  tauto

theorem initial3455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2662) ∨ (meaning t m 2666) := by
  exact rule3455 (meaning t m 2651) (meaning t m 2662) (meaning t m 2663) (meaning t m 2664) (meaning t m 2665)

theorem rule3459 (p2661 p2666 : Prop) (h : (p2661 ↔ (¬ p2666))) : (¬ p2661) ∨ (¬ p2666) := by
  classical
  tauto

theorem initial3459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2661)) ∨ (¬ (meaning t m 2666)) := by
  have source := ElevenTheory.theory140 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4)
  exact rule3459 (meaning t m 2661) (meaning t m 2666) source

theorem rule3461 (p2387 p2667 p2668 : Prop) (h : (¬ p2667) ∨ (¬ p2387) ∨ (¬ p2668)) : (¬ p2387) ∨ (¬ p2667) ∨ (¬ p2668) := by
  classical
  tauto

theorem initial3461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2668)) := by
  have source := ElevenTheory.theory141 (m.theta 0 6) (m.theta 3 6) (m.theta 6 8)
  exact rule3461 (meaning t m 2387) (meaning t m 2667) (meaning t m 2668) source

theorem rule3462 (p542 p548 : Prop) : (¬ p542) ∨ ((p542 ∨ p548)) := by
  classical
  tauto

theorem initial3462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 542)) ∨ (meaning t m 2669) := by
  exact rule3462 (meaning t m 542) (meaning t m 548)

theorem rule3463 (p542 p548 : Prop) : (¬ p548) ∨ ((p542 ∨ p548)) := by
  classical
  tauto

theorem initial3463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 548)) ∨ (meaning t m 2669) := by
  exact rule3463 (meaning t m 542) (meaning t m 548)

theorem rule3480 (p2669 p2670 : Prop) (h : (p2669 ↔ p2670)) : (¬ p2669) ∨ (p2670) := by
  classical
  tauto

theorem initial3480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2669)) ∨ (meaning t m 2670) := by
  have source := ElevenTheory.theory142 t (m.theta 3 6) (m.theta 3 8) (m.theta 6 8)
  exact rule3480 (meaning t m 2669) (meaning t m 2670) source

theorem rule3482 (p554 p560 : Prop) : (¬ p554) ∨ ((p554 ∨ p560)) := by
  classical
  tauto

theorem initial3482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 554)) ∨ (meaning t m 2678) := by
  exact rule3482 (meaning t m 554) (meaning t m 560)

theorem rule3483 (p554 p560 : Prop) : (¬ p560) ∨ ((p554 ∨ p560)) := by
  classical
  tauto

theorem initial3483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 560)) ∨ (meaning t m 2678) := by
  exact rule3483 (meaning t m 554) (meaning t m 560)

theorem rule3500 (p2678 p2679 : Prop) (h : (p2678 ↔ p2679)) : (¬ p2678) ∨ (p2679) := by
  classical
  tauto

theorem initial3500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2678)) ∨ (meaning t m 2679) := by
  have source := ElevenTheory.theory143 t (m.theta 2 3) (m.theta 2 7) (m.theta 3 7)
  exact rule3500 (meaning t m 2678) (meaning t m 2679) source

end SunPrize.SMT
