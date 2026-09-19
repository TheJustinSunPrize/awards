import SunPrize.Certificate.Derived081
import SunPrize.Certificate.Logic082
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived132038 (p : Nat → Prop) (h : Inputs p) :
    (p 2352) ∨ (¬ p 2177) ∨ (¬ p 2363) ∨ (¬ p 2651) ∨ (p 2553) :=
  ElevenRUP.step132038 (p 2098) (p 2132) (p 2137) (p 2156) (p 2166) (p 2177) (p 2187) (p 2220) (p 2274) (p 2284) (p 2331) (p 2341) (p 2352) (p 2363) (p 2406) (p 2459) (p 2493) (p 2553) (p 2563) (p 2608) (p 2619) (p 2630) (p 2641) (p 2651) (p 2696) (p 2707) (p 2727) (p 2737) (p 2748) (p 2749) (p 2797) (p 2829) (p 2839) (p 2850) (p 2870) (p 2881) (p 2901) (p 2911) (p 2946) (p 3125) (p 3146) (p 3156) (p 3201) (p 3323) (p 3367) (p 3371) (p 3379) (p 3422) (p 3425) (p 3541) (p 3577) (p 3581) (p 3747) (p 3873) (p 4169) (p 4281) (p 5083) (derived132015 p h) (derived132006 p h) (derived131645 p h) (derived132018 p h) (derived130735 p h) (derived131647 p h) (derived131182 p h) (derived131646 p h) (derived131998 p h) (derived131921 p h) (derived102249 p h) (derived132026 p h) (derived125321 p h) (derived104526 p h) (derived132027 p h) (derived116567 p h) (derived120332 p h) (derived113198 p h) (derived129728 p h) (derived95899 p h) (h 31669) (derived130369 p h) (derived102427 p h) (derived96372 p h) (derived107095 p h) (derived132033 p h) (derived91585 p h) (h 23469) (derived103244 p h) (derived78229 p h) (derived77708 p h) (derived99313 p h) (derived99321 p h) (derived77109 p h) (derived101920 p h) (derived116469 p h) (derived96166 p h) (derived132037 p h) (derived96359 p h) (derived132036 p h) (h 6913) (h 26059) (derived125336 p h) (derived130846 p h) (derived119362 p h) (derived96362 p h) (derived102867 p h) (derived82804 p h) (derived115431 p h) (derived125551 p h) (derived120670 p h) (derived124846 p h) (derived79125 p h)

theorem derived132039 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2352) ∨ (¬ p 2363) ∨ (¬ p 2651) ∨ (p 2553) :=
  ElevenRUP.step132039 (p 2132) (p 2137) (p 2156) (p 2187) (p 2246) (p 2331) (p 2352) (p 2363) (p 2437) (p 2553) (p 2563) (p 2608) (p 2619) (p 2630) (p 2651) (p 2696) (p 2727) (p 2737) (p 2811) (p 2839) (p 2881) (p 2946) (p 3016) (p 3146) (p 3581) (p 3873) (derived131998 p h) (derived132015 p h) (derived132006 p h) (derived131999 p h) (derived131645 p h) (derived132005 p h) (derived130735 p h) (derived132027 p h) (derived102249 p h) (derived132026 p h) (derived102427 p h) (derived125321 p h) (derived104526 p h) (derived120332 p h) (derived131735 p h) (derived43763 p h) (derived103131 p h) (derived132028 p h) (derived131812 p h) (derived132036 p h) (derived46020 p h) (derived125336 p h) (derived102867 p h)

theorem derived132040 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) ∨ (¬ p 2651) ∨ (p 2553) :=
  ElevenRUP.step132040 (p 2132) (p 2136) (p 2166) (p 2177) (p 2220) (p 2274) (p 2284) (p 2352) (p 2363) (p 2373) (p 2406) (p 2493) (p 2553) (p 2563) (p 2608) (p 2619) (p 2630) (p 2651) (p 2696) (p 2727) (p 2737) (p 2749) (p 2811) (p 2839) (p 2850) (p 2946) (p 2958) (p 2992) (p 3016) (p 3136) (p 3146) (p 3156) (p 3309) (p 3367) (p 3371) (p 3379) (p 3541) (p 3581) (p 3660) (p 3873) (p 4203) (p 4236) (p 4281) (p 5191) (derived131647 p h) (derived132006 p h) (derived132015 p h) (derived132021 p h) (derived131182 p h) (derived130737 p h) (derived130736 p h) (derived132018 p h) (derived130735 p h) (derived131998 p h) (derived132000 p h) (derived131645 p h) (derived131999 p h) (derived120332 p h) (derived113198 p h) (derived129728 p h) (derived125321 p h) (derived104526 p h) (derived96372 p h) (derived95899 p h) (h 31669) (derived102249 p h) (derived132026 p h) (derived102521 p h) (derived130369 p h) (derived129216 p h) (derived132027 p h) (derived132039 p h) (derived132038 p h) (derived125595 p h) (derived103294 p h) (derived79801 p h) (derived132032 p h) (derived103244 p h) (derived85729 p h) (derived91585 p h) (derived103692 p h) (derived83726 p h) (derived58637 p h) (derived84333 p h) (derived79109 p h) (derived96895 p h)

theorem derived132041 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2651) ∨ (p 2553) :=
  ElevenRUP.step132041 (p 2177) (p 2352) (p 2363) (p 2406) (p 2459) (p 2493) (p 2505) (p 2553) (p 2598) (p 2608) (p 2630) (p 2651) (p 2696) (p 2727) (p 2737) (p 2749) (p 2829) (p 2850) (p 2881) (p 3063) (p 3093) (p 3367) (p 3379) (p 3422) (p 3541) (p 3550) (p 3873) (p 3923) (p 4281) (p 4870) (p 4992) (derived132006 p h) (derived131647 p h) (derived132015 p h) (derived131921 p h) (derived132018 p h) (derived131998 p h) (derived131645 p h) (derived125321 p h) (derived120332 p h) (derived95899 p h) (derived113198 p h) (derived107095 p h) (h 31669) (derived129728 p h) (derived102586 p h) (derived96029 p h) (derived132040 p h) (derived74478 p h) (derived125400 p h) (derived80464 p h) (derived96472 p h) (derived131735 p h) (h 8334) (derived79801 p h) (derived108969 p h) (derived96943 p h) (derived120583 p h) (derived120564 p h) (derived81128 p h) (derived82549 p h)

theorem derived132042 (p : Nat → Prop) (h : Inputs p) :
    (p 2553) :=
  ElevenRUP.step132042 (p 2132) (p 2136) (p 2137) (p 2241) (p 2264) (p 2295) (p 2331) (p 2341) (p 2427) (p 2459) (p 2553) (p 2598) (p 2630) (p 2641) (p 2651) (p 2685) (p 2696) (p 2707) (p 2737) (p 2748) (p 2749) (p 2797) (p 2807) (p 2829) (p 2839) (p 2850) (p 2870) (p 2881) (p 2946) (p 3016) (p 3019) (p 3051) (p 3246) (p 3367) (p 3422) (p 3425) (p 3434) (p 3516) (p 3577) (p 3587) (p 3873) (p 4357) (p 4841) (p 4988) (derived131647 p h) (derived131645 p h) (derived132004 p h) (derived131921 p h) (derived131998 p h) (derived131646 p h) (derived132015 p h) (derived132041 p h) (derived129395 p h) (derived129396 p h) (derived130974 p h) (derived131033 p h) (derived117846 p h) (derived107098 p h) (derived129429 p h) (derived129740 p h) (derived87375 p h) (derived82677 p h) (derived129343 p h) (derived102427 p h) (derived102521 p h) (derived129707 p h) (derived102194 p h) (derived82804 p h) (derived82527 p h) (derived102054 p h) (derived101604 p h) (derived111165 p h) (derived126098 p h) (derived115087 p h) (derived82904 p h) (derived131207 p h) (derived102334 p h) (derived83665 p h) (derived96166 p h) (derived126603 p h) (derived83673 p h) (derived102490 p h) (derived46036 p h) (derived104070 p h) (derived126903 p h) (derived114176 p h) (derived120432 p h) (derived122028 p h)

theorem derived132044 (p : Nat → Prop) (h : Inputs p) :
    (p 3920) :=
  ElevenRUP.step132044 (p 2553) (p 3920) (derived132042 p h) (derived94485 p h)

theorem derived132045 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) :=
  ElevenRUP.step132045 (p 2274) (p 2437) (p 2553) (derived132042 p h) (derived131182 p h) (derived129377 p h)

theorem derived132054 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2363) :=
  ElevenRUP.step132054 (p 2241) (p 2363) (p 2553) (derived132042 p h) (derived132004 p h) (derived129258 p h)

theorem derived132058 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3016) :=
  ElevenRUP.step132058 (p 2437) (p 3016) (p 3920) (derived132045 p h) (derived132044 p h) (derived114302 p h)

theorem derived132081 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3550) :=
  ElevenRUP.step132081 (p 2363) (p 2459) (p 3550) (derived132054 p h) (derived131921 p h) (derived74478 p h)

theorem derived132082 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2881) :=
  ElevenRUP.step132082 (p 2363) (p 2459) (p 2881) (derived132054 p h) (derived131921 p h) (derived125400 p h)

theorem derived132091 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3093) :=
  ElevenRUP.step132091 (p 3016) (p 3093) (p 3379) (derived132058 p h) (derived132018 p h) (derived130761 p h)

theorem derived132104 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) :=
  ElevenRUP.step132104 (p 2177) (p 3550) (derived132081 p h) (derived96472 p h)

theorem derived132106 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2911) :=
  ElevenRUP.step132106 (p 2274) (p 2553) (p 2881) (p 2911) (derived132082 p h) (derived131182 p h) (derived132042 p h) (derived125828 p h)

theorem derived132121 (p : Nat → Prop) (h : Inputs p) :
    (p 2295) :=
  ElevenRUP.step132121 (p 2295) (p 2553) (p 3093) (derived132091 p h) (derived132042 p h) (derived103846 p h)

theorem derived132128 (p : Nat → Prop) (h : Inputs p) :
    (p 3955) :=
  ElevenRUP.step132128 (p 2177) (p 3955) (derived132104 p h) (derived78596 p h)

theorem derived132134 (p : Nat → Prop) (h : Inputs p) :
    (p 2630) :=
  ElevenRUP.step132134 (p 2437) (p 2630) (p 2696) (p 2911) (derived132106 p h) (derived132045 p h) (derived131998 p h) (derived82675 p h)

theorem derived132148 (p : Nat → Prop) (h : Inputs p) :
    (p 2668) :=
  ElevenRUP.step132148 (p 2295) (p 2363) (p 2459) (p 2668) (derived132121 p h) (derived132054 p h) (derived131921 p h) (derived79363 p h)

theorem derived132149 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2331) :=
  ElevenRUP.step132149 (p 2274) (p 2295) (p 2331) (p 2737) (p 2811) (derived132121 p h) (derived131999 p h) (derived131182 p h) (derived131645 p h) (derived81874 p h)

theorem derived132158 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2187) :=
  ElevenRUP.step132158 (p 2187) (p 2274) (p 3955) (derived132128 p h) (derived131182 p h) (derived78588 p h)

theorem derived132168 (p : Nat → Prop) (h : Inputs p) :
    (p 2651) :=
  ElevenRUP.step132168 (p 2630) (p 2651) (p 2737) (derived132134 p h) (derived131645 p h) (derived131033 p h)

theorem derived132191 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3166) :=
  ElevenRUP.step132191 (p 2187) (p 2331) (p 2668) (p 3166) (derived132148 p h) (derived132149 p h) (derived132158 p h) (derived112323 p h)

theorem derived132207 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3256) :=
  ElevenRUP.step132207 (p 2187) (p 2363) (p 3256) (derived132158 p h) (derived132054 p h) (derived117577 p h)

theorem derived132253 (p : Nat → Prop) (h : Inputs p) :
    False :=
  ElevenRUP.step132253 (p 2459) (p 2651) (p 3166) (p 3256) (derived132207 p h) (derived132191 p h) (derived131921 p h) (derived132168 p h) (derived100966 p h)

end ElevenLogic
