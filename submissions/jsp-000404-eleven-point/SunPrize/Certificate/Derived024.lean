import SunPrize.Certificate.Derived023
import SunPrize.Certificate.Logic024
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ElevenLogic

theorem derived65771 (p : Nat → Prop) (h : Inputs p) :
    (p 4605) :=
  ElevenRUP.step65771 (p 2367) (p 4605) (derived65770 p h) (h 7356)

theorem derived65772 (p : Nat → Prop) (h : Inputs p) :
    (p 5838) :=
  ElevenRUP.step65772 (p 4605) (p 5838) (derived65771 p h) (h 12044)

theorem derived65773 (p : Nat → Prop) (h : Inputs p) :
    (p 2521) :=
  ElevenRUP.step65773 (p 410) (p 416) (p 2521) (h 3174) (h 3175) (h 456)

theorem derived65774 (p : Nat → Prop) (h : Inputs p) :
    (p 2522) :=
  ElevenRUP.step65774 (p 2521) (p 2522) (derived65773 p h) (h 3192)

theorem derived65775 (p : Nat → Prop) (h : Inputs p) :
    (p 4691) :=
  ElevenRUP.step65775 (p 2522) (p 4691) (derived65774 p h) (h 7580)

theorem derived65776 (p : Nat → Prop) (h : Inputs p) :
    (p 5868) :=
  ElevenRUP.step65776 (p 4691) (p 5868) (derived65775 p h) (h 12220)

theorem derived65778 (p : Nat → Prop) (h : Inputs p) :
    (p 2556) :=
  ElevenRUP.step65778 (p 446) (p 452) (p 2556) (h 3237) (h 3238) (h 495)

theorem derived65779 (p : Nat → Prop) (h : Inputs p) :
    (p 2557) :=
  ElevenRUP.step65779 (p 2556) (p 2557) (derived65778 p h) (h 3255)

theorem derived65780 (p : Nat → Prop) (h : Inputs p) :
    (p 4713) :=
  ElevenRUP.step65780 (p 2557) (p 4713) (derived65779 p h) (h 7631)

theorem derived65781 (p : Nat → Prop) (h : Inputs p) :
    (p 5877) :=
  ElevenRUP.step65781 (p 4713) (p 5877) (derived65780 p h) (h 12272)

theorem derived65782 (p : Nat → Prop) (h : Inputs p) :
    (p 2420) :=
  ElevenRUP.step65782 (p 326) (p 332) (p 2420) (h 2974) (h 2975) (h 365)

theorem derived65783 (p : Nat → Prop) (h : Inputs p) :
    (p 2421) :=
  ElevenRUP.step65783 (p 2420) (p 2421) (derived65782 p h) (h 2992)

theorem derived65784 (p : Nat → Prop) (h : Inputs p) :
    (p 4642) :=
  ElevenRUP.step65784 (p 2421) (p 4642) (derived65783 p h) (h 7442)

theorem derived65785 (p : Nat → Prop) (h : Inputs p) :
    (p 5853) :=
  ElevenRUP.step65785 (p 4642) (p 5853) (derived65784 p h) (h 12132)

theorem derived65786 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3266) ∨ (¬ p 2881) ∨ (¬ p 2373) ∨ (¬ p 3146) ∨ (¬ p 2459) :=
  ElevenRUP.step65786 (p 2373) (p 2427) (p 2459) (p 2881) (p 3146) (p 3266) (p 4235) (p 4642) (p 4643) (p 4645) (derived65784 p h) (derived51791 p h) (derived60656 p h) (h 7435) (h 7429) (h 7441)

theorem derived65788 (p : Nat → Prop) (h : Inputs p) :
    (p 4559) ∨ (¬ p 2881) :=
  ElevenRUP.step65788 (p 2177) (p 2881) (p 4275) (p 4553) (p 4554) (p 4557) (p 4559) (derived65724 p h) (h 7210) (derived46823 p h) (h 7214) (h 6838) (h 7201)

theorem derived65789 (p : Nat → Prop) (h : Inputs p) :
    (p 2180) :=
  ElevenRUP.step65789 (p 86) (p 92) (p 2180) (h 2498) (h 2499) (h 105)

theorem derived65790 (p : Nat → Prop) (h : Inputs p) :
    (p 2181) :=
  ElevenRUP.step65790 (p 2180) (p 2181) (derived65789 p h) (h 2516)

theorem derived65791 (p : Nat → Prop) (h : Inputs p) :
    (p 4504) :=
  ElevenRUP.step65791 (p 2181) (p 4504) (derived65790 p h) (h 7086)

theorem derived65792 (p : Nat → Prop) (h : Inputs p) :
    (p 5799) :=
  ElevenRUP.step65792 (p 4504) (p 5799) (derived65791 p h) (h 11815)

theorem derived65793 (p : Nat → Prop) (h : Inputs p) :
    (p 2843) :=
  ElevenRUP.step65793 (p 710) (p 716) (p 2843) (h 3812) (h 3813) (h 781)

theorem derived65794 (p : Nat → Prop) (h : Inputs p) :
    (p 2844) :=
  ElevenRUP.step65794 (p 2843) (p 2844) (derived65793 p h) (h 3830)

theorem derived65795 (p : Nat → Prop) (h : Inputs p) :
    (p 4879) :=
  ElevenRUP.step65795 (p 2844) (p 4879) (derived65794 p h) (h 8047)

theorem derived65796 (p : Nat → Prop) (h : Inputs p) :
    (p 5931) :=
  ElevenRUP.step65796 (p 4879) (p 5931) (derived65795 p h) (h 12591)

theorem derived65798 (p : Nat → Prop) (h : Inputs p) :
    (p 2399) :=
  ElevenRUP.step65798 (p 302) (p 308) (p 2399) (h 2932) (h 2933) (h 339)

theorem derived65799 (p : Nat → Prop) (h : Inputs p) :
    (p 2400) :=
  ElevenRUP.step65799 (p 2399) (p 2400) (derived65798 p h) (h 2950)

theorem derived65800 (p : Nat → Prop) (h : Inputs p) :
    (p 4626) :=
  ElevenRUP.step65800 (p 2400) (p 4626) (derived65799 p h) (h 7408)

theorem derived65801 (p : Nat → Prop) (h : Inputs p) :
    (p 5847) :=
  ElevenRUP.step65801 (p 4626) (p 5847) (derived65800 p h) (h 12097)

theorem derived65802 (p : Nat → Prop) (h : Inputs p) :
    (p 2193) :=
  ElevenRUP.step65802 (p 98) (p 104) (p 2193) (h 2519) (h 2520) (h 118)

theorem derived65803 (p : Nat → Prop) (h : Inputs p) :
    (p 2194) :=
  ElevenRUP.step65803 (p 2193) (p 2194) (derived65802 p h) (h 2537)

theorem derived65804 (p : Nat → Prop) (h : Inputs p) :
    (p 4510) :=
  ElevenRUP.step65804 (p 2194) (p 4510) (derived65803 p h) (h 7103)

theorem derived65805 (p : Nat → Prop) (h : Inputs p) :
    (p 5802) :=
  ElevenRUP.step65805 (p 4510) (p 5802) (derived65804 p h) (h 11832)

theorem derived65807 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2891) ∨ (¬ p 2589) ∨ (¬ p 3905) ∨ (¬ p 4244) ∨ (¬ p 2138) ∨ (¬ p 4235) :=
  ElevenRUP.step65807 (p 2138) (p 2589) (p 2870) (p 2891) (p 3366) (p 3371) (p 3905) (p 4034) (p 4210) (p 4235) (p 4244) (p 4418) (p 4731) (p 4732) (p 4734) (p 4735) (p 4872) (p 4873) (p 4876) (derived65699 p h) (derived65532 p h) (h 9153) (h 6814) (h 20333) (h 8016) (h 40558) (h 8029) (h 8022) (derived50628 p h) (h 20629) (h 7683) (h 7685) (h 7693)

theorem derived65808 (p : Nat → Prop) (h : Inputs p) :
    (p 2812) :=
  ElevenRUP.step65808 (p 674) (p 680) (p 2812) (h 3750) (h 3751) (h 742)

theorem derived65809 (p : Nat → Prop) (h : Inputs p) :
    (p 2813) :=
  ElevenRUP.step65809 (p 2812) (p 2813) (derived65808 p h) (h 3768)

theorem derived65810 (p : Nat → Prop) (h : Inputs p) :
    (p 4855) :=
  ElevenRUP.step65810 (p 2813) (p 4855) (derived65809 p h) (h 7996)

theorem derived65811 (p : Nat → Prop) (h : Inputs p) :
    (p 5922) :=
  ElevenRUP.step65811 (p 4855) (p 5922) (derived65810 p h) (h 12539)

theorem derived65812 (p : Nat → Prop) (h : Inputs p) :
    (p 3215) :=
  ElevenRUP.step65812 (p 1070) (p 1076) (p 3215) (h 4549) (h 4550) (h 1171)

theorem derived65813 (p : Nat → Prop) (h : Inputs p) :
    (p 3216) :=
  ElevenRUP.step65813 (p 3215) (p 3216) (derived65812 p h) (h 4567)

theorem derived65814 (p : Nat → Prop) (h : Inputs p) :
    (p 5095) :=
  ElevenRUP.step65814 (p 3216) (p 5095) (derived65813 p h) (h 8589)

theorem derived65816 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3758) ∨ (¬ p 4405) ∨ (¬ p 2373) ∨ (¬ p 3097) ∨ (¬ p 2138) ∨ (¬ p 4235) :=
  ElevenRUP.step65816 (p 2138) (p 2373) (p 2563) (p 2619) (p 3097) (p 3694) (p 3758) (p 3988) (p 4110) (p 4235) (p 4405) (p 4441) (p 4504) (p 4505) (p 4508) (p 4713) (p 4714) (p 4716) (p 5886) (p 5887) (p 5888) (derived65780 p h) (derived65791 p h) (derived65618 p h) (derived43029 p h) (h 7624) (h 5920) (h 7630) (h 7071) (h 7618) (h 7085) (derived43959 p h) (h 7077) (h 12309) (derived52622 p h) (h 12322) (h 12316)

theorem derived65818 (p : Nat → Prop) (h : Inputs p) :
    (p 2486) :=
  ElevenRUP.step65818 (p 386) (p 392) (p 2486) (h 3105) (h 3106) (h 430)

theorem derived65819 (p : Nat → Prop) (h : Inputs p) :
    (p 2487) :=
  ElevenRUP.step65819 (p 2486) (p 2487) (derived65818 p h) (h 3123)

theorem derived65820 (p : Nat → Prop) (h : Inputs p) :
    (p 4676) :=
  ElevenRUP.step65820 (p 2487) (p 4676) (derived65819 p h) (h 7525)

theorem derived65821 (p : Nat → Prop) (h : Inputs p) :
    (p 2324) :=
  ElevenRUP.step65821 (p 218) (p 224) (p 2324) (h 2784) (h 2785) (h 248)

theorem derived65822 (p : Nat → Prop) (h : Inputs p) :
    (p 2325) :=
  ElevenRUP.step65822 (p 2324) (p 2325) (derived65821 p h) (h 2802)

theorem derived65823 (p : Nat → Prop) (h : Inputs p) :
    (p 4578) :=
  ElevenRUP.step65823 (p 2325) (p 4578) (derived65822 p h) (h 7288)

theorem derived65824 (p : Nat → Prop) (h : Inputs p) :
    (p 5826) :=
  ElevenRUP.step65824 (p 4578) (p 5826) (derived65823 p h) (h 11972)

theorem derived65825 (p : Nat → Prop) (h : Inputs p) :
    (p 2790) :=
  ElevenRUP.step65825 (p 650) (p 656) (p 2790) (h 3709) (h 3710) (h 716)

theorem derived65826 (p : Nat → Prop) (h : Inputs p) :
    (p 2791) :=
  ElevenRUP.step65826 (p 2790) (p 2791) (derived65825 p h) (h 3727)

theorem derived65827 (p : Nat → Prop) (h : Inputs p) :
    (p 4839) :=
  ElevenRUP.step65827 (p 2791) (p 4839) (derived65826 p h) (h 7960)

theorem derived65828 (p : Nat → Prop) (h : Inputs p) :
    (p 5916) :=
  ElevenRUP.step65828 (p 4839) (p 5916) (derived65827 p h) (h 12500)

theorem derived65829 (p : Nat → Prop) (h : Inputs p) :
    (p 2720) :=
  ElevenRUP.step65829 (p 602) (p 608) (p 2720) (h 3566) (h 3567) (h 664)

theorem derived65830 (p : Nat → Prop) (h : Inputs p) :
    (p 2721) :=
  ElevenRUP.step65830 (p 2720) (p 2721) (derived65829 p h) (h 3584)

theorem derived65831 (p : Nat → Prop) (h : Inputs p) :
    (p 4808) :=
  ElevenRUP.step65831 (p 2721) (p 4808) (derived65830 p h) (h 7870)

theorem derived65832 (p : Nat → Prop) (h : Inputs p) :
    (p 5910) :=
  ElevenRUP.step65832 (p 4808) (p 5910) (derived65831 p h) (h 12462)

theorem derived65834 (p : Nat → Prop) (h : Inputs p) :
    (p 2644) :=
  ElevenRUP.step65834 (p 530) (p 536) (p 2644) (h 3413) (h 3414) (h 586)

theorem derived65835 (p : Nat → Prop) (h : Inputs p) :
    (p 2645) :=
  ElevenRUP.step65835 (p 2644) (p 2645) (derived65834 p h) (h 3431)

theorem derived65836 (p : Nat → Prop) (h : Inputs p) :
    (p 4762) :=
  ElevenRUP.step65836 (p 2645) (p 4762) (derived65835 p h) (h 7751)

theorem derived65839 (p : Nat → Prop) (h : Inputs p) :
    (p 2566) :=
  ElevenRUP.step65839 (p 458) (p 464) (p 2566) (h 3257) (h 3258) (h 508)

theorem derived65840 (p : Nat → Prop) (h : Inputs p) :
    (p 2567) :=
  ElevenRUP.step65840 (p 2566) (p 2567) (derived65839 p h) (h 3275)

theorem derived65841 (p : Nat → Prop) (h : Inputs p) :
    (p 4719) :=
  ElevenRUP.step65841 (p 2567) (p 4719) (derived65840 p h) (h 7637)

theorem derived65842 (p : Nat → Prop) (h : Inputs p) :
    (p 2535) :=
  ElevenRUP.step65842 (p 422) (p 428) (p 2535) (h 3195) (h 3196) (h 469)

theorem derived65843 (p : Nat → Prop) (h : Inputs p) :
    (p 2536) :=
  ElevenRUP.step65843 (p 2535) (p 2536) (derived65842 p h) (h 3213)

theorem derived65844 (p : Nat → Prop) (h : Inputs p) :
    (p 4698) :=
  ElevenRUP.step65844 (p 2536) (p 4698) (derived65843 p h) (h 7597)

theorem derived65845 (p : Nat → Prop) (h : Inputs p) :
    (p 5871) :=
  ElevenRUP.step65845 (p 4698) (p 5871) (derived65844 p h) (h 12237)

theorem derived65846 (p : Nat → Prop) (h : Inputs p) :
    (p 2410) :=
  ElevenRUP.step65846 (p 314) (p 320) (p 2410) (h 2954) (h 2955) (h 352)

theorem derived65847 (p : Nat → Prop) (h : Inputs p) :
    (p 2411) :=
  ElevenRUP.step65847 (p 2410) (p 2411) (derived65846 p h) (h 2972)

theorem derived65848 (p : Nat → Prop) (h : Inputs p) :
    (p 4633) :=
  ElevenRUP.step65848 (p 2411) (p 4633) (derived65847 p h) (h 7425)

theorem derived65849 (p : Nat → Prop) (h : Inputs p) :
    (p 5850) :=
  ElevenRUP.step65849 (p 4633) (p 5850) (derived65848 p h) (h 12115)

theorem derived65851 (p : Nat → Prop) (h : Inputs p) :
    (p 2546) :=
  ElevenRUP.step65851 (p 434) (p 440) (p 2546) (h 3217) (h 3218) (h 482)

theorem derived65852 (p : Nat → Prop) (h : Inputs p) :
    (p 2547) :=
  ElevenRUP.step65852 (p 2546) (p 2547) (derived65851 p h) (h 3235)

theorem derived65853 (p : Nat → Prop) (h : Inputs p) :
    (p 4706) :=
  ElevenRUP.step65853 (p 2547) (p 4706) (derived65852 p h) (h 7614)

theorem derived65854 (p : Nat → Prop) (h : Inputs p) :
    (p 5874) :=
  ElevenRUP.step65854 (p 4706) (p 5874) (derived65853 p h) (h 12255)

theorem derived65856 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4755) ∨ (¬ p 2542) ∨ (¬ p 2246) ∨ (¬ p 2727) ∨ (¬ p 4389) ∨ (¬ p 2230) ∨ (¬ p 4715) :=
  ElevenRUP.step65856 (p 2230) (p 2246) (p 2331) (p 2542) (p 2651) (p 2654) (p 2656) (p 2661) (p 2727) (p 2963) (p 4154) (p 4245) (p 4319) (p 4389) (p 4578) (p 4579) (p 4582) (p 4715) (p 4755) (p 4762) (derived65823 p h) (derived65836 p h) (h 7731) (h 7732) (h 7733) (h 15125) (derived51526 p h) (h 7281) (h 3434) (h 7287) (h 7750) (h 7275) (h 3449) (derived49230 p h)

theorem derived65857 (p : Nat → Prop) (h : Inputs p) :
    (p 2669) :=
  ElevenRUP.step65857 (p 542) (p 548) (p 2669) (h 3462) (h 3463) (h 599)

theorem derived65858 (p : Nat → Prop) (h : Inputs p) :
    (p 2670) :=
  ElevenRUP.step65858 (p 2669) (p 2670) (derived65857 p h) (h 3480)

theorem derived65859 (p : Nat → Prop) (h : Inputs p) :
    (p 4767) :=
  ElevenRUP.step65859 (p 2670) (p 4767) (derived65858 p h) (h 7784)

theorem derived65860 (p : Nat → Prop) (h : Inputs p) :
    (p 5895) :=
  ElevenRUP.step65860 (p 4767) (p 5895) (derived65859 p h) (h 12375)

theorem derived65863 (p : Nat → Prop) (h : Inputs p) :
    (p 2203) :=
  ElevenRUP.step65863 (p 110) (p 116) (p 2203) (h 2541) (h 2542) (h 131)

theorem derived65864 (p : Nat → Prop) (h : Inputs p) :
    (p 2204) :=
  ElevenRUP.step65864 (p 2203) (p 2204) (derived65863 p h) (h 2559)

theorem derived65865 (p : Nat → Prop) (h : Inputs p) :
    (p 4519) :=
  ElevenRUP.step65865 (p 2204) (p 4519) (derived65864 p h) (h 7120)

theorem derived65866 (p : Nat → Prop) (h : Inputs p) :
    (p 5805) :=
  ElevenRUP.step65866 (p 4519) (p 5805) (derived65865 p h) (h 11850)

theorem derived65869 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4195) ∨ (¬ p 2230) ∨ (¬ p 4389) ∨ (¬ p 2630) ∨ (¬ p 2542) ∨ (¬ p 4715) :=
  ElevenRUP.step65869 (p 2230) (p 2331) (p 2542) (p 2630) (p 2651) (p 2654) (p 2656) (p 2661) (p 2963) (p 4195) (p 4389) (p 4578) (p 4579) (p 4582) (p 4715) (p 4762) (derived65836 p h) (derived65823 p h) (derived50312 p h) (derived44438 p h) (h 3434) (h 7281) (h 7750) (h 7287) (h 3449) (h 7275) (derived49230 p h)

theorem derived65870 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (¬ p 4787) ∨ (¬ p 4236) ∨ (¬ p 2657) ∨ (¬ p 4751) :=
  ElevenRUP.step65870 (p 2630) (p 2657) (p 2737) (p 2740) (p 2743) (p 2747) (p 3055) (p 3366) (p 3367) (p 3683) (p 4236) (p 4731) (p 4732) (p 4734) (p 4735) (p 4751) (p 4787) (p 4815) (derived65613 p h) (derived65532 p h) (h 7719) (h 22900) (h 7721) (derived48009 p h) (h 4835) (h 3608) (h 7685) (h 7875) (h 7693) (h 3622) (h 7683) (derived42791 p h)

theorem derived65874 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5192) ∨ (¬ p 2498) ∨ (¬ p 4257) ∨ (¬ p 4866) ∨ (¬ p 3591) ∨ (¬ p 2230) ∨ (¬ p 4715) :=
  ElevenRUP.step65874 (p 2230) (p 2406) (p 2498) (p 3238) (p 3379) (p 3591) (p 4079) (p 4257) (p 4626) (p 4627) (p 4630) (p 4715) (p 4866) (p 5192) (derived65800 p h) (h 8804) (h 8805) (derived49538 p h) (derived50238 p h) (h 7395) (h 7401) (h 7407)

theorem derived65879 (p : Nat → Prop) (h : Inputs p) :
    (p 2430) :=
  ElevenRUP.step65879 (p 338) (p 344) (p 2430) (h 2994) (h 2995) (h 378)

theorem derived65880 (p : Nat → Prop) (h : Inputs p) :
    (p 2431) :=
  ElevenRUP.step65880 (p 2430) (p 2431) (derived65879 p h) (h 3012)

theorem derived65881 (p : Nat → Prop) (h : Inputs p) :
    (p 4648) :=
  ElevenRUP.step65881 (p 2431) (p 4648) (derived65880 p h) (h 7460)

theorem derived65882 (p : Nat → Prop) (h : Inputs p) :
    (p 5856) :=
  ElevenRUP.step65882 (p 4648) (p 5856) (derived65881 p h) (h 12149)

theorem derived65885 (p : Nat → Prop) (h : Inputs p) :
    (p 2288) :=
  ElevenRUP.step65885 (p 194) (p 200) (p 2288) (h 2713) (h 2714) (h 222)

theorem derived65886 (p : Nat → Prop) (h : Inputs p) :
    (p 2289) :=
  ElevenRUP.step65886 (p 2288) (p 2289) (derived65885 p h) (h 2731)

theorem derived65887 (p : Nat → Prop) (h : Inputs p) :
    (p 4567) :=
  ElevenRUP.step65887 (p 2289) (p 4567) (derived65886 p h) (h 7250)

theorem derived65888 (p : Nat → Prop) (h : Inputs p) :
    (p 5823) :=
  ElevenRUP.step65888 (p 4567) (p 5823) (derived65887 p h) (h 11955)

theorem derived65889 (p : Nat → Prop) (h : Inputs p) :
    (p 2463) :=
  ElevenRUP.step65889 (p 374) (p 380) (p 2463) (h 3057) (h 3058) (h 417)

theorem derived65890 (p : Nat → Prop) (h : Inputs p) :
    (p 2464) :=
  ElevenRUP.step65890 (p 2463) (p 2464) (derived65889 p h) (h 3075)

theorem derived65891 (p : Nat → Prop) (h : Inputs p) :
    (p 4670) :=
  ElevenRUP.step65891 (p 2464) (p 4670) (derived65890 p h) (h 7499)

theorem derived65893 (p : Nat → Prop) (h : Inputs p) :
    (p 2345) :=
  ElevenRUP.step65893 (p 242) (p 248) (p 2345) (h 2827) (h 2828) (h 274)

theorem derived65894 (p : Nat → Prop) (h : Inputs p) :
    (p 2346) :=
  ElevenRUP.step65894 (p 2345) (p 2346) (derived65893 p h) (h 2845)

theorem derived65895 (p : Nat → Prop) (h : Inputs p) :
    (p 4593) :=
  ElevenRUP.step65895 (p 2346) (p 4593) (derived65894 p h) (h 7322)

theorem derived65896 (p : Nat → Prop) (h : Inputs p) :
    (p 5832) :=
  ElevenRUP.step65896 (p 4593) (p 5832) (derived65895 p h) (h 12006)

theorem derived65900 (p : Nat → Prop) (h : Inputs p) :
    (p 2915) :=
  ElevenRUP.step65900 (p 794) (p 800) (p 2915) (h 3956) (h 3957) (h 872)

theorem derived65901 (p : Nat → Prop) (h : Inputs p) :
    (p 2916) :=
  ElevenRUP.step65901 (p 2915) (p 2916) (derived65900 p h) (h 3974)

theorem derived65902 (p : Nat → Prop) (h : Inputs p) :
    (p 4925) :=
  ElevenRUP.step65902 (p 2916) (p 4925) (derived65901 p h) (h 8156)

theorem derived65906 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2797) ∨ (¬ p 3016) ∨ (¬ p 3984) ∨ (¬ p 4787) ∨ (¬ p 2654) :=
  ElevenRUP.step65906 (p 2579) (p 2630) (p 2654) (p 2655) (p 2659) (p 2797) (p 2810) (p 3016) (p 3984) (p 4747) (p 4748) (p 4751) (p 4787) (derived65606 p h) (h 3437) (h 3433) (derived58281 p h) (derived41612 p h) (h 7721) (h 7715) (h 7727)

theorem derived65907 (p : Nat → Prop) (h : Inputs p) :
    (p 2312) ∨ (¬ p 4975) ∨ (¬ p 3568) ∨ (¬ p 2657) :=
  ElevenRUP.step65907 (p 2307) (p 2310) (p 2312) (p 2317) (p 2318) (p 2319) (p 2657) (p 3567) (p 3568) (p 3987) (p 4573) (p 4578) (p 4579) (p 4582) (p 4975) (derived65754 p h) (derived65823 p h) (h 2755) (h 5196) (h 7254) (h 2769) (h 2770) (h 5195) (derived49439 p h) (h 7274) (h 7280) (h 7287)

theorem derived65910 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5140) ∨ (¬ p 4366) ∨ (¬ p 4514) ∨ (¬ p 2608) ∨ (¬ p 2274) :=
  ElevenRUP.step65910 (p 2274) (p 2608) (p 3093) (p 3549) (p 3591) (p 4366) (p 4427) (p 4514) (p 5013) (p 5014) (p 5019) (p 5140) (derived65583 p h) (h 8704) (h 8705) (derived41837 p h) (derived47638 p h) (h 8392) (h 8386) (h 8398)

theorem derived65914 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4235) ∨ (¬ p 2579) ∨ (¬ p 2284) ∨ (¬ p 2659) ∨ (¬ p 4705) ∨ (¬ p 3413) ∨ (¬ p 3872) :=
  ElevenRUP.step65914 (p 2230) (p 2284) (p 2563) (p 2579) (p 2589) (p 2659) (p 2901) (p 3096) (p 3413) (p 3872) (p 4235) (p 4534) (p 4535) (p 4537) (p 4705) (p 4713) (p 4714) (p 4716) (derived65780 p h) (derived65673 p h) (h 6731) (h 20312) (derived41883 p h) (h 7624) (h 7142) (h 7630) (h 7154) (h 7617) (h 7148) (derived41152 p h)

theorem derived65915 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2579) ∨ (¬ p 2284) ∨ (¬ p 2659) ∨ (¬ p 3646) ∨ (¬ p 4705) ∨ (¬ p 2542) ∨ (¬ p 3413) ∨ (¬ p 2911) ∨ (¬ p 3016) ∨ (¬ p 3872) :=
  ElevenRUP.step65915 (p 2230) (p 2284) (p 2542) (p 2563) (p 2579) (p 2589) (p 2659) (p 2911) (p 3016) (p 3389) (p 3413) (p 3540) (p 3646) (p 3741) (p 3872) (p 3904) (p 4110) (p 4235) (p 4534) (p 4535) (p 4537) (p 4642) (p 4643) (p 4645) (p 4705) (p 4713) (p 4714) (p 4716) (p 5195) (p 5196) (p 5200) (derived65496 p h) (derived65784 p h) (derived65673 p h) (derived65780 p h) (derived46915 p h) (h 8822) (h 8828) (h 8816) (derived65914 p h) (h 7429) (h 7441) (h 7434) (h 19841) (h 38156) (h 7148) (derived41609 p h) (h 7154) (h 7618) (h 7140) (h 7630) (derived41572 p h) (h 7624)

theorem derived65917 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2299) ∨ (¬ p 2933) ∨ (¬ p 2922) ∨ (¬ p 4452) ∨ (¬ p 3093) ∨ (¬ p 2911) :=
  ElevenRUP.step65917 (p 2299) (p 2911) (p 2922) (p 2933) (p 3093) (p 3379) (p 3452) (p 4452) (p 5188) (p 5189) (p 5192) (derived65500 p h) (derived45312 p h) (derived64862 p h) (h 8805) (h 8799) (h 8811)

theorem derived65918 (p : Nat → Prop) (h : Inputs p) :
    (p 2499) ∨ (¬ p 5143) ∨ (¬ p 3093) ∨ (¬ p 4709) ∨ (¬ p 2911) :=
  ElevenRUP.step65918 (p 2177) (p 2299) (p 2493) (p 2496) (p 2499) (p 2503) (p 2553) (p 2911) (p 2922) (p 2925) (p 2928) (p 2932) (p 2933) (p 3093) (p 3309) (p 3379) (p 3452) (p 3920) (p 4452) (p 4499) (p 4500) (p 4502) (p 4676) (p 4709) (p 4925) (p 5143) (p 5188) (p 5189) (p 5192) (derived65820 p h) (derived65902 p h) (derived65748 p h) (derived65500 p h) (h 8711) (h 8710) (h 7607) (h 7606) (h 3127) (h 6412) (h 7524) (h 3978) (h 3141) (h 8155) (h 27159) (h 3990) (derived65917 p h) (h 7056) (h 7068) (h 7062) (derived47943 p h) (derived42843 p h) (h 8799) (h 8805) (h 8811)

theorem derived65920 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 4484) ∨ (¬ p 2284) ∨ (¬ p 4705) ∨ (¬ p 3413) ∨ (¬ p 4031) ∨ (p 3574) ∨ (¬ p 2386) :=
  ElevenRUP.step65920 (p 2284) (p 2386) (p 2406) (p 2499) (p 3238) (p 3413) (p 3487) (p 3574) (p 3646) (p 3743) (p 4031) (p 4484) (p 4626) (p 4627) (p 4630) (p 4705) (p 4808) (p 4809) (p 4811) (p 4812) (derived65831 p h) (derived65800 p h) (h 7022) (h 7021) (h 6364) (derived54371 p h) (h 7861) (h 7401) (h 7869) (h 7407) (h 7859) (h 7395) (derived41126 p h)

theorem derived65921 (p : Nat → Prop) (h : Inputs p) :
    (p 2767) :=
  ElevenRUP.step65921 (p 638) (p 644) (p 2767) (h 3661) (h 3662) (h 703)

theorem derived65922 (p : Nat → Prop) (h : Inputs p) :
    (p 2768) :=
  ElevenRUP.step65922 (p 2767) (p 2768) (derived65921 p h) (h 3679)

theorem derived65923 (p : Nat → Prop) (h : Inputs p) :
    (p 4833) :=
  ElevenRUP.step65923 (p 2768) (p 4833) (derived65922 p h) (h 7921)

theorem derived65924 (p : Nat → Prop) (h : Inputs p) :
    (p 2115) :=
  ElevenRUP.step65924 (p 26) (p 32) (p 2115) (h 2366) (h 2367) (h 40)

theorem derived65925 (p : Nat → Prop) (h : Inputs p) :
    (p 2116) :=
  ElevenRUP.step65925 (p 2115) (p 2116) (derived65924 p h) (h 2384)

theorem derived65926 (p : Nat → Prop) (h : Inputs p) :
    (p 4469) :=
  ElevenRUP.step65926 (p 2116) (p 4469) (derived65925 p h) (h 6997)

theorem derived65927 (p : Nat → Prop) (h : Inputs p) :
    (p 5787) :=
  ElevenRUP.step65927 (p 4469) (p 5787) (derived65926 p h) (h 11746)

theorem derived65928 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2177) ∨ (¬ p 2122) ∨ (¬ p 3422) ∨ (¬ p 2774) ∨ (¬ p 2553) :=
  ElevenRUP.step65928 (p 2122) (p 2177) (p 2553) (p 2598) (p 2774) (p 3055) (p 3422) (p 4725) (p 4726) (p 4728) (derived65591 p h) (derived46418 p h) (derived56917 p h) (h 7670) (h 7664) (h 7676)

theorem derived65934 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2142) ∨ (p 2156) ∨ (¬ p 4906) ∨ (¬ p 2284) ∨ (¬ p 2780) :=
  ElevenRUP.step65934 (p 2132) (p 2142) (p 2143) (p 2156) (p 2284) (p 2780) (p 2860) (p 4428) (p 4886) (p 4887) (p 4890) (p 4906) (derived65741 p h) (h 2420) (h 2422) (h 6640) (derived50691 p h) (h 8057) (h 8050) (h 8063)

theorem derived65936 (p : Nat → Prop) (h : Inputs p) :
    (p 2257) :=
  ElevenRUP.step65936 (p 158) (p 164) (p 2257) (h 2651) (h 2652) (h 183)

theorem derived65937 (p : Nat → Prop) (h : Inputs p) :
    (p 2258) :=
  ElevenRUP.step65937 (p 2257) (p 2258) (derived65936 p h) (h 2669)

theorem derived65938 (p : Nat → Prop) (h : Inputs p) :
    (p 4546) :=
  ElevenRUP.step65938 (p 2258) (p 4546) (derived65937 p h) (h 7198)

theorem derived65939 (p : Nat → Prop) (h : Inputs p) :
    (p 5814) :=
  ElevenRUP.step65939 (p 4546) (p 5814) (derived65938 p h) (h 11903)

theorem derived65942 (p : Nat → Prop) (h : Inputs p) :
    (p 2442) :=
  ElevenRUP.step65942 (p 350) (p 356) (p 2442) (h 3015) (h 3016) (h 391)

theorem derived65943 (p : Nat → Prop) (h : Inputs p) :
    (p 2443) :=
  ElevenRUP.step65943 (p 2442) (p 2443) (derived65942 p h) (h 3033)

theorem derived65944 (p : Nat → Prop) (h : Inputs p) :
    (p 4654) :=
  ElevenRUP.step65944 (p 2443) (p 4654) (derived65943 p h) (h 7477)

theorem derived65945 (p : Nat → Prop) (h : Inputs p) :
    (p 5859) :=
  ElevenRUP.step65945 (p 4654) (p 5859) (derived65944 p h) (h 12166)

theorem derived65947 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4515) ∨ (¬ p 3646) ∨ (¬ p 2608) ∨ (¬ p 4377) ∨ (p 3093) :=
  ElevenRUP.step65947 (p 2192) (p 2210) (p 2608) (p 3093) (p 3369) (p 3646) (p 4338) (p 4377) (p 4515) (p 4519) (p 4520) (p 4523) (derived65865 p h) (h 7095) (h 7096) (h 34923) (derived41882 p h) (h 7113) (h 7105) (h 7119)

theorem derived65949 (p : Nat → Prop) (h : Inputs p) :
    (p 3646) ∨ (¬ p 2317) ∨ (¬ p 3556) :=
  ElevenRUP.step65949 (p 2317) (p 2318) (p 2319) (p 2962) (p 3556) (p 3646) (p 3872) (p 4275) (p 4483) (p 4484) (p 4487) (p 4553) (p 4554) (p 4557) (derived65737 p h) (derived65724 p h) (h 2769) (h 2768) (h 7022) (h 6734) (h 7034) (h 7207) (h 7027) (h 7214) (h 13907) (h 7201)

theorem derived65950 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2284) ∨ (¬ p 4511) ∨ (¬ p 3591) ∨ (¬ p 2608) :=
  ElevenRUP.step65950 (p 2210) (p 2284) (p 2608) (p 3555) (p 3591) (p 3957) (p 4173) (p 4282) (p 4511) (p 4512) (p 4519) (p 4520) (p 4523) (p 4955) (p 4956) (p 4957) (p 4958) (derived65661 p h) (derived65865 p h) (h 7090) (h 7089) (h 7088) (h 38297) (derived46321 p h) (h 8244) (h 7107) (h 8252) (h 7119) (h 8242) (h 7113) (derived48141 p h)

theorem derived65953 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2499) ∨ (¬ p 3422) ∨ (¬ p 5214) ∨ (¬ p 3591) ∨ (¬ p 2608) :=
  ElevenRUP.step65953 (p 2493) (p 2496) (p 2498) (p 2499) (p 2503) (p 2608) (p 3379) (p 3422) (p 3452) (p 3591) (p 4676) (p 5188) (p 5189) (p 5192) (p 5214) (derived65820 p h) (derived65500 p h) (h 9329) (derived45490 p h) (h 3141) (h 8799) (h 7524) (h 8811) (h 3126) (h 8805) (derived41933 p h)

theorem derived65955 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5007) ∨ (¬ p 2542) ∨ (¬ p 4885) ∨ (¬ p 2619) :=
  ElevenRUP.step65955 (p 2542) (p 2619) (p 3693) (p 3878) (p 4256) (p 4355) (p 4437) (p 4605) (p 4606) (p 4609) (p 4885) (p 5007) (derived65771 p h) (h 8367) (h 8368) (h 8369) (h 25935) (derived51071 p h) (h 7348) (h 7342) (h 7355)

theorem derived65956 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3584) ∨ (¬ p 3582) ∨ (¬ p 2850) ∨ (¬ p 4715) ∨ (¬ p 3096) ∨ (¬ p 4509) ∨ (¬ p 2619) :=
  ElevenRUP.step65956 (p 2373) (p 2619) (p 2850) (p 3096) (p 3582) (p 3584) (p 3880) (p 4509) (p 4605) (p 4606) (p 4609) (p 4715) (derived65771 p h) (derived57959 p h) (derived64242 p h) (h 7343) (h 7349) (h 7355)

theorem derived65957 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4912) ∨ (¬ p 4377) ∨ (¬ p 3556) ∨ (¬ p 2608) :=
  ElevenRUP.step65957 (p 2608) (p 2891) (p 3369) (p 3556) (p 3571) (p 3645) (p 4377) (p 4431) (p 4519) (p 4520) (p 4523) (p 4912) (derived65865 p h) (h 8108) (h 8109) (h 8110) (h 13537) (derived41696 p h) (h 7111) (h 7105) (h 7119)

theorem derived65959 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2860) ∨ (¬ p 3957) ∨ (¬ p 4173) ∨ (¬ p 3591) ∨ (¬ p 4875) ∨ (¬ p 2608) :=
  ElevenRUP.step65959 (p 2210) (p 2608) (p 2860) (p 3555) (p 3591) (p 3957) (p 4173) (p 4519) (p 4520) (p 4523) (p 4875) (derived65865 p h) (derived50504 p h) (derived63592 p h) (h 7113) (h 7107) (h 7119)

theorem derived65965 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2949) ∨ (¬ p 3136) ∨ (¬ p 4787) ∨ (¬ p 3758) ∨ (¬ p 4120) ∨ (¬ p 2619) :=
  ElevenRUP.step65965 (p 2619) (p 2949) (p 2950) (p 2952) (p 3136) (p 3156) (p 3497) (p 3758) (p 4120) (p 4787) (p 5060) (p 5061) (p 5064) (derived65559 p h) (h 4026) (h 4028) (derived50247 p h) (derived42885 p h) (h 8496) (h 8490) (h 8502)

theorem derived65966 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4809) ∨ (¬ p 4703) ∨ (¬ p 2499) ∨ (¬ p 4715) ∨ (¬ p 2992) :=
  ElevenRUP.step65966 (p 2499) (p 2992) (p 3016) (p 3402) (p 3574) (p 4111) (p 4241) (p 4703) (p 4704) (p 4715) (p 4809) (p 4970) (p 4971) (p 4974) (derived65653 p h) (h 7591) (h 7588) (h 7855) (h 7857) (derived48656 p h) (derived41275 p h) (h 8280) (h 8274) (h 8286)

theorem derived65973 (p : Nat → Prop) (h : Inputs p) :
    (p 2427) ∨ (¬ p 4727) ∨ (¬ p 4753) ∨ (¬ p 2440) ∨ (¬ p 2870) ∨ (¬ p 3556) :=
  ElevenRUP.step65973 (p 2427) (p 2440) (p 2589) (p 2870) (p 3556) (p 3582) (p 3698) (p 4031) (p 4235) (p 4534) (p 4535) (p 4537) (p 4642) (p 4643) (p 4645) (p 4727) (p 4753) (p 4879) (p 4880) (p 4883) (derived65784 p h) (derived65795 p h) (derived65673 p h) (h 7435) (h 6374) (h 7441) (h 8033) (h 7429) (h 8046) (h 8039) (derived48557 p h) (derived42204 p h) (h 7142) (h 7146) (h 7154)

theorem derived65976 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4535) ∨ (¬ p 2542) ∨ (p 2132) ∨ (¬ p 2870) ∨ (¬ p 3556) :=
  ElevenRUP.step65976 (p 2132) (p 2427) (p 2542) (p 2589) (p 2598) (p 2654) (p 2659) (p 2661) (p 2662) (p 2850) (p 2870) (p 3556) (p 3582) (p 3698) (p 3904) (p 4235) (p 4535) (p 4642) (p 4643) (p 4645) (p 4725) (p 4726) (p 4727) (p 4728) (p 4762) (p 4879) (p 4880) (p 4883) (derived65836 p h) (derived65795 p h) (derived65591 p h) (derived65784 p h) (h 7140) (h 7142) (h 6146) (h 3447) (h 7750) (h 3437) (derived42468 p h) (h 8033) (h 8046) (h 8039) (h 8040) (h 25038) (h 7670) (h 7676) (h 7666) (derived50295 p h) (derived48557 p h) (h 7435) (h 7429) (h 7441)

theorem derived65977 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3952) ∨ (¬ p 3365) ∨ (¬ p 4315) ∨ (¬ p 4316) ∨ (¬ p 3583) ∨ (¬ p 3954) :=
  ElevenRUP.step65977 (p 2737) (p 2740) (p 2743) (p 2747) (p 3365) (p 3583) (p 3952) (p 3954) (p 4315) (p 4316) (p 4815) (derived65613 p h) (derived48955 p h) (derived46288 p h) (h 3622) (h 3608) (h 7875)

theorem derived65978 (p : Nat → Prop) (h : Inputs p) :
    (p 2904) :=
  ElevenRUP.step65978 (p 782) (p 788) (p 2904) (h 3934) (h 3935) (h 859)

theorem derived65979 (p : Nat → Prop) (h : Inputs p) :
    (p 2905) :=
  ElevenRUP.step65979 (p 2904) (p 2905) (derived65978 p h) (h 3952)

theorem derived65980 (p : Nat → Prop) (h : Inputs p) :
    (p 4920) :=
  ElevenRUP.step65980 (p 2905) (p 4920) (derived65979 p h) (h 8151)

theorem derived65981 (p : Nat → Prop) (h : Inputs p) :
    (p 5949) :=
  ElevenRUP.step65981 (p 4920) (p 5949) (derived65980 p h) (h 12696)

theorem derived65984 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4554) ∨ (¬ p 2295) ∨ (¬ p 2553) ∨ (¬ p 4718) ∨ (¬ p 3556) ∨ (¬ p 2954) ∨ (¬ p 4336) :=
  ElevenRUP.step65984 (p 2156) (p 2295) (p 2553) (p 2954) (p 3097) (p 3556) (p 3646) (p 4275) (p 4336) (p 4483) (p 4484) (p 4487) (p 4554) (p 4718) (derived65737 p h) (h 7201) (h 7202) (derived57162 p h) (derived42065 p h) (h 7028) (h 7022) (h 7034)

theorem derived65988 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4511) ∨ (¬ p 4256) ∨ (¬ p 4809) ∨ (¬ p 4699) ∨ (¬ p 4501) ∨ (¬ p 3644) ∨ (¬ p 2307) ∨ (¬ p 2563) ∨ (¬ p 2747) ∨ (¬ p 3954) ∨ (¬ p 2284) ∨ (¬ p 3872) ∨ (¬ p 3556) :=
  ElevenRUP.step65988 (p 2156) (p 2166) (p 2190) (p 2191) (p 2210) (p 2241) (p 2244) (p 2247) (p 2251) (p 2252) (p 2284) (p 2307) (p 2352) (p 2373) (p 2406) (p 2417) (p 2427) (p 2437) (p 2440) (p 2459) (p 2528) (p 2534) (p 2542) (p 2563) (p 2619) (p 2651) (p 2654) (p 2657) (p 2661) (p 2747) (p 2748) (p 2750) (p 2881) (p 2891) (p 2901) (p 2949) (p 2950) (p 2956) (p 2957) (p 2992) (p 3016) (p 3073) (p 3093) (p 3136) (p 3146) (p 3156) (p 3246) (p 3309) (p 3399) (p 3449) (p 3486) (p 3497) (p 3549) (p 3554) (p 3555) (p 3556) (p 3569) (p 3574) (p 3583) (p 3591) (p 3631) (p 3644) (p 3646) (p 3660) (p 3690) (p 3692) (p 3741) (p 3742) (p 3743) (p 3817) (p 3860) (p 3872) (p 3880) (p 3906) (p 3954) (p 3956) (p 3957) (p 3989) (p 4031) (p 4110) (p 4111) (p 4116) (p 4119) (p 4173) (p 4203) (p 4235) (p 4242) (p 4243) (p 4256) (p 4261) (p 4278) (p 4340) (p 4348) (p 4355) (p 4359) (p 4366) (p 4483) (p 4484) (p 4487) (p 4490) (p 4491) (p 4495) (p 4501) (p 4504) (p 4505) (p 4508) (p 4511) (p 4512) (p 4519) (p 4520) (p 4523) (p 4533) (p 4534) (p 4535) (p 4537) (p 4540) (p 4593) (p 4594) (p 4597) (p 4605) (p 4606) (p 4609) (p 4626) (p 4627) (p 4629) (p 4630) (p 4633) (p 4634) (p 4639) (p 4642) (p 4643) (p 4645) (p 4648) (p 4649) (p 4651) (p 4664) (p 4665) (p 4667) (p 4668) (p 4669) (p 4691) (p 4692) (p 4694) (p 4699) (p 4700) (p 4701) (p 4713) (p 4714) (p 4716) (p 4738) (p 4739) (p 4741) (p 4743) (p 4762) (p 4809) (p 4872) (p 4873) (p 4876) (p 4899) (p 4900) (p 4903) (p 4906) (p 4907) (p 4908) (p 4909) (p 4912) (p 4931) (p 4955) (p 4956) (p 4957) (p 4958) (p 4970) (p 4971) (p 4974) (p 4999) (p 5000) (p 5003) (p 5013) (p 5014) (p 5019) (p 5047) (p 5048) (p 5049) (p 5050) (p 5054) (p 5055) (p 5057) (p 5060) (p 5061) (p 5064) (p 5100) (p 5101) (p 5103) (p 5139) (p 5140) (p 5143) (p 5204) (p 5205) (p 5209) (p 5237) (p 5238) (p 5241) (p 5310) (p 5311) (p 5314) (p 5315) (p 5355) (p 5356) (p 5361) (derived65737 p h) (derived65784 p h) (derived65649 p h) (derived65673 p h) (derived65780 p h) (derived65653 p h) (derived65687 p h) (derived65836 p h) (derived65800 p h) (derived65661 p h) (derived65567 p h) (derived65520 p h) (derived65681 p h) (derived65690 p h) (derived65881 p h) (derived65694 p h) (derived65556 p h) (derived65775 p h) (derived65865 p h) (derived65699 p h) (derived65583 p h) (derived65492 p h) (derived65617 p h) (derived65895 p h) (derived65424 p h) (derived65444 p h) (derived65791 p h) (derived65540 p h) (derived65771 p h) (derived65559 p h) (derived65848 p h) (derived65476 p h) (derived65563 p h) (derived65597 p h) (h 7582) (h 3620) (h 7857) (h 19996) (h 8462) (h 8468) (h 8458) (h 8457) (h 20017) (h 8246) (h 8252) (h 8242) (h 7584) (h 9451) (h 7856) (h 6867) (h 7401) (h 7407) (h 7397) (h 6731) (h 30502) (h 4040) (h 8182) (h 4026) (h 7585) (derived55129 p h) (h 3449) (h 7750) (h 3435) (h 6734) (h 9440) (h 7618) (h 7630) (h 7622) (h 20348) (h 23019) (h 7146) (h 7154) (h 7144) (derived57213 p h) (h 8280) (h 8286) (h 8274) (h 20312) (h 7429) (h 7441) (h 7433) (h 20717) (h 8092) (h 8098) (h 8084) (h 7434) (h 7623) (h 5739) (h 3623) (h 7028) (h 7034) (h 7021) (h 7088) (h 7089) (h 7090) (derived41942 p h) (derived41459 p h) (h 8705) (h 8110) (h 6798) (h 8717) (h 8116) (h 7045) (h 8711) (h 8102) (h 8103) (h 8104) (h 7051) (h 6682) (derived63238 p h) (h 7038) (h 7453) (h 7459) (h 7447) (derived44724 p h) (derived43271 p h) (h 7481) (h 2625) (h 7493) (h 7159) (h 7487) (h 7488) (h 7489) (h 2637) (h 2639) (derived45831 p h) (derived42642 p h) (derived41389 p h) (h 7567) (h 7107) (h 8017) (h 7579) (h 7119) (h 8029) (h 7573) (h 7113) (h 8021) (derived48141 p h) (derived41864 p h) (h 6718) (h 8386) (h 8833) (h 7704) (h 8398) (h 8845) (h 7710) (h 8392) (h 8839) (h 7696) (h 7699) (derived50065 p h) (derived63123 p h) (derived53159 p h) (h 7309) (h 9217) (h 9061) (h 7321) (h 9223) (h 9073) (h 7315) (h 9211) (h 9065) (derived40917 p h) (derived59744 p h) (h 7073) (h 8615) (h 7085) (h 8621) (h 7078) (h 8609) (h 6866) (h 6279) (h 5078) (derived51491 p h) (derived42140 p h) (h 7343) (h 8490) (h 7418) (h 8911) (h 7355) (h 8502) (h 7424) (h 8923) (h 7348) (h 8496) (h 7412) (h 8917) (derived54486 p h) (derived61025 p h) (h 8473) (h 8357) (h 8485) (h 8363) (h 8479) (h 8351) (derived63200 p h) (h 40482)

theorem derived65989 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2241) ∨ (¬ p 2891) ∨ (¬ p 3369) ∨ (¬ p 5049) ∨ (¬ p 2747) ∨ (¬ p 3954) ∨ (¬ p 3556) :=
  ElevenRUP.step65989 (p 2241) (p 2747) (p 2748) (p 2750) (p 2891) (p 3369) (p 3371) (p 3556) (p 3583) (p 3954) (p 4872) (p 4873) (p 4876) (p 5049) (derived65699 p h) (h 3623) (h 3620) (derived42613 p h) (derived41389 p h) (h 8022) (h 8017) (h 8029)

theorem derived65990 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2437) ∨ (¬ p 3876) ∨ (¬ p 4882) ∨ (¬ p 5049) ∨ (¬ p 3364) ∨ (¬ p 3574) ∨ (¬ p 2440) ∨ (¬ p 3569) ∨ (¬ p 3556) :=
  ElevenRUP.step65990 (p 2135) (p 2136) (p 2142) (p 2143) (p 2437) (p 2440) (p 2696) (p 2870) (p 3055) (p 3364) (p 3365) (p 3556) (p 3569) (p 3574) (p 3876) (p 4244) (p 4478) (p 4784) (p 4785) (p 4788) (p 4882) (p 4892) (p 4893) (p 4896) (p 5049) (derived65630 p h) (derived65646 p h) (derived65602 p h) (derived63237 p h) (derived53915 p h) (h 8068) (h 6855) (h 6408) (h 8080) (h 2420) (h 7805) (h 8074) (h 7001) (h 7817) (h 2406) (h 7811) (derived50242 p h)

theorem derived65991 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4809) ∨ (¬ p 4699) ∨ (¬ p 4501) ∨ (¬ p 3644) ∨ (¬ p 4186) ∨ (¬ p 2307) ∨ (¬ p 2563) ∨ (¬ p 2747) ∨ (¬ p 3954) ∨ (¬ p 2284) ∨ (¬ p 3872) ∨ (¬ p 3556) :=
  ElevenRUP.step65991 (p 2156) (p 2192) (p 2241) (p 2244) (p 2247) (p 2251) (p 2284) (p 2307) (p 2437) (p 2440) (p 2563) (p 2630) (p 2747) (p 2748) (p 2750) (p 2850) (p 3016) (p 3136) (p 3201) (p 3364) (p 3369) (p 3371) (p 3556) (p 3569) (p 3574) (p 3583) (p 3644) (p 3645) (p 3646) (p 3684) (p 3742) (p 3872) (p 3876) (p 3954) (p 4031) (p 4110) (p 4111) (p 4186) (p 4203) (p 4235) (p 4256) (p 4343) (p 4501) (p 4510) (p 4511) (p 4515) (p 4519) (p 4520) (p 4523) (p 4533) (p 4534) (p 4535) (p 4537) (p 4540) (p 4642) (p 4643) (p 4645) (p 4648) (p 4649) (p 4651) (p 4699) (p 4700) (p 4713) (p 4714) (p 4716) (p 4747) (p 4748) (p 4751) (p 4809) (p 4872) (p 4873) (p 4876) (p 4879) (p 4880) (p 4882) (p 4883) (p 4970) (p 4971) (p 4974) (p 5047) (p 5048) (p 5049) (p 5050) (p 5080) (p 5081) (p 5084) (derived65784 p h) (derived65673 p h) (derived65780 p h) (derived65653 p h) (derived65606 p h) (derived65567 p h) (derived65795 p h) (derived65548 p h) (derived65881 p h) (derived65556 p h) (derived65804 p h) (derived65699 p h) (derived65865 p h) (h 6734) (h 9440) (h 7618) (h 7630) (h 7622) (h 20348) (h 23019) (h 7146) (h 7154) (h 7144) (h 7584) (derived57213 p h) (h 8280) (h 8286) (h 8274) (h 7582) (h 20312) (h 7429) (h 7441) (h 7433) (h 3623) (h 3620) (h 7857) (h 35728) (h 19996) (h 7721) (h 8462) (h 7727) (h 8468) (h 7713) (h 7714) (h 8457) (h 6594) (h 19857) (derived51291 p h) (h 8040) (h 8558) (h 8046) (h 8564) (h 8036) (h 8552) (derived65990 p h) (h 7453) (h 7459) (h 7447) (derived43271 p h) (h 6402) (h 2625) (derived65988 p h) (h 7159) (h 7102) (h 2639) (h 7096) (derived41389 p h) (h 5323) (h 8017) (h 7111) (h 8029) (h 7119) (h 8022) (h 7105) (derived53017 p h)

theorem derived65992 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2870) ∨ (¬ p 2696) ∨ (¬ p 5049) ∨ (¬ p 3556) :=
  ElevenRUP.step65992 (p 2135) (p 2136) (p 2142) (p 2143) (p 2696) (p 2870) (p 3556) (p 4478) (p 5049) (derived65646 p h) (h 6884) (derived50242 p h) (h 2420) (h 2406) (h 7001)

theorem derived65993 (p : Nat → Prop) (h : Inputs p) :
    (p 3020) :=
  ElevenRUP.step65993 (p 878) (p 884) (p 3020) (h 4163) (h 4164) (h 963)

theorem derived65994 (p : Nat → Prop) (h : Inputs p) :
    (p 3021) :=
  ElevenRUP.step65994 (p 3020) (p 3021) (derived65993 p h) (h 4181)

theorem derived65995 (p : Nat → Prop) (h : Inputs p) :
    (p 4977) :=
  ElevenRUP.step65995 (p 3021) (p 4977) (derived65994 p h) (h 8292)

theorem derived65996 (p : Nat → Prop) (h : Inputs p) :
    (p 2511) :=
  ElevenRUP.step65996 (p 398) (p 404) (p 2511) (h 3154) (h 3155) (h 443)

theorem derived65997 (p : Nat → Prop) (h : Inputs p) :
    (p 2512) :=
  ElevenRUP.step65997 (p 2511) (p 2512) (derived65996 p h) (h 3172)

theorem derived65998 (p : Nat → Prop) (h : Inputs p) :
    (p 4682) :=
  ElevenRUP.step65998 (p 2512) (p 4682) (derived65997 p h) (h 7563)

theorem derived65999 (p : Nat → Prop) (h : Inputs p) :
    (p 5865) :=
  ElevenRUP.step65999 (p 4682) (p 5865) (derived65998 p h) (h 12202)

theorem derived66003 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4244) ∨ (¬ p 2819) ∨ (¬ p 3548) ∨ (¬ p 4133) ∨ (¬ p 4024) ∨ (¬ p 3054) ∨ (¬ p 4533) ∨ (¬ p 3646) ∨ (¬ p 3093) ∨ (¬ p 2952) ∨ (¬ p 2750) ∨ (¬ p 4173) ∨ (¬ p 4629) ∨ (¬ p 2252) ∨ (¬ p 3952) ∨ (¬ p 2427) ∨ (¬ p 2563) ∨ (¬ p 3954) ∨ (¬ p 4882) :=
  ElevenRUP.step66003 (p 2252) (p 2427) (p 2563) (p 2750) (p 2819) (p 2881) (p 2891) (p 2901) (p 2952) (p 3051) (p 3054) (p 3093) (p 3548) (p 3554) (p 3556) (p 3570) (p 3646) (p 3952) (p 3954) (p 4024) (p 4133) (p 4173) (p 4244) (p 4320) (p 4533) (p 4629) (p 4882) (p 4899) (p 4900) (p 4903) (p 4907) (p 4908) (p 4912) (p 4915) (p 4916) (p 4918) (p 4982) (p 4983) (p 4987) (derived65681 p h) (derived65642 p h) (derived65649 p h) (derived65729 p h) (derived43934 p h) (derived51441 p h) (h 8110) (h 8321) (h 8116) (h 8327) (h 8102) (h 8315) (derived40975 p h) (derived63244 p h) (h 8092) (h 8127) (h 8098) (h 8133) (h 8086) (h 8121) (derived55177 p h)

theorem derived66004 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4348) ∨ (¬ p 2528) ∨ (¬ p 2299) ∨ (¬ p 2657) ∨ (¬ p 3742) ∨ (¬ p 4712) :=
  ElevenRUP.step66004 (p 2299) (p 2528) (p 2657) (p 3644) (p 3742) (p 3875) (p 4348) (p 4712) (p 4920) (p 4921) (p 4923) (derived65980 p h) (derived49237 p h) (derived44724 p h) (h 8143) (h 8138) (h 8150)

theorem derived66005 (p : Nat → Prop) (h : Inputs p) :
    (p 2284) ∨ (¬ p 4809) ∨ (¬ p 2563) ∨ (¬ p 4557) ∨ (¬ p 4732) ∨ (¬ p 4882) :=
  ElevenRUP.step66005 (p 2143) (p 2166) (p 2177) (p 2187) (p 2192) (p 2210) (p 2220) (p 2230) (p 2241) (p 2244) (p 2247) (p 2251) (p 2252) (p 2253) (p 2254) (p 2274) (p 2284) (p 2299) (p 2363) (p 2396) (p 2406) (p 2417) (p 2427) (p 2437) (p 2440) (p 2449) (p 2459) (p 2509) (p 2518) (p 2528) (p 2534) (p 2563) (p 2588) (p 2619) (p 2630) (p 2651) (p 2654) (p 2657) (p 2661) (p 2685) (p 2717) (p 2740) (p 2741) (p 2747) (p 2748) (p 2750) (p 2753) (p 2761) (p 2774) (p 2777) (p 2780) (p 2784) (p 2797) (p 2819) (p 2829) (p 2850) (p 2860) (p 2870) (p 2881) (p 2901) (p 2911) (p 2946) (p 2949) (p 2951) (p 2952) (p 2956) (p 2992) (p 2995) (p 3051) (p 3054) (p 3063) (p 3073) (p 3083) (p 3093) (p 3125) (p 3136) (p 3146) (p 3246) (p 3266) (p 3309) (p 3319) (p 3322) (p 3323) (p 3399) (p 3412) (p 3449) (p 3452) (p 3461) (p 3483) (p 3527) (p 3548) (p 3549) (p 3555) (p 3574) (p 3576) (p 3588) (p 3591) (p 3644) (p 3645) (p 3646) (p 3659) (p 3662) (p 3688) (p 3690) (p 3692) (p 3694) (p 3696) (p 3697) (p 3742) (p 3744) (p 3745) (p 3868) (p 3872) (p 3873) (p 3880) (p 3917) (p 3920) (p 3923) (p 3945) (p 3947) (p 3952) (p 3954) (p 3955) (p 3956) (p 3957) (p 3969) (p 3989) (p 4024) (p 4026) (p 4037) (p 4110) (p 4111) (p 4112) (p 4116) (p 4133) (p 4140) (p 4153) (p 4154) (p 4173) (p 4191) (p 4193) (p 4200) (p 4202) (p 4203) (p 4235) (p 4241) (p 4243) (p 4244) (p 4256) (p 4261) (p 4278) (p 4316) (p 4317) (p 4320) (p 4330) (p 4343) (p 4344) (p 4347) (p 4348) (p 4355) (p 4358) (p 4381) (p 4384) (p 4441) (p 4444) (p 4452) (p 4490) (p 4491) (p 4492) (p 4495) (p 4499) (p 4500) (p 4501) (p 4502) (p 4504) (p 4505) (p 4508) (p 4510) (p 4511) (p 4512) (p 4515) (p 4519) (p 4520) (p 4523) (p 4526) (p 4527) (p 4530) (p 4533) (p 4534) (p 4535) (p 4537) (p 4540) (p 4557) (p 4558) (p 4561) (p 4562) (p 4565) (p 4593) (p 4594) (p 4597) (p 4599) (p 4600) (p 4602) (p 4605) (p 4606) (p 4609) (p 4610) (p 4618) (p 4619) (p 4620) (p 4622) (p 4626) (p 4627) (p 4629) (p 4630) (p 4633) (p 4634) (p 4639) (p 4642) (p 4643) (p 4645) (p 4646) (p 4648) (p 4649) (p 4651) (p 4654) (p 4655) (p 4659) (p 4664) (p 4665) (p 4667) (p 4682) (p 4683) (p 4686) (p 4691) (p 4692) (p 4694) (p 4698) (p 4699) (p 4700) (p 4703) (p 4706) (p 4707) (p 4709) (p 4712) (p 4713) (p 4714) (p 4716) (p 4732) (p 4738) (p 4739) (p 4743) (p 4747) (p 4748) (p 4751) (p 4762) (p 4775) (p 4776) (p 4778) (p 4780) (p 4791) (p 4792) (p 4795) (p 4798) (p 4799) (p 4803) (p 4809) (p 4815) (p 4821) (p 4822) (p 4827) (p 4831) (p 4833) (p 4839) (p 4840) (p 4842) (p 4844) (p 4855) (p 4856) (p 4860) (p 4864) (p 4865) (p 4868) (p 4872) (p 4873) (p 4874) (p 4876) (p 4879) (p 4880) (p 4882) (p 4883) (p 4886) (p 4887) (p 4890) (p 4892) (p 4893) (p 4896) (p 4899) (p 4900) (p 4901) (p 4903) (p 4915) (p 4916) (p 4918) (p 4920) (p 4921) (p 4923) (p 4931) (p 4955) (p 4956) (p 4958) (p 4991) (p 4992) (p 4996) (p 4999) (p 5000) (p 5003) (p 5006) (p 5007) (p 5010) (p 5013) (p 5014) (p 5019) (p 5041) (p 5042) (p 5044) (p 5047) (p 5048) (p 5050) (p 5054) (p 5055) (p 5057) (p 5100) (p 5101) (p 5103) (p 5114) (p 5115) (p 5120) (p 5139) (p 5140) (p 5143) (p 5146) (p 5147) (p 5151) (p 5188) (p 5189) (p 5192) (p 5194) (p 5245) (p 5246) (p 5251) (p 5262) (p 5263) (p 5268) (p 5272) (p 5273) (p 5277) (p 5303) (p 5304) (p 5306) (p 5499) (p 5500) (p 5503) (p 5506) (p 5554) (p 5555) (p 5558) (p 5561) (p 5562) (p 5566) (p 5567) (p 5568) (p 5571) (derived65784 p h) (derived65780 p h) (derived65853 p h) (derived65733 p h) (derived65844 p h) (derived65661 p h) (derived65556 p h) (derived65881 p h) (derived65800 p h) (derived65804 p h) (derived65613 p h) (derived65865 p h) (derived65500 p h) (derived65520 p h) (derived65606 p h) (derived65567 p h) (derived65827 p h) (derived65709 p h) (derived65836 p h) (derived65687 p h) (derived65699 p h) (derived65583 p h) (derived65673 p h) (derived65795 p h) (derived65741 p h) (derived65716 p h) (derived65622 p h) (derived65771 p h) (derived65748 p h) (derived65923 p h) (derived65626 p h) (derived65998 p h) (derived65448 p h) (derived65895 p h) (derived65791 p h) (derived65634 p h) (derived65638 p h) (derived65810 p h) (derived65758 p h) (derived65597 p h) (derived65630 p h) (derived65729 p h) (derived65649 p h) (derived65540 p h) (derived65720 p h) (derived65944 p h) (derived65571 p h) (derived65460 p h) (derived65516 p h) (derived65464 p h) (derived65775 p h) (derived65694 p h) (derived65980 p h) (derived65848 p h) (derived65587 p h) (derived65528 p h) (derived65356 p h) (derived65472 p h) (derived65376 p h) (derived65352 p h) (derived65705 p h) (derived65617 p h) (derived65690 p h) (derived65563 p h) (h 7857) (h 7856) (h 7208) (h 9440) (h 7618) (h 7630) (h 7622) (h 6680) (h 7601) (h 7613) (h 7609) (h 7606) (h 7207) (h 20312) (h 7429) (h 7441) (h 7436) (h 5739) (h 7209) (h 7206) (h 7681) (h 7680) (h 7679) (h 7226) (h 6533) (h 7232) (h 7588) (h 7218) (h 7219) (h 7220) (h 7596) (h 7582) (h 7584) (h 27082) (h 20017) (derived46112 p h) (derived52915 p h) (h 20082) (h 6201) (h 8246) (h 2625) (h 7453) (h 7401) (h 8252) (h 7159) (h 7459) (h 7407) (h 8239) (h 2637) (h 2638) (h 2639) (h 2640) (h 7445) (h 7447) (h 7393) (h 7397) (h 6237) (h 20007) (h 6267) (h 6413) (derived42642 p h) (h 7096) (h 3606) (h 7107) (h 6295) (h 7102) (h 7875) (h 7119) (h 8799) (h 7088) (h 7089) (h 3620) (h 3623) (h 7111) (h 7113) (h 8811) (derived61082 p h) (h 35728) (h 19996) (h 33848) (h 38656) (derived51595 p h) (derived49229 p h) (h 29892) (derived41941 p h) (h 8807) (h 8705) (h 7721) (h 8462) (h 7953) (h 7794) (h 3449) (h 4042) (h 8015) (h 8386) (derived59873 p h) (h 8717) (h 7727) (h 8468) (h 7959) (h 7800) (h 7750) (h 8182) (h 8029) (h 8398) (h 7148) (h 8710) (h 8711) (h 7714) (h 8455) (h 7948) (h 7789) (h 3435) (h 4027) (h 4028) (h 8021) (h 8392) (h 7154) (h 19857) (h 20521) (derived49201 p h) (derived41580 p h) (h 5865) (derived44033 p h) (h 17146) (h 25108) (derived52571 p h) (h 7144) (h 8040) (h 8057) (h 8000) (h 7823) (h 7343) (h 7062) (h 8046) (h 8063) (h 8012) (h 7835) (h 7355) (h 7068) (h 8032) (h 8049) (h 8004) (h 8006) (h 7827) (h 7348) (h 7350) (h 7054) (h 7056) (h 7057) (h 7058) (derived42276 p h) (derived42709 p h) (derived41927 p h) (derived60034 p h) (derived50065 p h) (derived60774 p h) (h 3683) (h 7846) (h 7556) (h 9044) (h 7309) (h 7073) (h 7920) (h 7852) (h 7562) (h 9050) (h 7321) (h 7085) (h 3697) (h 7840) (h 7550) (h 9038) (h 7317) (h 7077) (h 7079) (derived55680 p h) (derived53093 p h) (h 8375) (h 8334) (h 8381) (h 8346) (h 8369) (h 8339) (h 8340) (h 26882) (derived63247 p h) (derived46449 p h) (h 7983) (h 7332) (h 7995) (h 7338) (h 7989) (h 7324) (h 7326) (h 7328) (derived46832 p h) (h 8357) (h 8363) (h 8351) (derived66003 p h) (h 8068) (h 6664) (h 8080) (h 8121) (h 8072) (h 8074) (h 8133) (h 19748) (h 6716) (h 8126) (h 8127) (h 8092) (derived63093 p h) (derived54932 p h) (h 8098) (h 8615) (h 7384) (h 8087) (h 8621) (h 7390) (h 8609) (h 7379) (derived51033 p h) (derived41348 p h) (h 7470) (h 8439) (h 7476) (h 8451) (h 7464) (h 8445) (derived49369 p h) (derived41115 p h) (h 8981) (h 8723) (h 8993) (h 8735) (h 8987) (h 8729) (derived59844 p h) (derived52093 p h) (h 8962) (h 7567) (h 8974) (h 7579) (h 8968) (h 7573) (derived66004 p h) (h 7481) (h 7493) (h 7486) (h 7487) (derived49633 p h) (h 8144) (h 8150) (h 8138) (derived58899 p h) (h 7418) (h 7424) (h 7412) (derived44820 p h) (h 7902) (h 7914) (h 7908) (h 7910) (derived41811 p h) (h 8646) (h 8658) (h 8651) (h 8652) (h 20091) (derived41469 p h) (h 9721) (h 8928) (h 9733) (h 8940) (h 9725) (h 8934) (derived50996 p h) (h 9583) (h 9595) (h 9589) (derived54078 p h) (h 9791) (h 9803) (h 9797) (derived45725 p h) (h 7130) (h 6704) (h 7136) (h 7704) (h 7122) (h 7123) (h 7710) (h 11852) (h 7698) (h 7045) (derived49801 p h) (h 7051) (h 8473) (h 7037) (h 8485) (derived62130 p h) (h 8479)

theorem derived66007 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4173) ∨ (¬ p 3591) ∨ (¬ p 4629) ∨ (¬ p 2241) ∨ (¬ p 2563) :=
  ElevenRUP.step66007 (p 2192) (p 2210) (p 2241) (p 2563) (p 3555) (p 3591) (p 3957) (p 4173) (p 4510) (p 4511) (p 4515) (p 4519) (p 4520) (p 4523) (p 4629) (derived65804 p h) (derived65865 p h) (h 9774) (derived42642 p h) (h 7096) (h 7107) (h 7102) (h 7119) (h 7089) (h 7113) (derived41941 p h)

theorem derived66009 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3483) ∨ (¬ p 2315) ∨ (¬ p 3821) ∨ (¬ p 3822) ∨ (p 2122) :=
  ElevenRUP.step66009 (p 2122) (p 2315) (p 3483) (p 3821) (p 3822) (p 4025) (p 4618) (p 4619) (p 4622) (p 4623) (derived65720 p h) (h 38128) (derived48783 p h) (h 7376) (h 7382) (h 7390)

theorem derived66321 (p : Nat → Prop) (h : Inputs p) :
    (p 2101) ∨ (p 2108) :=
  ElevenRUP.step66321 (p 2101) (p 2108) (p 4464) (derived65610 p h) (h 6963)

theorem derived66324 (p : Nat → Prop) (h : Inputs p) :
    (p 4474) ∨ (p 4470) :=
  ElevenRUP.step66324 (p 4469) (p 4470) (p 4474) (derived65926 p h) (h 6996)

theorem derived66325 (p : Nat → Prop) (h : Inputs p) :
    (p 2135) ∨ (p 2142) :=
  ElevenRUP.step66325 (p 2135) (p 2142) (p 4478) (derived65646 p h) (h 7001)

theorem derived66328 (p : Nat → Prop) (h : Inputs p) :
    (p 4487) ∨ (p 4484) :=
  ElevenRUP.step66328 (p 4483) (p 4484) (p 4487) (derived65737 p h) (h 7034)

theorem derived66329 (p : Nat → Prop) (h : Inputs p) :
    (p 4491) ∨ (p 4495) :=
  ElevenRUP.step66329 (p 4490) (p 4491) (p 4495) (derived65690 p h) (h 7051)

theorem derived66330 (p : Nat → Prop) (h : Inputs p) :
    (p 4502) ∨ (p 4500) :=
  ElevenRUP.step66330 (p 4499) (p 4500) (p 4502) (derived65748 p h) (h 7068)

theorem derived66331 (p : Nat → Prop) (h : Inputs p) :
    (p 4508) ∨ (p 4505) :=
  ElevenRUP.step66331 (p 4504) (p 4505) (p 4508) (derived65791 p h) (h 7085)

theorem derived66332 (p : Nat → Prop) (h : Inputs p) :
    (p 4511) ∨ (p 4515) :=
  ElevenRUP.step66332 (p 4510) (p 4511) (p 4515) (derived65804 p h) (h 7102)

theorem derived66333 (p : Nat → Prop) (h : Inputs p) :
    (p 4523) ∨ (p 4520) :=
  ElevenRUP.step66333 (p 4519) (p 4520) (p 4523) (derived65865 p h) (h 7119)

theorem derived66334 (p : Nat → Prop) (h : Inputs p) :
    (p 4527) ∨ (p 4530) :=
  ElevenRUP.step66334 (p 4526) (p 4527) (p 4530) (derived65705 p h) (h 7136)

theorem derived66335 (p : Nat → Prop) (h : Inputs p) :
    (p 4535) ∨ (p 4537) :=
  ElevenRUP.step66335 (p 4534) (p 4535) (p 4537) (derived65673 p h) (h 7154)

theorem derived66336 (p : Nat → Prop) (h : Inputs p) :
    (p 2244) ∨ (p 2251) :=
  ElevenRUP.step66336 (p 2244) (p 2251) (p 4540) (derived65556 p h) (h 7159)

theorem derived66339 (p : Nat → Prop) (h : Inputs p) :
    (p 4551) ∨ (p 4547) :=
  ElevenRUP.step66339 (p 4546) (p 4547) (p 4551) (derived65938 p h) (h 7197)

theorem derived66340 (p : Nat → Prop) (h : Inputs p) :
    (p 4554) ∨ (p 4557) :=
  ElevenRUP.step66340 (p 4553) (p 4554) (p 4557) (derived65724 p h) (h 7214)

theorem derived66341 (p : Nat → Prop) (h : Inputs p) :
    (p 4565) ∨ (p 4562) :=
  ElevenRUP.step66341 (p 4561) (p 4562) (p 4565) (derived65733 p h) (h 7232)

theorem derived66342 (p : Nat → Prop) (h : Inputs p) :
    (p 4571) ∨ (p 4568) :=
  ElevenRUP.step66342 (p 4567) (p 4568) (p 4571) (derived65887 p h) (h 7249)

theorem derived66343 (p : Nat → Prop) (h : Inputs p) :
    (p 2317) ∨ (p 2310) :=
  ElevenRUP.step66343 (p 2310) (p 2317) (p 4573) (derived65754 p h) (h 7254)

theorem derived66346 (p : Nat → Prop) (h : Inputs p) :
    (p 4579) ∨ (p 4582) :=
  ElevenRUP.step66346 (p 4578) (p 4579) (p 4582) (derived65823 p h) (h 7287)

theorem derived66347 (p : Nat → Prop) (h : Inputs p) :
    (p 4589) ∨ (p 4586) :=
  ElevenRUP.step66347 (p 4585) (p 4586) (p 4589) (derived65767 p h) (h 7304)

theorem derived66348 (p : Nat → Prop) (h : Inputs p) :
    (p 4597) ∨ (p 4594) :=
  ElevenRUP.step66348 (p 4593) (p 4594) (p 4597) (derived65895 p h) (h 7321)

theorem derived66349 (p : Nat → Prop) (h : Inputs p) :
    (p 4602) ∨ (p 4600) :=
  ElevenRUP.step66349 (p 4599) (p 4600) (p 4602) (derived65758 p h) (h 7338)

theorem derived66350 (p : Nat → Prop) (h : Inputs p) :
    (p 4609) ∨ (p 4606) :=
  ElevenRUP.step66350 (p 4605) (p 4606) (p 4609) (derived65771 p h) (h 7355)

theorem derived66351 (p : Nat → Prop) (h : Inputs p) :
    (p 4615) ∨ (p 4612) :=
  ElevenRUP.step66351 (p 4611) (p 4612) (p 4615) (derived65763 p h) (h 7373)

theorem derived66352 (p : Nat → Prop) (h : Inputs p) :
    (p 4619) ∨ (p 4622) :=
  ElevenRUP.step66352 (p 4618) (p 4619) (p 4622) (derived65720 p h) (h 7390)

theorem derived66353 (p : Nat → Prop) (h : Inputs p) :
    (p 4627) ∨ (p 4630) :=
  ElevenRUP.step66353 (p 4626) (p 4627) (p 4630) (derived65800 p h) (h 7407)

theorem derived66354 (p : Nat → Prop) (h : Inputs p) :
    (p 4634) ∨ (p 4639) :=
  ElevenRUP.step66354 (p 4633) (p 4634) (p 4639) (derived65848 p h) (h 7424)

theorem derived66355 (p : Nat → Prop) (h : Inputs p) :
    (p 4643) ∨ (p 4645) :=
  ElevenRUP.step66355 (p 4642) (p 4643) (p 4645) (derived65784 p h) (h 7441)

theorem derived66356 (p : Nat → Prop) (h : Inputs p) :
    (p 4651) ∨ (p 4649) :=
  ElevenRUP.step66356 (p 4648) (p 4649) (p 4651) (derived65881 p h) (h 7459)

theorem derived66357 (p : Nat → Prop) (h : Inputs p) :
    (p 4655) ∨ (p 4659) :=
  ElevenRUP.step66357 (p 4654) (p 4655) (p 4659) (derived65944 p h) (h 7476)

theorem derived66358 (p : Nat → Prop) (h : Inputs p) :
    (p 4665) ∨ (p 4667) :=
  ElevenRUP.step66358 (p 4664) (p 4665) (p 4667) (derived65694 p h) (h 7493)

theorem derived66359 (p : Nat → Prop) (h : Inputs p) :
    (p 2480) ∨ (p 2473) :=
  ElevenRUP.step66359 (p 2473) (p 2480) (p 4670) (derived65891 p h) (h 7498)

theorem derived66362 (p : Nat → Prop) (h : Inputs p) :
    (p 2496) ∨ (p 2503) :=
  ElevenRUP.step66362 (p 2496) (p 2503) (p 4676) (derived65820 p h) (h 7524)

theorem derived66365 (p : Nat → Prop) (h : Inputs p) :
    (p 4683) ∨ (p 4686) :=
  ElevenRUP.step66365 (p 4682) (p 4683) (p 4686) (derived65998 p h) (h 7562)

theorem derived66366 (p : Nat → Prop) (h : Inputs p) :
    (p 4692) ∨ (p 4694) :=
  ElevenRUP.step66366 (p 4691) (p 4692) (p 4694) (derived65775 p h) (h 7579)

theorem derived66367 (p : Nat → Prop) (h : Inputs p) :
    (p 4703) ∨ (p 4699) :=
  ElevenRUP.step66367 (p 4698) (p 4699) (p 4703) (derived65844 p h) (h 7596)

theorem derived66368 (p : Nat → Prop) (h : Inputs p) :
    (p 4709) ∨ (p 4707) :=
  ElevenRUP.step66368 (p 4706) (p 4707) (p 4709) (derived65853 p h) (h 7613)

theorem derived66369 (p : Nat → Prop) (h : Inputs p) :
    (p 4714) ∨ (p 4716) :=
  ElevenRUP.step66369 (p 4713) (p 4714) (p 4716) (derived65780 p h) (h 7630)

theorem derived66370 (p : Nat → Prop) (h : Inputs p) :
    (p 2576) ∨ (p 2583) :=
  ElevenRUP.step66370 (p 2576) (p 2583) (p 4719) (derived65841 p h) (h 7636)

theorem derived66373 (p : Nat → Prop) (h : Inputs p) :
    (p 4728) ∨ (p 4726) :=
  ElevenRUP.step66373 (p 4725) (p 4726) (p 4728) (derived65591 p h) (h 7676)

theorem derived66374 (p : Nat → Prop) (h : Inputs p) :
    (p 4732) ∨ (p 4735) :=
  ElevenRUP.step66374 (p 4731) (p 4732) (p 4735) (derived65532 p h) (h 7693)

theorem derived66375 (p : Nat → Prop) (h : Inputs p) :
    (p 4739) ∨ (p 4743) :=
  ElevenRUP.step66375 (p 4738) (p 4739) (p 4743) (derived65617 p h) (h 7710)

theorem derived66376 (p : Nat → Prop) (h : Inputs p) :
    (p 4751) ∨ (p 4748) :=
  ElevenRUP.step66376 (p 4747) (p 4748) (p 4751) (derived65606 p h) (h 7727)

theorem derived66377 (p : Nat → Prop) (h : Inputs p) :
    (p 4758) ∨ (p 4755) :=
  ElevenRUP.step66377 (p 4754) (p 4755) (p 4758) (derived65665 p h) (h 7745)

theorem derived66378 (p : Nat → Prop) (h : Inputs p) :
    (p 2654) ∨ (p 2661) :=
  ElevenRUP.step66378 (p 2654) (p 2661) (p 4762) (derived65836 p h) (h 7750)

theorem derived66381 (p : Nat → Prop) (h : Inputs p) :
    (p 4772) ∨ (p 4768) :=
  ElevenRUP.step66381 (p 4767) (p 4768) (p 4772) (derived65859 p h) (h 7783)

theorem derived66382 (p : Nat → Prop) (h : Inputs p) :
    (p 4776) ∨ (p 4780) :=
  ElevenRUP.step66382 (p 4775) (p 4776) (p 4780) (derived65709 p h) (h 7800)

theorem derived66383 (p : Nat → Prop) (h : Inputs p) :
    (p 4785) ∨ (p 4788) :=
  ElevenRUP.step66383 (p 4784) (p 4785) (p 4788) (derived65602 p h) (h 7817)

theorem derived66384 (p : Nat → Prop) (h : Inputs p) :
    (p 4792) ∨ (p 4795) :=
  ElevenRUP.step66384 (p 4791) (p 4792) (p 4795) (derived65622 p h) (h 7835)

theorem derived66385 (p : Nat → Prop) (h : Inputs p) :
    (p 4803) ∨ (p 4799) :=
  ElevenRUP.step66385 (p 4798) (p 4799) (p 4803) (derived65626 p h) (h 7852)

theorem derived66386 (p : Nat → Prop) (h : Inputs p) :
    (p 4809) ∨ (p 4812) :=
  ElevenRUP.step66386 (p 4808) (p 4809) (p 4812) (derived65831 p h) (h 7869)

theorem derived66387 (p : Nat → Prop) (h : Inputs p) :
    (p 2740) ∨ (p 2747) :=
  ElevenRUP.step66387 (p 2740) (p 2747) (p 4815) (derived65613 p h) (h 7875)

theorem derived66390 (p : Nat → Prop) (h : Inputs p) :
    (p 4827) ∨ (p 4822) :=
  ElevenRUP.step66390 (p 4821) (p 4822) (p 4827) (derived65587 p h) (h 7914)

theorem derived66391 (p : Nat → Prop) (h : Inputs p) :
    (p 2784) ∨ (p 2777) :=
  ElevenRUP.step66391 (p 2777) (p 2784) (p 4833) (derived65923 p h) (h 7920)

theorem derived66394 (p : Nat → Prop) (h : Inputs p) :
    (p 4844) ∨ (p 4840) :=
  ElevenRUP.step66394 (p 4839) (p 4840) (p 4844) (derived65827 p h) (h 7959)

theorem derived66395 (p : Nat → Prop) (h : Inputs p) :
    (p 4856) ∨ (p 4860) :=
  ElevenRUP.step66395 (p 4855) (p 4856) (p 4860) (derived65810 p h) (h 7995)

theorem derived66396 (p : Nat → Prop) (h : Inputs p) :
    (p 4865) ∨ (p 4868) :=
  ElevenRUP.step66396 (p 4864) (p 4865) (p 4868) (derived65716 p h) (h 8012)

theorem derived66397 (p : Nat → Prop) (h : Inputs p) :
    (p 4873) ∨ (p 4876) :=
  ElevenRUP.step66397 (p 4872) (p 4873) (p 4876) (derived65699 p h) (h 8029)

theorem derived66398 (p : Nat → Prop) (h : Inputs p) :
    (p 4880) ∨ (p 4883) :=
  ElevenRUP.step66398 (p 4879) (p 4880) (p 4883) (derived65795 p h) (h 8046)

theorem derived66399 (p : Nat → Prop) (h : Inputs p) :
    (p 4887) ∨ (p 4890) :=
  ElevenRUP.step66399 (p 4886) (p 4887) (p 4890) (derived65741 p h) (h 8063)

theorem derived66400 (p : Nat → Prop) (h : Inputs p) :
    (p 4896) ∨ (p 4893) :=
  ElevenRUP.step66400 (p 4892) (p 4893) (p 4896) (derived65630 p h) (h 8080)

theorem derived66401 (p : Nat → Prop) (h : Inputs p) :
    (p 4903) ∨ (p 4900) :=
  ElevenRUP.step66401 (p 4899) (p 4900) (p 4903) (derived65649 p h) (h 8098)

theorem derived66402 (p : Nat → Prop) (h : Inputs p) :
    (p 4912) ∨ (p 4908) :=
  ElevenRUP.step66402 (p 4907) (p 4908) (p 4912) (derived65681 p h) (h 8116)

theorem derived66403 (p : Nat → Prop) (h : Inputs p) :
    (p 4916) ∨ (p 4918) :=
  ElevenRUP.step66403 (p 4915) (p 4916) (p 4918) (derived65729 p h) (h 8133)

theorem derived66404 (p : Nat → Prop) (h : Inputs p) :
    (p 4923) ∨ (p 4921) :=
  ElevenRUP.step66404 (p 4920) (p 4921) (p 4923) (derived65980 p h) (h 8150)

theorem derived66405 (p : Nat → Prop) (h : Inputs p) :
    (p 2932) ∨ (p 2925) :=
  ElevenRUP.step66405 (p 2925) (p 2932) (p 4925) (derived65902 p h) (h 8155)

theorem derived66408 (p : Nat → Prop) (h : Inputs p) :
    (p 2956) ∨ (p 2949) :=
  ElevenRUP.step66408 (p 2949) (p 2956) (p 4931) (derived65687 p h) (h 8182)

theorem derived66411 (p : Nat → Prop) (h : Inputs p) :
    (p 4937) ∨ (p 4941) :=
  ElevenRUP.step66411 (p 4936) (p 4937) (p 4941) (derived65677 p h) (h 8218)

theorem derived66412 (p : Nat → Prop) (h : Inputs p) :
    (p 4946) ∨ (p 4951) :=
  ElevenRUP.step66412 (p 4945) (p 4946) (p 4951) (derived65669 p h) (h 8235)

theorem derived66413 (p : Nat → Prop) (h : Inputs p) :
    (p 4956) ∨ (p 4958) :=
  ElevenRUP.step66413 (p 4955) (p 4956) (p 4958) (derived65661 p h) (h 8252)

theorem derived66414 (p : Nat → Prop) (h : Inputs p) :
    (p 4966) ∨ (p 4962) :=
  ElevenRUP.step66414 (p 4961) (p 4962) (p 4966) (derived65657 p h) (h 8269)

theorem derived66415 (p : Nat → Prop) (h : Inputs p) :
    (p 4974) ∨ (p 4971) :=
  ElevenRUP.step66415 (p 4970) (p 4971) (p 4974) (derived65653 p h) (h 8286)

theorem derived66416 (p : Nat → Prop) (h : Inputs p) :
    (p 3036) ∨ (p 3030) :=
  ElevenRUP.step66416 (p 3030) (p 3036) (p 4977) (derived65995 p h) (h 8291)

theorem derived66419 (p : Nat → Prop) (h : Inputs p) :
    (p 4983) ∨ (p 4987) :=
  ElevenRUP.step66419 (p 4982) (p 4983) (p 4987) (derived65642 p h) (h 8327)

theorem derived66420 (p : Nat → Prop) (h : Inputs p) :
    (p 4992) ∨ (p 4996) :=
  ElevenRUP.step66420 (p 4991) (p 4992) (p 4996) (derived65638 p h) (h 8346)

theorem derived66421 (p : Nat → Prop) (h : Inputs p) :
    (p 5003) ∨ (p 5000) :=
  ElevenRUP.step66421 (p 4999) (p 5000) (p 5003) (derived65597 p h) (h 8363)

theorem derived66422 (p : Nat → Prop) (h : Inputs p) :
    (p 5007) ∨ (p 5010) :=
  ElevenRUP.step66422 (p 5006) (p 5007) (p 5010) (derived65634 p h) (h 8381)

theorem derived66423 (p : Nat → Prop) (h : Inputs p) :
    (p 5019) ∨ (p 5014) :=
  ElevenRUP.step66423 (p 5013) (p 5014) (p 5019) (derived65583 p h) (h 8398)

theorem derived66424 (p : Nat → Prop) (h : Inputs p) :
    (p 5024) ∨ (p 5029) :=
  ElevenRUP.step66424 (p 5023) (p 5024) (p 5029) (derived65579 p h) (h 8417)

theorem derived66425 (p : Nat → Prop) (h : Inputs p) :
    (p 5035) ∨ (p 5037) :=
  ElevenRUP.step66425 (p 5034) (p 5035) (p 5037) (derived65575 p h) (h 8434)

theorem derived66426 (p : Nat → Prop) (h : Inputs p) :
    (p 5042) ∨ (p 5044) :=
  ElevenRUP.step66426 (p 5041) (p 5042) (p 5044) (derived65571 p h) (h 8451)

theorem derived66427 (p : Nat → Prop) (h : Inputs p) :
    (p 5048) ∨ (p 5050) :=
  ElevenRUP.step66427 (p 5047) (p 5048) (p 5050) (derived65567 p h) (h 8468)

theorem derived66428 (p : Nat → Prop) (h : Inputs p) :
    (p 5055) ∨ (p 5057) :=
  ElevenRUP.step66428 (p 5054) (p 5055) (p 5057) (derived65563 p h) (h 8485)

theorem derived66429 (p : Nat → Prop) (h : Inputs p) :
    (p 5061) ∨ (p 5064) :=
  ElevenRUP.step66429 (p 5060) (p 5061) (p 5064) (derived65559 p h) (h 8502)

theorem derived66430 (p : Nat → Prop) (h : Inputs p) :
    (p 5073) ∨ (p 5077) :=
  ElevenRUP.step66430 (p 5072) (p 5073) (p 5077) (derived65552 p h) (h 8546)

theorem derived66431 (p : Nat → Prop) (h : Inputs p) :
    (p 5081) ∨ (p 5084) :=
  ElevenRUP.step66431 (p 5080) (p 5081) (p 5084) (derived65548 p h) (h 8564)

theorem derived66432 (p : Nat → Prop) (h : Inputs p) :
    (p 5089) ∨ (p 5092) :=
  ElevenRUP.step66432 (p 5088) (p 5089) (p 5092) (derived65544 p h) (h 8583)

theorem derived66433 (p : Nat → Prop) (h : Inputs p) :
    (p 3225) ∨ (p 3231) :=
  ElevenRUP.step66433 (p 3225) (p 3231) (p 5095) (derived65814 p h) (h 8588)

theorem derived66436 (p : Nat → Prop) (h : Inputs p) :
    (p 5101) ∨ (p 5103) :=
  ElevenRUP.step66436 (p 5100) (p 5101) (p 5103) (derived65540 p h) (h 8621)

theorem derived66437 (p : Nat → Prop) (h : Inputs p) :
    (p 5106) ∨ (p 5110) :=
  ElevenRUP.step66437 (p 5105) (p 5106) (p 5110) (derived65536 p h) (h 8640)

theorem derived66438 (p : Nat → Prop) (h : Inputs p) :
    (p 5115) ∨ (p 5120) :=
  ElevenRUP.step66438 (p 5114) (p 5115) (p 5120) (derived65528 p h) (h 8658)

theorem derived66439 (p : Nat → Prop) (h : Inputs p) :
    (p 5125) ∨ (p 5130) :=
  ElevenRUP.step66439 (p 5124) (p 5125) (p 5130) (derived65524 p h) (h 8676)

theorem derived66440 (p : Nat → Prop) (h : Inputs p) :
    (p 5140) ∨ (p 5143) :=
  ElevenRUP.step66440 (p 5139) (p 5140) (p 5143) (derived65520 p h) (h 8717)

theorem derived66441 (p : Nat → Prop) (h : Inputs p) :
    (p 5147) ∨ (p 5151) :=
  ElevenRUP.step66441 (p 5146) (p 5147) (p 5151) (derived65516 p h) (h 8735)

theorem derived66442 (p : Nat → Prop) (h : Inputs p) :
    (p 5157) ∨ (p 5163) :=
  ElevenRUP.step66442 (p 5156) (p 5157) (p 5163) (derived65512 p h) (h 8753)

theorem derived66443 (p : Nat → Prop) (h : Inputs p) :
    (p 5169) ∨ (p 5174) :=
  ElevenRUP.step66443 (p 5168) (p 5169) (p 5174) (derived65508 p h) (h 8771)

theorem derived66444 (p : Nat → Prop) (h : Inputs p) :
    (p 5180) ∨ (p 5185) :=
  ElevenRUP.step66444 (p 5179) (p 5180) (p 5185) (derived65504 p h) (h 8788)

theorem derived66445 (p : Nat → Prop) (h : Inputs p) :
    (p 5189) ∨ (p 5192) :=
  ElevenRUP.step66445 (p 5188) (p 5189) (p 5192) (derived65500 p h) (h 8811)

theorem derived66446 (p : Nat → Prop) (h : Inputs p) :
    (p 5196) ∨ (p 5200) :=
  ElevenRUP.step66446 (p 5195) (p 5196) (p 5200) (derived65496 p h) (h 8828)

theorem derived66447 (p : Nat → Prop) (h : Inputs p) :
    (p 5209) ∨ (p 5205) :=
  ElevenRUP.step66447 (p 5204) (p 5205) (p 5209) (derived65492 p h) (h 8845)

theorem derived66448 (p : Nat → Prop) (h : Inputs p) :
    (p 5215) ∨ (p 5213) :=
  ElevenRUP.step66448 (p 5212) (p 5213) (p 5215) (derived65488 p h) (h 8865)

theorem derived66449 (p : Nat → Prop) (h : Inputs p) :
    (p 5219) ∨ (p 5223) :=
  ElevenRUP.step66449 (p 5218) (p 5219) (p 5223) (derived65484 p h) (h 8885)

theorem derived66450 (p : Nat → Prop) (h : Inputs p) :
    (p 5227) ∨ (p 5232) :=
  ElevenRUP.step66450 (p 5226) (p 5227) (p 5232) (derived65480 p h) (h 8905)

theorem derived66451 (p : Nat → Prop) (h : Inputs p) :
    (p 5241) ∨ (p 5238) :=
  ElevenRUP.step66451 (p 5237) (p 5238) (p 5241) (derived65476 p h) (h 8923)

theorem derived66452 (p : Nat → Prop) (h : Inputs p) :
    (p 5246) ∨ (p 5251) :=
  ElevenRUP.step66452 (p 5245) (p 5246) (p 5251) (derived65472 p h) (h 8940)

theorem derived66453 (p : Nat → Prop) (h : Inputs p) :
    (p 5259) ∨ (p 5256) :=
  ElevenRUP.step66453 (p 5255) (p 5256) (p 5259) (derived65468 p h) (h 8957)

theorem derived66454 (p : Nat → Prop) (h : Inputs p) :
    (p 5263) ∨ (p 5268) :=
  ElevenRUP.step66454 (p 5262) (p 5263) (p 5268) (derived65464 p h) (h 8974)

theorem derived66455 (p : Nat → Prop) (h : Inputs p) :
    (p 5273) ∨ (p 5277) :=
  ElevenRUP.step66455 (p 5272) (p 5273) (p 5277) (derived65460 p h) (h 8993)

theorem derived66456 (p : Nat → Prop) (h : Inputs p) :
    (p 5281) ∨ (p 5287) :=
  ElevenRUP.step66456 (p 5280) (p 5281) (p 5287) (derived65456 p h) (h 9014)

theorem derived66457 (p : Nat → Prop) (h : Inputs p) :
    (p 5293) ∨ (p 5298) :=
  ElevenRUP.step66457 (p 5292) (p 5293) (p 5298) (derived65452 p h) (h 9031)

theorem derived66458 (p : Nat → Prop) (h : Inputs p) :
    (p 5304) ∨ (p 5306) :=
  ElevenRUP.step66458 (p 5303) (p 5304) (p 5306) (derived65448 p h) (h 9050)

theorem derived66459 (p : Nat → Prop) (h : Inputs p) :
    (p 5311) ∨ (p 5314) :=
  ElevenRUP.step66459 (p 5310) (p 5311) (p 5314) (derived65444 p h) (h 9073)

theorem derived66460 (p : Nat → Prop) (h : Inputs p) :
    (p 5320) ∨ (p 5323) :=
  ElevenRUP.step66460 (p 5319) (p 5320) (p 5323) (derived65440 p h) (h 9114)

theorem derived66461 (p : Nat → Prop) (h : Inputs p) :
    (p 5327) ∨ (p 5331) :=
  ElevenRUP.step66461 (p 5326) (p 5327) (p 5331) (derived65436 p h) (h 9170)

theorem derived66462 (p : Nat → Prop) (h : Inputs p) :
    (p 5337) ∨ (p 5342) :=
  ElevenRUP.step66462 (p 5336) (p 5337) (p 5342) (derived65432 p h) (h 9187)

theorem derived66463 (p : Nat → Prop) (h : Inputs p) :
    (p 5348) ∨ (p 5351) :=
  ElevenRUP.step66463 (p 5347) (p 5348) (p 5351) (derived65428 p h) (h 9204)

theorem derived66464 (p : Nat → Prop) (h : Inputs p) :
    (p 5356) ∨ (p 5361) :=
  ElevenRUP.step66464 (p 5355) (p 5356) (p 5361) (derived65424 p h) (h 9223)

theorem derived66465 (p : Nat → Prop) (h : Inputs p) :
    (p 5367) ∨ (p 5372) :=
  ElevenRUP.step66465 (p 5366) (p 5367) (p 5372) (derived65420 p h) (h 9247)

theorem derived66466 (p : Nat → Prop) (h : Inputs p) :
    (p 5377) ∨ (p 5382) :=
  ElevenRUP.step66466 (p 5376) (p 5377) (p 5382) (derived65416 p h) (h 9267)

theorem derived66467 (p : Nat → Prop) (h : Inputs p) :
    (p 5386) ∨ (p 5390) :=
  ElevenRUP.step66467 (p 5385) (p 5386) (p 5390) (derived65412 p h) (h 9303)

theorem derived66468 (p : Nat → Prop) (h : Inputs p) :
    (p 5396) ∨ (p 5401) :=
  ElevenRUP.step66468 (p 5395) (p 5396) (p 5401) (derived65408 p h) (h 9320)

theorem derived66469 (p : Nat → Prop) (h : Inputs p) :
    (p 5407) ∨ (p 5412) :=
  ElevenRUP.step66469 (p 5406) (p 5407) (p 5412) (derived65404 p h) (h 9351)

theorem derived66470 (p : Nat → Prop) (h : Inputs p) :
    (p 5418) ∨ (p 5424) :=
  ElevenRUP.step66470 (p 5417) (p 5418) (p 5424) (derived65400 p h) (h 9368)

theorem derived66471 (p : Nat → Prop) (h : Inputs p) :
    (p 5430) ∨ (p 5436) :=
  ElevenRUP.step66471 (p 5429) (p 5430) (p 5436) (derived65396 p h) (h 9386)

theorem derived66472 (p : Nat → Prop) (h : Inputs p) :
    (p 5442) ∨ (p 5446) :=
  ElevenRUP.step66472 (p 5441) (p 5442) (p 5446) (derived65392 p h) (h 9404)

theorem derived66473 (p : Nat → Prop) (h : Inputs p) :
    (p 5452) ∨ (p 5457) :=
  ElevenRUP.step66473 (p 5451) (p 5452) (p 5457) (derived65388 p h) (h 9436)

theorem derived66474 (p : Nat → Prop) (h : Inputs p) :
    (p 3777) ∨ (p 3770) :=
  ElevenRUP.step66474 (p 3770) (p 3777) (p 5462) (derived65713 p h) (h 9454)

theorem derived66477 (p : Nat → Prop) (h : Inputs p) :
    (p 5469) ∨ (p 5474) :=
  ElevenRUP.step66477 (p 5468) (p 5469) (p 5474) (derived65384 p h) (h 9493)

theorem derived66478 (p : Nat → Prop) (h : Inputs p) :
    (p 5485) ∨ (p 5490) :=
  ElevenRUP.step66478 (p 5484) (p 5485) (p 5490) (derived65380 p h) (h 9545)

theorem derived66479 (p : Nat → Prop) (h : Inputs p) :
    (p 5500) ∨ (p 5506) :=
  ElevenRUP.step66479 (p 5499) (p 5500) (p 5506) (derived65376 p h) (h 9595)

theorem derived66480 (p : Nat → Prop) (h : Inputs p) :
    (p 5512) ∨ (p 5517) :=
  ElevenRUP.step66480 (p 5511) (p 5512) (p 5517) (derived65372 p h) (h 9634)

theorem derived66482 (p : Nat → Prop) (h : Inputs p) :
    (p 5533) ∨ (p 5538) :=
  ElevenRUP.step66482 (p 5532) (p 5533) (p 5538) (derived65364 p h) (h 9673)

theorem derived66483 (p : Nat → Prop) (h : Inputs p) :
    (p 5544) ∨ (p 5549) :=
  ElevenRUP.step66483 (p 5543) (p 5544) (p 5549) (derived65360 p h) (h 9715)

theorem derived66484 (p : Nat → Prop) (h : Inputs p) :
    (p 5555) ∨ (p 5561) :=
  ElevenRUP.step66484 (p 5554) (p 5555) (p 5561) (derived65356 p h) (h 9733)

theorem derived66485 (p : Nat → Prop) (h : Inputs p) :
    (p 5567) ∨ (p 5571) :=
  ElevenRUP.step66485 (p 5566) (p 5567) (p 5571) (derived65352 p h) (h 9803)

theorem derived66486 (p : Nat → Prop) (h : Inputs p) :
    (p 5577) ∨ (p 5583) :=
  ElevenRUP.step66486 (p 5576) (p 5577) (p 5583) (derived65348 p h) (h 9820)

theorem derived66487 (p : Nat → Prop) (h : Inputs p) :
    (p 5589) ∨ (p 5593) :=
  ElevenRUP.step66487 (p 5588) (p 5589) (p 5593) (derived65344 p h) (h 9850)

theorem derived66488 (p : Nat → Prop) (h : Inputs p) :
    (p 5597) ∨ (p 5603) :=
  ElevenRUP.step66488 (p 5596) (p 5597) (p 5603) (derived65340 p h) (h 9876)

theorem derived66489 (p : Nat → Prop) (h : Inputs p) :
    (p 5609) ∨ (p 5615) :=
  ElevenRUP.step66489 (p 5608) (p 5609) (p 5615) (derived65336 p h) (h 9893)

theorem derived66490 (p : Nat → Prop) (h : Inputs p) :
    (p 5621) ∨ (p 5626) :=
  ElevenRUP.step66490 (p 5620) (p 5621) (p 5626) (derived65332 p h) (h 9969)

theorem derived66491 (p : Nat → Prop) (h : Inputs p) :
    (p 5632) ∨ (p 5637) :=
  ElevenRUP.step66491 (p 5631) (p 5632) (p 5637) (derived65328 p h) (h 9986)

theorem derived66492 (p : Nat → Prop) (h : Inputs p) :
    (p 5643) ∨ (p 5648) :=
  ElevenRUP.step66492 (p 5642) (p 5643) (p 5648) (derived65324 p h) (h 10013)

theorem derived66493 (p : Nat → Prop) (h : Inputs p) :
    (p 5659) ∨ (p 5663) :=
  ElevenRUP.step66493 (p 5658) (p 5659) (p 5663) (derived65320 p h) (h 10131)

theorem derived66494 (p : Nat → Prop) (h : Inputs p) :
    (p 5669) ∨ (p 5673) :=
  ElevenRUP.step66494 (p 5668) (p 5669) (p 5673) (derived65316 p h) (h 10167)

theorem derived66495 (p : Nat → Prop) (h : Inputs p) :
    (p 5678) ∨ (p 5684) :=
  ElevenRUP.step66495 (p 5677) (p 5678) (p 5684) (derived65312 p h) (h 10200)

theorem derived66496 (p : Nat → Prop) (h : Inputs p) :
    (p 5690) ∨ (p 5696) :=
  ElevenRUP.step66496 (p 5689) (p 5690) (p 5696) (derived65308 p h) (h 10236)

theorem derived66498 (p : Nat → Prop) (h : Inputs p) :
    (p 5714) ∨ (p 5720) :=
  ElevenRUP.step66498 (p 5713) (p 5714) (p 5720) (derived65300 p h) (h 10443)

theorem derived66499 (p : Nat → Prop) (h : Inputs p) :
    (p 5726) ∨ (p 5731) :=
  ElevenRUP.step66499 (p 5725) (p 5726) (p 5731) (derived65296 p h) (h 10539)

theorem derived66500 (p : Nat → Prop) (h : Inputs p) :
    (p 5737) ∨ (p 5743) :=
  ElevenRUP.step66500 (p 5736) (p 5737) (p 5743) (derived65292 p h) (h 10664)

theorem derived66504 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5789) ∨ (¬ p 5788) :=
  ElevenRUP.step66504 (p 5787) (p 5788) (p 5789) (derived65927 p h) (h 11745)

theorem derived66505 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5792) ∨ (¬ p 5791) :=
  ElevenRUP.step66505 (p 5790) (p 5791) (p 5792) (derived65738 p h) (h 11763)

theorem derived66506 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5794) ∨ (¬ p 5795) :=
  ElevenRUP.step66506 (p 5793) (p 5794) (p 5795) (derived65691 p h) (h 11780)

theorem derived66507 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5798) ∨ (¬ p 5797) :=
  ElevenRUP.step66507 (p 5796) (p 5797) (p 5798) (derived65749 p h) (h 11797)

theorem derived66508 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5801) ∨ (¬ p 5800) :=
  ElevenRUP.step66508 (p 5799) (p 5800) (p 5801) (derived65792 p h) (h 11814)

theorem derived66509 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5803) ∨ (¬ p 5804) :=
  ElevenRUP.step66509 (p 5802) (p 5803) (p 5804) (derived65805 p h) (h 11831)

theorem derived66510 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5807) ∨ (¬ p 5806) :=
  ElevenRUP.step66510 (p 5805) (p 5806) (p 5807) (derived65866 p h) (h 11849)

theorem derived66511 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5809) ∨ (¬ p 5810) :=
  ElevenRUP.step66511 (p 5808) (p 5809) (p 5810) (derived65706 p h) (h 11867)

theorem derived66512 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5812) ∨ (¬ p 5813) :=
  ElevenRUP.step66512 (p 5811) (p 5812) (p 5813) (derived65674 p h) (h 11884)

theorem derived66513 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5816) ∨ (¬ p 5815) :=
  ElevenRUP.step66513 (p 5814) (p 5815) (p 5816) (derived65939 p h) (h 11902)

theorem derived66514 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5818) ∨ (¬ p 5819) :=
  ElevenRUP.step66514 (p 5817) (p 5818) (p 5819) (derived65725 p h) (h 11919)

theorem derived66515 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5822) ∨ (¬ p 5821) :=
  ElevenRUP.step66515 (p 5820) (p 5821) (p 5822) (derived65734 p h) (h 11936)

theorem derived66516 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5825) ∨ (¬ p 5824) :=
  ElevenRUP.step66516 (p 5823) (p 5824) (p 5825) (derived65888 p h) (h 11954)

theorem derived66517 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5827) ∨ (¬ p 5828) :=
  ElevenRUP.step66517 (p 5826) (p 5827) (p 5828) (derived65824 p h) (h 11971)

theorem derived66518 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5831) ∨ (¬ p 5830) :=
  ElevenRUP.step66518 (p 5829) (p 5830) (p 5831) (derived65768 p h) (h 11988)

theorem derived66519 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5834) ∨ (¬ p 5833) :=
  ElevenRUP.step66519 (p 5832) (p 5833) (p 5834) (derived65896 p h) (h 12005)

theorem derived66520 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5837) ∨ (¬ p 5836) :=
  ElevenRUP.step66520 (p 5835) (p 5836) (p 5837) (derived65759 p h) (h 12024)

theorem derived66521 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5840) ∨ (¬ p 5839) :=
  ElevenRUP.step66521 (p 5838) (p 5839) (p 5840) (derived65772 p h) (h 12043)

theorem derived66522 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5843) ∨ (¬ p 5842) :=
  ElevenRUP.step66522 (p 5841) (p 5842) (p 5843) (derived65764 p h) (h 12060)

theorem derived66523 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5845) ∨ (¬ p 5846) :=
  ElevenRUP.step66523 (p 5844) (p 5845) (p 5846) (derived65721 p h) (h 12078)

theorem derived66524 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5848) ∨ (¬ p 5849) :=
  ElevenRUP.step66524 (p 5847) (p 5848) (p 5849) (derived65801 p h) (h 12096)

theorem derived66525 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5851) ∨ (¬ p 5852) :=
  ElevenRUP.step66525 (p 5850) (p 5851) (p 5852) (derived65849 p h) (h 12114)

theorem derived66526 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5854) ∨ (¬ p 5855) :=
  ElevenRUP.step66526 (p 5853) (p 5854) (p 5855) (derived65785 p h) (h 12131)

theorem derived66527 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5858) ∨ (¬ p 5857) :=
  ElevenRUP.step66527 (p 5856) (p 5857) (p 5858) (derived65882 p h) (h 12148)

theorem derived66528 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5860) ∨ (¬ p 5861) :=
  ElevenRUP.step66528 (p 5859) (p 5860) (p 5861) (derived65945 p h) (h 12165)

theorem derived66529 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5863) ∨ (¬ p 5864) :=
  ElevenRUP.step66529 (p 5862) (p 5863) (p 5864) (derived65695 p h) (h 12182)

theorem derived66530 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5866) ∨ (¬ p 5867) :=
  ElevenRUP.step66530 (p 5865) (p 5866) (p 5867) (derived65999 p h) (h 12201)

theorem derived66531 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5869) ∨ (¬ p 5870) :=
  ElevenRUP.step66531 (p 5868) (p 5869) (p 5870) (derived65776 p h) (h 12219)

theorem derived66532 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5873) ∨ (¬ p 5872) :=
  ElevenRUP.step66532 (p 5871) (p 5872) (p 5873) (derived65845 p h) (h 12236)

theorem derived66533 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5876) ∨ (¬ p 5875) :=
  ElevenRUP.step66533 (p 5874) (p 5875) (p 5876) (derived65854 p h) (h 12254)

theorem derived66534 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5878) ∨ (¬ p 5879) :=
  ElevenRUP.step66534 (p 5877) (p 5878) (p 5879) (derived65781 p h) (h 12271)

theorem derived66535 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5882) ∨ (¬ p 5881) :=
  ElevenRUP.step66535 (p 5880) (p 5881) (p 5882) (derived65592 p h) (h 12288)

theorem derived66536 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5884) ∨ (¬ p 5885) :=
  ElevenRUP.step66536 (p 5883) (p 5884) (p 5885) (derived65533 p h) (h 12305)

theorem derived66537 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5887) ∨ (¬ p 5888) :=
  ElevenRUP.step66537 (p 5886) (p 5887) (p 5888) (derived65618 p h) (h 12322)

theorem derived66538 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5891) ∨ (¬ p 5890) :=
  ElevenRUP.step66538 (p 5889) (p 5890) (p 5891) (derived65607 p h) (h 12339)

theorem derived66539 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5894) ∨ (¬ p 5893) :=
  ElevenRUP.step66539 (p 5892) (p 5893) (p 5894) (derived65666 p h) (h 12357)

theorem derived66540 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5897) ∨ (¬ p 5896) :=
  ElevenRUP.step66540 (p 5895) (p 5896) (p 5897) (derived65860 p h) (h 12374)

theorem derived66541 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5899) ∨ (¬ p 5900) :=
  ElevenRUP.step66541 (p 5898) (p 5899) (p 5900) (derived65710 p h) (h 12391)

theorem derived66542 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5902) ∨ (¬ p 5903) :=
  ElevenRUP.step66542 (p 5901) (p 5902) (p 5903) (derived65603 p h) (h 12408)

theorem derived66543 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5905) ∨ (¬ p 5906) :=
  ElevenRUP.step66543 (p 5904) (p 5905) (p 5906) (derived65623 p h) (h 12426)

theorem derived66544 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5909) ∨ (¬ p 5908) :=
  ElevenRUP.step66544 (p 5907) (p 5908) (p 5909) (derived65627 p h) (h 12444)

theorem derived66545 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5911) ∨ (¬ p 5912) :=
  ElevenRUP.step66545 (p 5910) (p 5911) (p 5912) (derived65832 p h) (h 12461)

theorem derived66546 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5915) ∨ (¬ p 5914) :=
  ElevenRUP.step66546 (p 5913) (p 5914) (p 5915) (derived65588 p h) (h 12479)

theorem derived66547 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5918) ∨ (¬ p 5917) :=
  ElevenRUP.step66547 (p 5916) (p 5917) (p 5918) (derived65828 p h) (h 12499)

theorem derived66548 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5923) ∨ (¬ p 5924) :=
  ElevenRUP.step66548 (p 5922) (p 5923) (p 5924) (derived65811 p h) (h 12538)

theorem derived66549 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5926) ∨ (¬ p 5927) :=
  ElevenRUP.step66549 (p 5925) (p 5926) (p 5927) (derived65717 p h) (h 12556)

theorem derived66550 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5929) ∨ (¬ p 5930) :=
  ElevenRUP.step66550 (p 5928) (p 5929) (p 5930) (derived65700 p h) (h 12573)

theorem derived66551 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5932) ∨ (¬ p 5933) :=
  ElevenRUP.step66551 (p 5931) (p 5932) (p 5933) (derived65796 p h) (h 12590)

theorem derived66552 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5935) ∨ (¬ p 5936) :=
  ElevenRUP.step66552 (p 5934) (p 5935) (p 5936) (derived65742 p h) (h 12607)

theorem derived66553 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5939) ∨ (¬ p 5938) :=
  ElevenRUP.step66553 (p 5937) (p 5938) (p 5939) (derived65631 p h) (h 12625)

theorem derived66554 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5942) ∨ (¬ p 5941) :=
  ElevenRUP.step66554 (p 5940) (p 5941) (p 5942) (derived65650 p h) (h 12644)

theorem derived66555 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5945) ∨ (¬ p 5944) :=
  ElevenRUP.step66555 (p 5943) (p 5944) (p 5945) (derived65682 p h) (h 12661)

theorem derived66556 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5947) ∨ (¬ p 5948) :=
  ElevenRUP.step66556 (p 5946) (p 5947) (p 5948) (derived65730 p h) (h 12678)

theorem derived66557 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5951) ∨ (¬ p 5950) :=
  ElevenRUP.step66557 (p 5949) (p 5950) (p 5951) (derived65981 p h) (h 12695)

theorem derived66558 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5953) ∨ (¬ p 5954) :=
  ElevenRUP.step66558 (p 5952) (p 5953) (p 5954) (derived65678 p h) (h 12715)

theorem derived66559 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5956) ∨ (¬ p 5957) :=
  ElevenRUP.step66559 (p 5955) (p 5956) (p 5957) (derived65670 p h) (h 12733)

theorem derived66560 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5959) ∨ (¬ p 5960) :=
  ElevenRUP.step66560 (p 5958) (p 5959) (p 5960) (derived65662 p h) (h 12751)

theorem derived66561 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5963) ∨ (¬ p 5962) :=
  ElevenRUP.step66561 (p 5961) (p 5962) (p 5963) (derived65658 p h) (h 12773)

theorem derived66562 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5966) ∨ (¬ p 5965) :=
  ElevenRUP.step66562 (p 5964) (p 5965) (p 5966) (derived65654 p h) (h 12793)

theorem derived66563 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5968) ∨ (¬ p 5969) :=
  ElevenRUP.step66563 (p 5967) (p 5968) (p 5969) (derived65643 p h) (h 12814)

theorem derived66564 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5971) ∨ (¬ p 5972) :=
  ElevenRUP.step66564 (p 5970) (p 5971) (p 5972) (derived65639 p h) (h 12831)

theorem derived66565 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5975) ∨ (¬ p 5974) :=
  ElevenRUP.step66565 (p 5973) (p 5974) (p 5975) (derived65598 p h) (h 12848)

theorem derived66566 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5977) ∨ (¬ p 5978) :=
  ElevenRUP.step66566 (p 5976) (p 5977) (p 5978) (derived65635 p h) (h 12866)

theorem derived66567 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5981) ∨ (¬ p 5980) :=
  ElevenRUP.step66567 (p 5979) (p 5980) (p 5981) (derived65584 p h) (h 12883)

theorem derived66568 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5983) ∨ (¬ p 5984) :=
  ElevenRUP.step66568 (p 5982) (p 5983) (p 5984) (derived65580 p h) (h 12901)

theorem derived66569 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5986) ∨ (¬ p 5987) :=
  ElevenRUP.step66569 (p 5985) (p 5986) (p 5987) (derived65576 p h) (h 12919)

theorem derived66570 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5989) ∨ (¬ p 5990) :=
  ElevenRUP.step66570 (p 5988) (p 5989) (p 5990) (derived65572 p h) (h 12936)

theorem derived66571 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5992) ∨ (¬ p 5993) :=
  ElevenRUP.step66571 (p 5991) (p 5992) (p 5993) (derived65568 p h) (h 12954)

theorem derived66572 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5995) ∨ (¬ p 5996) :=
  ElevenRUP.step66572 (p 5994) (p 5995) (p 5996) (derived65564 p h) (h 12971)

theorem derived66573 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5998) ∨ (¬ p 5999) :=
  ElevenRUP.step66573 (p 5997) (p 5998) (p 5999) (derived65560 p h) (h 12988)

theorem derived66574 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6001) ∨ (¬ p 6002) :=
  ElevenRUP.step66574 (p 6000) (p 6001) (p 6002) (derived65553 p h) (h 13008)

theorem derived66575 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6004) ∨ (¬ p 6005) :=
  ElevenRUP.step66575 (p 6003) (p 6004) (p 6005) (derived65549 p h) (h 13028)

theorem derived66577 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6010) ∨ (¬ p 6011) :=
  ElevenRUP.step66577 (p 6009) (p 6010) (p 6011) (derived65541 p h) (h 13067)

theorem derived66578 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6013) ∨ (¬ p 6014) :=
  ElevenRUP.step66578 (p 6012) (p 6013) (p 6014) (derived65537 p h) (h 13087)

theorem derived66579 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6016) ∨ (¬ p 6017) :=
  ElevenRUP.step66579 (p 6015) (p 6016) (p 6017) (derived65529 p h) (h 13105)

theorem derived66580 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6019) ∨ (¬ p 6020) :=
  ElevenRUP.step66580 (p 6018) (p 6019) (p 6020) (derived65525 p h) (h 13122)

theorem derived66581 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6022) ∨ (¬ p 6023) :=
  ElevenRUP.step66581 (p 6021) (p 6022) (p 6023) (derived65521 p h) (h 13141)

theorem derived66582 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6025) ∨ (¬ p 6026) :=
  ElevenRUP.step66582 (p 6024) (p 6025) (p 6026) (derived65517 p h) (h 13158)

theorem derived66583 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6028) ∨ (¬ p 6029) :=
  ElevenRUP.step66583 (p 6027) (p 6028) (p 6029) (derived65513 p h) (h 13176)

theorem derived66584 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6031) ∨ (¬ p 6032) :=
  ElevenRUP.step66584 (p 6030) (p 6031) (p 6032) (derived65509 p h) (h 13193)

theorem derived66585 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6034) ∨ (¬ p 6035) :=
  ElevenRUP.step66585 (p 6033) (p 6034) (p 6035) (derived65505 p h) (h 13210)

theorem derived66586 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6037) ∨ (¬ p 6038) :=
  ElevenRUP.step66586 (p 6036) (p 6037) (p 6038) (derived65501 p h) (h 13232)

theorem derived66587 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6040) ∨ (¬ p 6041) :=
  ElevenRUP.step66587 (p 6039) (p 6040) (p 6041) (derived65497 p h) (h 13250)

theorem derived66588 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6043) ∨ (¬ p 6044) :=
  ElevenRUP.step66588 (p 6042) (p 6043) (p 6044) (derived65493 p h) (h 13267)

theorem derived66589 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6047) ∨ (¬ p 6046) :=
  ElevenRUP.step66589 (p 6045) (p 6046) (p 6047) (derived65489 p h) (h 13286)

theorem derived66590 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6049) ∨ (¬ p 6050) :=
  ElevenRUP.step66590 (p 6048) (p 6049) (p 6050) (derived65485 p h) (h 13304)

theorem derived66591 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6052) ∨ (¬ p 6053) :=
  ElevenRUP.step66591 (p 6051) (p 6052) (p 6053) (derived65481 p h) (h 13324)

theorem derived66592 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6055) ∨ (¬ p 6056) :=
  ElevenRUP.step66592 (p 6054) (p 6055) (p 6056) (derived65477 p h) (h 13346)

theorem derived66593 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6058) ∨ (¬ p 6059) :=
  ElevenRUP.step66593 (p 6057) (p 6058) (p 6059) (derived65473 p h) (h 13367)

theorem derived66594 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6061) ∨ (¬ p 6062) :=
  ElevenRUP.step66594 (p 6060) (p 6061) (p 6062) (derived65469 p h) (h 13387)

theorem derived66595 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6064) ∨ (¬ p 6065) :=
  ElevenRUP.step66595 (p 6063) (p 6064) (p 6065) (derived65465 p h) (h 13407)

theorem derived66596 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6067) ∨ (¬ p 6068) :=
  ElevenRUP.step66596 (p 6066) (p 6067) (p 6068) (derived65461 p h) (h 13437)

theorem derived66597 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6070) ∨ (¬ p 6071) :=
  ElevenRUP.step66597 (p 6069) (p 6070) (p 6071) (derived65457 p h) (h 13462)

theorem derived66598 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6073) ∨ (¬ p 6074) :=
  ElevenRUP.step66598 (p 6072) (p 6073) (p 6074) (derived65453 p h) (h 13480)

theorem derived66599 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6076) ∨ (¬ p 6077) :=
  ElevenRUP.step66599 (p 6075) (p 6076) (p 6077) (derived65449 p h) (h 13498)

theorem derived66600 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6079) ∨ (¬ p 6080) :=
  ElevenRUP.step66600 (p 6078) (p 6079) (p 6080) (derived65445 p h) (h 13517)

theorem derived66601 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6082) ∨ (¬ p 6083) :=
  ElevenRUP.step66601 (p 6081) (p 6082) (p 6083) (derived65441 p h) (h 13557)

theorem derived66602 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6085) ∨ (¬ p 6086) :=
  ElevenRUP.step66602 (p 6084) (p 6085) (p 6086) (derived65437 p h) (h 13629)

theorem derived66603 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6088) ∨ (¬ p 6089) :=
  ElevenRUP.step66603 (p 6087) (p 6088) (p 6089) (derived65433 p h) (h 13646)

theorem derived66605 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6094) ∨ (¬ p 6095) :=
  ElevenRUP.step66605 (p 6093) (p 6094) (p 6095) (derived65425 p h) (h 13681)

theorem derived66606 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6097) ∨ (¬ p 6098) :=
  ElevenRUP.step66606 (p 6096) (p 6097) (p 6098) (derived65421 p h) (h 13711)

theorem derived66607 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6100) ∨ (¬ p 6101) :=
  ElevenRUP.step66607 (p 6099) (p 6100) (p 6101) (derived65417 p h) (h 13742)

theorem derived66608 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6103) ∨ (¬ p 6104) :=
  ElevenRUP.step66608 (p 6102) (p 6103) (p 6104) (derived65413 p h) (h 13778)

theorem derived66609 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6106) ∨ (¬ p 6107) :=
  ElevenRUP.step66609 (p 6105) (p 6106) (p 6107) (derived65409 p h) (h 13796)

theorem derived66610 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6109) ∨ (¬ p 6110) :=
  ElevenRUP.step66610 (p 6108) (p 6109) (p 6110) (derived65405 p h) (h 13840)

theorem derived66611 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6112) ∨ (¬ p 6113) :=
  ElevenRUP.step66611 (p 6111) (p 6112) (p 6113) (derived65401 p h) (h 13861)

theorem derived66613 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6118) ∨ (¬ p 6119) :=
  ElevenRUP.step66613 (p 6117) (p 6118) (p 6119) (derived65393 p h) (h 13895)

theorem derived66614 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6121) ∨ (¬ p 6122) :=
  ElevenRUP.step66614 (p 6120) (p 6121) (p 6122) (derived65389 p h) (h 13927)

theorem derived66615 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6124) ∨ (¬ p 6125) :=
  ElevenRUP.step66615 (p 6123) (p 6124) (p 6125) (derived65385 p h) (h 13970)

theorem derived66616 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6127) ∨ (¬ p 6128) :=
  ElevenRUP.step66616 (p 6126) (p 6127) (p 6128) (derived65381 p h) (h 14019)

theorem derived66617 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6130) ∨ (¬ p 6131) :=
  ElevenRUP.step66617 (p 6129) (p 6130) (p 6131) (derived65377 p h) (h 14046)

theorem derived66619 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6136) ∨ (¬ p 6137) :=
  ElevenRUP.step66619 (p 6135) (p 6136) (p 6137) (derived65369 p h) (h 14144)

theorem derived66620 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6139) ∨ (¬ p 6140) :=
  ElevenRUP.step66620 (p 6138) (p 6139) (p 6140) (derived65365 p h) (h 14179)

theorem derived66622 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6145) ∨ (¬ p 6146) :=
  ElevenRUP.step66622 (p 6144) (p 6145) (p 6146) (derived65357 p h) (h 14278)

theorem derived66623 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6148) ∨ (¬ p 6149) :=
  ElevenRUP.step66623 (p 6147) (p 6148) (p 6149) (derived65353 p h) (h 14404)

theorem derived66624 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6151) ∨ (¬ p 6152) :=
  ElevenRUP.step66624 (p 6150) (p 6151) (p 6152) (derived65349 p h) (h 14422)

theorem derived66625 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6154) ∨ (¬ p 6155) :=
  ElevenRUP.step66625 (p 6153) (p 6154) (p 6155) (derived65345 p h) (h 14486)

theorem derived66628 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6163) ∨ (¬ p 6164) :=
  ElevenRUP.step66628 (p 6162) (p 6163) (p 6164) (derived65333 p h) (h 14712)

theorem derived66629 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6166) ∨ (¬ p 6167) :=
  ElevenRUP.step66629 (p 6165) (p 6166) (p 6167) (derived65329 p h) (h 14731)

theorem derived66630 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6169) ∨ (¬ p 6170) :=
  ElevenRUP.step66630 (p 6168) (p 6169) (p 6170) (derived65325 p h) (h 14763)

theorem derived66631 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6172) ∨ (¬ p 6173) :=
  ElevenRUP.step66631 (p 6171) (p 6172) (p 6173) (derived65321 p h) (h 15014)

theorem derived66632 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6175) ∨ (¬ p 6176) :=
  ElevenRUP.step66632 (p 6174) (p 6175) (p 6176) (derived65317 p h) (h 15094)

theorem derived66633 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6178) ∨ (¬ p 6179) :=
  ElevenRUP.step66633 (p 6177) (p 6178) (p 6179) (derived65313 p h) (h 15165)

theorem derived66634 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6181) ∨ (¬ p 6182) :=
  ElevenRUP.step66634 (p 6180) (p 6181) (p 6182) (derived65309 p h) (h 15274)

theorem derived66636 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6187) ∨ (¬ p 6188) :=
  ElevenRUP.step66636 (p 6186) (p 6187) (p 6188) (derived65301 p h) (h 15779)

theorem derived66637 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6190) ∨ (¬ p 6191) :=
  ElevenRUP.step66637 (p 6189) (p 6190) (p 6191) (derived65297 p h) (h 16044)

theorem derived66638 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 6193) ∨ (¬ p 6194) :=
  ElevenRUP.step66638 (p 6192) (p 6193) (p 6194) (derived65293 p h) (h 16419)

theorem derived66644 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4554) ∨ (¬ p 3556) ∨ (¬ p 4533) ∨ (¬ p 4718) ∨ (¬ p 3660) ∨ (¬ p 2553) :=
  ElevenRUP.step66644 (p 2156) (p 2553) (p 3097) (p 3556) (p 3646) (p 3660) (p 4275) (p 4484) (p 4487) (p 4533) (p 4554) (p 4718) (h 7201) (h 7202) (derived57162 p h) (derived53114 p h) (h 7028) (h 7022) (derived66328 p h)

theorem derived66646 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3692) ∨ (¬ p 2528) ∨ (¬ p 2459) ∨ (¬ p 2191) ∨ (¬ p 4629) ∨ (¬ p 2589) :=
  ElevenRUP.step66646 (p 2191) (p 2459) (p 2528) (p 2589) (p 3692) (p 3880) (p 4355) (p 4606) (p 4609) (p 4629) (derived44763 p h) (derived54486 p h) (h 7343) (h 7348) (derived66350 p h)

theorem derived66647 (p : Nat → Prop) (h : Inputs p) :
    (p 3256) ∨ (¬ p 2373) ∨ (¬ p 3146) ∨ (¬ p 4702) :=
  ElevenRUP.step66647 (p 2373) (p 3146) (p 3256) (p 3661) (p 4118) (p 4311) (p 4702) (p 5061) (p 5064) (p 5106) (p 5110) (h 8634) (h 34559) (derived66437 p h) (h 8494) (h 8628) (derived66429 p h) (derived41848 p h) (h 8488)

theorem derived66648 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4812) ∨ (¬ p 2810) ∨ (¬ p 2751) ∨ (¬ p 2657) ∨ (¬ p 3379) :=
  ElevenRUP.step66648 (p 2244) (p 2247) (p 2251) (p 2252) (p 2657) (p 2751) (p 2810) (p 3379) (p 3487) (p 4281) (p 4812) (h 7861) (h 7862) (derived49266 p h) (h 15387) (h 2625) (h 2637) (derived66336 p h)

theorem derived66649 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2747) ∨ (¬ p 4256) ∨ (¬ p 3644) ∨ (¬ p 4732) ∨ (¬ p 2657) ∨ (¬ p 4523) ∨ (¬ p 3556) ∨ (¬ p 4557) ∨ (¬ p 2563) :=
  ElevenRUP.step66649 (p 2156) (p 2177) (p 2192) (p 2210) (p 2274) (p 2284) (p 2307) (p 2310) (p 2313) (p 2317) (p 2427) (p 2542) (p 2563) (p 2630) (p 2651) (p 2654) (p 2657) (p 2659) (p 2661) (p 2737) (p 2747) (p 2751) (p 2810) (p 2839) (p 3054) (p 3093) (p 3309) (p 3361) (p 3365) (p 3379) (p 3549) (p 3556) (p 3583) (p 3585) (p 3591) (p 3644) (p 3645) (p 3646) (p 3695) (p 3872) (p 3873) (p 3904) (p 3954) (p 3957) (p 4031) (p 4198) (p 4202) (p 4210) (p 4243) (p 4244) (p 4256) (p 4484) (p 4487) (p 4500) (p 4501) (p 4502) (p 4511) (p 4512) (p 4515) (p 4523) (p 4533) (p 4535) (p 4537) (p 4557) (p 4627) (p 4629) (p 4630) (p 4699) (p 4703) (p 4732) (p 4748) (p 4751) (p 4785) (p 4788) (p 4809) (p 4812) (p 4873) (p 4874) (p 4876) (p 4880) (p 4882) (p 4883) (p 5014) (p 5019) (p 5140) (p 5143) (p 5213) (p 5215) (p 5216) (h 7113) (h 7681) (h 29892) (h 8015) (derived66397 p h) (h 8023) (h 9144) (h 7207) (h 7111) (h 8021) (h 26822) (h 20311) (h 8038) (derived66398 p h) (h 8032) (h 37227) (h 8853) (derived66448 p h) (h 8860) (h 8036) (h 5739) (h 22664) (h 7399) (derived66353 p h) (h 7397) (h 7208) (h 6734) (h 5323) (h 7096) (derived66332 p h) (h 7088) (derived61082 p h) (h 8705) (derived66440 p h) (h 8711) (h 7089) (derived41941 p h) (h 8386) (derived66423 p h) (h 8392) (derived52571 p h) (h 7062) (derived66330 p h) (h 7057) (h 7679) (h 20298) (h 7146) (derived66335 p h) (h 7140) (h 8330) (h 3449) (derived66378 p h) (h 3437) (derived41572 p h) (h 7590) (derived66367 p h) (h 7393) (h 6790) (h 7144) (h 20348) (h 7028) (derived66328 p h) (h 7020) (derived60888 p h) (h 2756) (derived66343 p h) (h 2770) (h 3622) (h 3624) (derived49742 p h) (h 7805) (derived66383 p h) (h 7809) (h 4833) (h 7721) (derived66376 p h) (h 7715) (derived66648 p h) (derived66386 p h) (derived66005 p h) (derived65988 p h)

theorem derived66650 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4732) ∨ (¬ p 2657) ∨ (¬ p 4523) ∨ (¬ p 3556) ∨ (¬ p 4557) ∨ (¬ p 3741) ∨ (¬ p 2563) :=
  ElevenRUP.step66650 (p 2177) (p 2192) (p 2210) (p 2274) (p 2299) (p 2427) (p 2437) (p 2440) (p 2542) (p 2563) (p 2651) (p 2654) (p 2657) (p 2659) (p 2661) (p 2740) (p 2743) (p 2747) (p 2839) (p 2881) (p 2891) (p 2911) (p 3093) (p 3309) (p 3486) (p 3527) (p 3548) (p 3549) (p 3554) (p 3556) (p 3569) (p 3570) (p 3591) (p 3644) (p 3645) (p 3646) (p 3741) (p 3742) (p 3872) (p 3904) (p 3954) (p 3957) (p 4031) (p 4173) (p 4186) (p 4210) (p 4235) (p 4243) (p 4256) (p 4392) (p 4452) (p 4500) (p 4502) (p 4511) (p 4512) (p 4515) (p 4523) (p 4533) (p 4535) (p 4537) (p 4557) (p 4627) (p 4629) (p 4630) (p 4643) (p 4645) (p 4649) (p 4651) (p 4699) (p 4703) (p 4732) (p 4873) (p 4874) (p 4876) (p 4900) (p 4903) (p 4908) (p 4912) (p 4921) (p 4923) (p 5014) (p 5019) (p 5048) (p 5050) (p 5052) (p 5140) (p 5143) (p 5304) (p 5306) (h 7207) (h 20312) (h 7429) (derived66355 p h) (h 7433) (h 5739) (h 7111) (h 22664) (h 7399) (derived66353 p h) (h 7397) (h 20298) (h 7146) (derived66335 p h) (h 7144) (h 6734) (h 5323) (h 7096) (derived66332 p h) (h 7090) (derived41459 p h) (h 8110) (derived66402 p h) (h 8104) (h 7140) (h 8330) (h 3449) (derived66378 p h) (h 3437) (derived41572 p h) (h 7590) (derived66367 p h) (h 7584) (derived63238 p h) (h 7453) (derived66356 p h) (h 7447) (h 8102) (h 7113) (h 7089) (derived41941 p h) (h 8386) (derived66423 p h) (h 8392) (h 7208) (h 7088) (derived61082 p h) (h 8705) (derived66440 p h) (h 8711) (h 8710) (h 7681) (h 29892) (derived52571 p h) (h 8015) (h 7062) (derived66397 p h) (derived66330 p h) (h 8021) (h 8023) (h 7056) (derived60034 p h) (h 9044) (derived66458 p h) (h 9038) (derived40975 p h) (h 8092) (derived66401 p h) (h 8086) (derived41489 p h) (h 8144) (derived66404 p h) (h 8136) (h 8138) (h 6402) (derived66649 p h) (derived66387 p h) (h 3608) (h 18646) (derived50872 p h) (h 8454) (h 8463) (derived66427 p h)

theorem derived66651 (p : Nat → Prop) (h : Inputs p) :
    (p 2081) :=
  ElevenRUP.step66651 (p 1) (p 7) (p 2081) (h 2296) (h 2297) (h 13)

theorem derived66652 (p : Nat → Prop) (h : Inputs p) :
    (p 2082) :=
  ElevenRUP.step66652 (p 2081) (p 2082) (derived66651 p h) (h 2314)

theorem derived66653 (p : Nat → Prop) (h : Inputs p) :
    (p 4453) :=
  ElevenRUP.step66653 (p 2082) (p 4453) (derived66652 p h) (h 6959)

theorem derived66654 (p : Nat → Prop) (h : Inputs p) :
    (p 5784) :=
  ElevenRUP.step66654 (p 4453) (p 5784) (derived66653 p h) (h 11728)

theorem derived66658 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3574) ∨ (¬ p 2588) ∨ (¬ p 2299) ∨ (¬ p 2657) :=
  ElevenRUP.step66658 (p 2299) (p 2588) (p 2630) (p 2657) (p 2810) (p 3361) (p 3367) (p 3422) (p 3475) (p 3574) (p 3584) (p 3585) (p 4236) (p 4748) (p 4751) (p 4785) (p 4787) (p 4788) (p 5213) (p 5215) (p 5219) (p 5223) (derived43874 p h) (h 7715) (derived66376 p h) (h 7720) (h 7721) (h 4833) (h 7809) (derived66383 p h) (h 7803) (h 7807) (derived65870 p h) (derived51047 p h) (h 8859) (h 8879) (derived66448 p h) (derived66449 p h) (h 8853) (h 8873) (derived43890 p h)

theorem derived66659 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4606) ∨ (¬ p 2493) ∨ (¬ p 4507) ∨ (¬ p 2509) ∨ (¬ p 4716) :=
  ElevenRUP.step66659 (p 2406) (p 2493) (p 2509) (p 2563) (p 3238) (p 3693) (p 3880) (p 4203) (p 4507) (p 4606) (p 4627) (p 4630) (p 4716) (h 7624) (h 7622) (h 7342) (h 7343) (derived53958 p h) (derived63184 p h) (h 7401) (h 7395) (derived66353 p h)

theorem derived66660 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4609) ∨ (¬ p 3742) ∨ (¬ p 3016) ∨ (¬ p 3497) ∨ (¬ p 4186) ∨ (¬ p 4717) :=
  ElevenRUP.step66660 (p 2373) (p 2542) (p 3016) (p 3497) (p 3742) (p 4186) (p 4355) (p 4609) (p 4699) (p 4700) (p 4703) (p 4717) (h 7348) (h 7349) (h 20162) (derived41712 p h) (h 7590) (h 7582) (derived66367 p h)

theorem derived66663 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3585) ∨ (p 3583) ∨ (¬ p 4749) ∨ (¬ p 2737) ∨ (¬ p 3238) :=
  ElevenRUP.step66663 (p 2737) (p 2850) (p 3054) (p 3238) (p 3367) (p 3583) (p 3585) (p 4257) (p 4749) (p 4880) (p 4883) (p 5213) (p 5215) (h 8999) (h 37227) (h 8859) (h 8032) (derived66448 p h) (derived66398 p h) (h 8851) (h 8040) (derived41294 p h)

theorem derived66669 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2496) ∨ (¬ p 2406) ∨ (¬ p 4261) ∨ (¬ p 4371) ∨ (¬ p 3573) ∨ (¬ p 2363) ∨ (¬ p 4608) :=
  ElevenRUP.step66669 (p 2363) (p 2406) (p 2496) (p 2497) (p 2499) (p 2509) (p 2528) (p 2534) (p 3453) (p 3573) (p 4261) (p 4371) (p 4608) (p 4692) (p 4694) (h 3125) (h 3127) (h 37493) (h 22593) (derived49121 p h) (derived57873 p h) (h 7573) (h 7567) (derived66366 p h)

theorem derived66674 (p : Nat → Prop) (h : Inputs p) :
    (p 3570) ∨ (¬ p 3989) ∨ (¬ p 4500) :=
  ElevenRUP.step66674 (p 2299) (p 3570) (p 3872) (p 3989) (p 4138) (p 4275) (p 4500) (p 4554) (p 4557) (h 7056) (h 7055) (h 27210) (h 6943) (h 7207) (h 7201) (derived66340 p h)

theorem derived66677 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5019) ∨ (p 2383) ∨ (¬ p 3860) ∨ (¬ p 4514) ∨ (¬ p 2187) :=
  ElevenRUP.step66677 (p 2187) (p 2383) (p 3063) (p 3093) (p 3204) (p 3860) (p 4514) (p 4992) (p 4993) (p 4996) (p 5019) (h 8390) (h 8392) (h 6329) (derived54781 p h) (h 8340) (h 8333) (derived66420 p h)

theorem derived66678 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2387) ∨ (¬ p 2352) ∨ (¬ p 3379) ∨ (¬ p 3860) ∨ (¬ p 2241) ∨ (¬ p 4514) ∨ (¬ p 4756) ∨ (¬ p 2187) :=
  ElevenRUP.step66678 (p 2187) (p 2241) (p 2352) (p 2383) (p 2387) (p 3063) (p 3379) (p 3591) (p 3860) (p 3923) (p 4514) (p 4756) (p 4992) (p 4996) (p 5014) (p 5015) (p 5019) (h 9785) (derived66677 p h) (derived66423 p h) (h 8384) (h 8386) (derived55404 p h) (derived43981 p h) (h 8340) (h 8334) (derived66420 p h)

theorem derived66679 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4996) ∨ (¬ p 3917) ∨ (¬ p 3654) ∨ (¬ p 4444) ∨ (¬ p 3399) ∨ (¬ p 3680) ∨ (¬ p 2589) ∨ (¬ p 3227) ∨ (¬ p 3379) ∨ (¬ p 3860) ∨ (¬ p 4697) ∨ (¬ p 2786) ∨ (¬ p 4789) ∨ (¬ p 4811) ∨ (¬ p 4871) ∨ (¬ p 3990) ∨ (¬ p 3955) ∨ (¬ p 2655) ∨ (¬ p 2542) :=
  ElevenRUP.step66679 (p 2122) (p 2542) (p 2589) (p 2655) (p 2786) (p 3063) (p 3227) (p 3343) (p 3359) (p 3379) (p 3399) (p 3461) (p 3547) (p 3549) (p 3591) (p 3654) (p 3680) (p 3822) (p 3830) (p 3834) (p 3860) (p 3917) (p 3955) (p 3990) (p 4026) (p 4191) (p 4317) (p 4444) (p 4470) (p 4474) (p 4697) (p 4789) (p 4811) (p 4871) (p 4996) (p 5140) (p 5143) (p 5147) (p 5151) (p 5152) (p 5169) (p 5174) (p 5246) (p 5251) (p 5485) (p 5490) (h 8339) (h 8340) (h 29238) (h 19944) (h 19762) (h 8705) (h 8723) (derived66440 p h) (derived66441 p h) (h 8709) (h 8727) (derived62951 p h) (derived42269 p h) (h 6984) (h 9539) (derived66324 p h) (derived66478 p h) (h 6990) (h 9533) (derived46854 p h) (derived42260 p h) (h 8928) (h 8765) (derived66452 p h) (derived66443 p h) (h 8934) (h 8759) (derived49052 p h)

theorem derived66680 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5192) ∨ (¬ p 2098) ∨ (¬ p 3237) ∨ (¬ p 4358) ∨ (¬ p 3860) ∨ (¬ p 4697) ∨ (¬ p 3690) ∨ (¬ p 4402) ∨ (¬ p 4621) ∨ (¬ p 4729) ∨ (¬ p 3609) ∨ (¬ p 5216) ∨ (¬ p 2786) ∨ (¬ p 2241) ∨ (¬ p 2252) ∨ (¬ p 4514) ∨ (¬ p 4811) ∨ (¬ p 4756) ∨ (¬ p 3570) ∨ (¬ p 4871) ∨ (¬ p 3990) ∨ (¬ p 3955) ∨ (¬ p 4732) ∨ (¬ p 2187) ∨ (¬ p 2542) ∨ (¬ p 2952) ∨ (¬ p 4320) ∨ (¬ p 4608) :=
  ElevenRUP.step66680 (p 2098) (p 2187) (p 2230) (p 2241) (p 2252) (p 2352) (p 2383) (p 2387) (p 2406) (p 2427) (p 2437) (p 2440) (p 2441) (p 2542) (p 2589) (p 2651) (p 2654) (p 2655) (p 2661) (p 2740) (p 2741) (p 2747) (p 2748) (p 2750) (p 2753) (p 2761) (p 2786) (p 2911) (p 2922) (p 2925) (p 2927) (p 2932) (p 2952) (p 3083) (p 3093) (p 3222) (p 3225) (p 3227) (p 3231) (p 3237) (p 3238) (p 3266) (p 3365) (p 3379) (p 3399) (p 3413) (p 3483) (p 3570) (p 3609) (p 3644) (p 3654) (p 3680) (p 3690) (p 3742) (p 3860) (p 3868) (p 3873) (p 3917) (p 3923) (p 3954) (p 3955) (p 3990) (p 4001) (p 4079) (p 4129) (p 4235) (p 4241) (p 4256) (p 4320) (p 4322) (p 4358) (p 4366) (p 4370) (p 4381) (p 4383) (p 4402) (p 4432) (p 4444) (p 4514) (p 4535) (p 4537) (p 4594) (p 4597) (p 4608) (p 4612) (p 4615) (p 4621) (p 4627) (p 4630) (p 4643) (p 4645) (p 4649) (p 4651) (p 4683) (p 4686) (p 4688) (p 4697) (p 4699) (p 4703) (p 4729) (p 4732) (p 4756) (p 4785) (p 4788) (p 4789) (p 4811) (p 4822) (p 4827) (p 4831) (p 4871) (p 4921) (p 4923) (p 4992) (p 4993) (p 4996) (p 5007) (p 5010) (p 5014) (p 5016) (p 5019) (p 5115) (p 5120) (p 5192) (p 5205) (p 5209) (p 5216) (p 5263) (p 5268) (p 5396) (p 5401) (p 5500) (p 5503) (p 5506) (p 5555) (p 5558) (p 5561) (p 5564) (p 5659) (p 5660) (p 5663) (derived63296 p h) (h 7902) (derived66390 p h) (h 7910) (h 7908) (h 7679) (h 7681) (h 6267) (h 3606) (derived66387 p h) (h 3620) (h 27638) (h 7805) (derived66383 p h) (h 7812) (h 3623) (h 9451) (h 7584) (derived66367 p h) (h 7588) (h 24547) (h 7435) (derived66355 p h) (h 7428) (h 20262) (h 8144) (derived66404 p h) (h 8137) (derived63098 p h) (h 9721) (derived66484 p h) (h 9728) (h 5947) (h 7680) (h 7589) (h 14339) (h 3449) (derived66378 p h) (h 3433) (h 7427) (h 26527) (h 8804) (h 8805) (h 20283) (h 7555) (derived66365 p h) (h 7549) (derived42186 p h) (derived42261 p h) (h 7401) (h 8375) (derived66353 p h) (derived66422 p h) (h 7395) (h 8369) (h 4598) (h 4597) (derived49291 p h) (h 3992) (h 4585) (h 7148) (derived66405 p h) (derived66433 p h) (derived66335 p h) (h 3977) (h 4570) (h 7142) (derived53117 p h) (derived44001 p h) (derived57164 p h) (h 7447) (h 9308) (h 7308) (derived66356 p h) (derived66468 p h) (derived66348 p h) (h 7453) (h 9314) (h 7315) (derived41590 p h) (derived42265 p h) (h 8833) (h 9589) (derived66447 p h) (derived66479 p h) (h 8839) (h 9583) (derived43991 p h) (h 10125) (derived66493 p h) (h 10119) (derived55859 p h) (h 8652) (derived66438 p h) (h 8646) (derived66678 p h) (h 7361) (derived66351 p h) (h 7367) (derived57165 p h) (h 6818) (h 8968) (derived66454 p h) (h 8962) (derived66679 p h) (derived66420 p h) (h 8333) (h 8334) (derived54781 p h) (h 19898) (h 8392) (h 8385) (derived66423 p h)

theorem derived66681 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4500) ∨ (¬ p 4992) ∨ (¬ p 2383) ∨ (¬ p 3860) :=
  ElevenRUP.step66681 (p 2307) (p 2310) (p 2313) (p 2317) (p 2383) (p 3093) (p 3309) (p 3549) (p 3860) (p 3923) (p 3955) (p 4500) (p 4501) (p 4992) (p 4993) (p 4994) (p 5014) (p 5016) (p 5019) (p 5020) (p 5140) (p 5143) (h 8334) (h 19898) (h 8385) (derived66423 p h) (h 8392) (h 8391) (h 8335) (h 8333) (h 7054) (h 7057) (h 19973) (derived51073 p h) (h 2756) (h 8711) (derived66343 p h) (derived66440 p h) (h 2770) (h 8705) (derived61066 p h)

theorem derived66682 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4868) ∨ (¬ p 3452) ∨ (¬ p 3923) ∨ (¬ p 2383) :=
  ElevenRUP.step66682 (p 2383) (p 2493) (p 2496) (p 2497) (p 2503) (p 2608) (p 2829) (p 3093) (p 3452) (p 3541) (p 3584) (p 3590) (p 3923) (p 3954) (p 4732) (p 4735) (p 4868) (p 4870) (p 5014) (p 5016) (p 5019) (p 5020) (p 5213) (p 5215) (p 5219) (p 5223) (p 5224) (h 19898) (h 8385) (derived66423 p h) (h 8392) (h 6132) (h 3125) (derived66362 p h) (h 3141) (h 8391) (h 8006) (h 8007) (derived42586 p h) (h 7681) (derived66374 p h) (h 7687) (h 5163) (h 8858) (derived66448 p h) (h 8852) (derived51425 p h) (h 19922) (h 8880) (h 8873) (derived66449 p h)

theorem derived66683 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3452) ∨ (¬ p 3923) ∨ (¬ p 2383) :=
  ElevenRUP.step66683 (p 2383) (p 2608) (p 3093) (p 3452) (p 3541) (p 3923) (p 3953) (p 3954) (p 4376) (p 4732) (p 4735) (p 4865) (p 4868) (p 5014) (p 5016) (p 5019) (p 5020) (p 5213) (p 5215) (h 19898) (h 8385) (derived66423 p h) (h 8392) (h 8391) (derived66682 p h) (derived66396 p h) (h 7998) (h 5866) (derived42594 p h) (h 7681) (h 8854) (derived66374 p h) (derived66448 p h) (h 7687) (h 8858) (h 5163)

theorem derived66684 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3367) ∨ (¬ p 4865) ∨ (¬ p 3923) ∨ (¬ p 2383) :=
  ElevenRUP.step66684 (p 2352) (p 2383) (p 2573) (p 2576) (p 2578) (p 2583) (p 2819) (p 3055) (p 3093) (p 3366) (p 3367) (p 3688) (p 3923) (p 3953) (p 3954) (p 4342) (p 4358) (p 4375) (p 4726) (p 4728) (p 4730) (p 4732) (p 4735) (p 4856) (p 4860) (p 4865) (p 5014) (p 5016) (p 5019) (p 5219) (p 5221) (p 5223) (h 19898) (h 8385) (derived66423 p h) (h 8392) (h 7998) (h 5866) (h 7681) (derived66374 p h) (h 7685) (h 8000) (h 4835) (h 23622) (h 7664) (h 8878) (derived66373 p h) (derived66449 p h) (h 7672) (h 8872) (h 8874) (derived41027 p h) (derived41149 p h) (h 3293) (h 7989) (derived66370 p h) (derived66395 p h) (h 3278) (h 7983) (h 29119) (derived43129 p h)

theorem derived66687 (p : Nat → Prop) (h : Inputs p) :
    (p 3583) ∨ (¬ p 4608) ∨ (¬ p 3874) ∨ (¬ p 3585) :=
  ElevenRUP.step66687 (p 2839) (p 3054) (p 3583) (p 3585) (p 3695) (p 3874) (p 4608) (p 4873) (p 4876) (p 4880) (p 4883) (h 8017) (h 37227) (derived66397 p h) (h 8032) (h 8023) (derived66398 p h) (derived52514 p h) (h 8038)

theorem derived66698 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5014) ∨ (¬ p 3063) ∨ (¬ p 2608) ∨ (¬ p 3589) ∨ (¬ p 4866) ∨ (¬ p 3918) ∨ (¬ p 4358) :=
  ElevenRUP.step66698 (p 2387) (p 2608) (p 2774) (p 2777) (p 2779) (p 2784) (p 3063) (p 3589) (p 3591) (p 3918) (p 4358) (p 4866) (p 5014) (p 5015) (h 8384) (h 8386) (derived48555 p h) (h 32770) (h 19665) (h 3697) (h 3682) (derived66391 p h)

theorem derived66699 (p : Nat → Prop) (h : Inputs p) :
    (p 2352) ∨ (¬ p 2440) ∨ (¬ p 3125) ∨ (¬ p 3322) ∨ (¬ p 2383) :=
  ElevenRUP.step66699 (p 2352) (p 2383) (p 2440) (p 2573) (p 2576) (p 2578) (p 2579) (p 2583) (p 2584) (p 2590) (p 2654) (p 2656) (p 2661) (p 2665) (p 3125) (p 3322) (p 3564) (p 3574) (p 3956) (p 4203) (p 4594) (p 4597) (p 4714) (p 4716) (h 7315) (h 29119) (h 27945) (derived66348 p h) (h 3278) (h 6764) (h 7309) (derived66370 p h) (h 7622) (h 3292) (h 3293) (derived66369 p h) (h 9992) (h 7616) (h 16654) (h 5860) (derived48290 p h) (h 3434) (h 3451) (derived66378 p h)

theorem derived66701 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3583) ∨ (¬ p 3876) ∨ (¬ p 3574) ∨ (¬ p 3684) ∨ (¬ p 3698) ∨ (¬ p 3362) ∨ (¬ p 3363) ∨ (¬ p 2132) ∨ (¬ p 2542) :=
  ElevenRUP.step66701 (p 2132) (p 2230) (p 2437) (p 2542) (p 2589) (p 2753) (p 3362) (p 3363) (p 3367) (p 3389) (p 3540) (p 3574) (p 3583) (p 3585) (p 3683) (p 3684) (p 3698) (p 3742) (p 3876) (p 4535) (p 4537) (p 4649) (p 4651) (p 4732) (p 4735) (p 4737) (p 4748) (p 4750) (p 4751) (p 5196) (p 5200) (p 5213) (p 5215) (h 5390) (h 7719) (derived66376 p h) (h 7717) (h 5391) (derived50540 p h) (h 7680) (h 8859) (derived66374 p h) (derived66448 p h) (h 7689) (h 8853) (derived41001 p h) (derived49312 p h) (h 7148) (h 8822) (derived66335 p h) (derived66446 p h) (h 7142) (h 8816) (derived43004 p h) (derived46819 p h) (h 7447) (h 7453) (derived66356 p h)

theorem derived66703 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5192) ∨ (¬ p 3834) ∨ (¬ p 3471) ∨ (¬ p 4366) ∨ (¬ p 3822) ∨ (¬ p 2753) ∨ (¬ p 3609) ∨ (¬ p 4256) ∨ (¬ p 3346) ∨ (¬ p 3540) ∨ (¬ p 2589) ∨ (¬ p 2751) ∨ (¬ p 2750) ∨ (¬ p 2319) ∨ (¬ p 2318) ∨ (¬ p 2553) ∨ (¬ p 3920) ∨ (¬ p 2657) ∨ (¬ p 2655) ∨ (¬ p 2810) ∨ (¬ p 4729) ∨ (¬ p 5222) ∨ (¬ p 2788) ∨ (¬ p 2786) ∨ (¬ p 4857) ∨ (¬ p 2383) ∨ (¬ p 2542) :=
  ElevenRUP.step66703 (p 2122) (p 2177) (p 2244) (p 2247) (p 2251) (p 2252) (p 2299) (p 2318) (p 2319) (p 2341) (p 2383) (p 2437) (p 2459) (p 2534) (p 2542) (p 2553) (p 2589) (p 2655) (p 2657) (p 2717) (p 2750) (p 2751) (p 2753) (p 2786) (p 2788) (p 2810) (p 2911) (p 2922) (p 2925) (p 2927) (p 2932) (p 3222) (p 3225) (p 3227) (p 3231) (p 3343) (p 3346) (p 3347) (p 3359) (p 3379) (p 3402) (p 3471) (p 3540) (p 3551) (p 3609) (p 3644) (p 3659) (p 3689) (p 3742) (p 3822) (p 3834) (p 3920) (p 4256) (p 4348) (p 4366) (p 4438) (p 4470) (p 4474) (p 4500) (p 4502) (p 4586) (p 4589) (p 4649) (p 4651) (p 4665) (p 4667) (p 4692) (p 4694) (p 4697) (p 4729) (p 4799) (p 4803) (p 4809) (p 4811) (p 4812) (p 4857) (p 4921) (p 4923) (p 5169) (p 5174) (p 5192) (p 5222) (h 9529) (h 6990) (derived66324 p h) (h 6982) (derived46836 p h) (h 7567) (derived66366 p h) (h 7575) (h 8803) (h 8805) (h 5162) (h 4809) (derived66648 p h) (h 3992) (h 4585) (derived66386 p h) (derived66405 p h) (derived66433 p h) (h 7855) (h 7859) (h 3977) (h 4570) (h 4899) (derived41590 p h) (derived42260 p h) (h 2625) (h 7453) (h 8765) (derived66336 p h) (derived66356 p h) (derived66443 p h) (h 2637) (h 7447) (h 8759) (derived53117 p h) (h 8138) (derived66404 p h) (h 8144) (h 8146) (derived42286 p h) (derived61974 p h) (h 7292) (h 7481) (derived66347 p h) (derived66358 p h) (h 7298) (h 7487) (derived40958 p h) (derived50993 p h) (h 7056) (h 7846) (derived66330 p h) (derived66385 p h) (h 7062) (h 7840) (derived53108 p h)

theorem derived66705 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3238) ∨ (¬ p 4111) ∨ (¬ p 3402) ∨ (¬ p 2247) ∨ (¬ p 3452) ∨ (¬ p 3822) ∨ (¬ p 5219) ∨ (¬ p 2553) ∨ (¬ p 2659) ∨ (¬ p 2542) ∨ (¬ p 4535) :=
  ElevenRUP.step66705 (p 2220) (p 2247) (p 2373) (p 2509) (p 2542) (p 2553) (p 2659) (p 2850) (p 2982) (p 3016) (p 3083) (p 3096) (p 3193) (p 3222) (p 3225) (p 3231) (p 3237) (p 3238) (p 3343) (p 3359) (p 3402) (p 3452) (p 3574) (p 3584) (p 3660) (p 3683) (p 3684) (p 3744) (p 3822) (p 3904) (p 3989) (p 4109) (p 4111) (p 4120) (p 4137) (p 4256) (p 4505) (p 4508) (p 4509) (p 4527) (p 4530) (p 4535) (p 4606) (p 4607) (p 4609) (p 4714) (p 4716) (p 4748) (p 4750) (p 4751) (p 4880) (p 4883) (p 4946) (p 4951) (p 4971) (p 4974) (p 5042) (p 5044) (p 5046) (p 5169) (p 5174) (p 5219) (p 5220) (p 5977) (p 5978) (h 8873) (h 8871) (h 7141) (h 7140) (derived48558 p h) (derived44020 p h) (h 8759) (h 8040) (derived66443 p h) (derived66398 p h) (h 8765) (h 8034) (h 5390) (h 7719) (derived66376 p h) (h 7717) (derived59246 p h) (h 8280) (h 6621) (derived66415 p h) (h 7623) (h 8274) (derived66369 p h) (derived44194 p h) (h 7617) (h 6861) (derived44325 p h) (h 8439) (h 7073) (derived66426 p h) (derived66331 p h) (h 8446) (h 7080) (derived50990 p h) (derived61866 p h) (h 8229) (h 7130) (derived66412 p h) (derived66334 p h) (h 8221) (h 7124) (h 4597) (derived40922 p h) (h 4585) (h 7349) (derived66433 p h) (derived66350 p h) (h 4571) (h 7341) (derived43960 p h) (h 22568) (h 12853) (derived43963 p h) (derived66566 p h) (h 12860)

theorem derived66707 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3193) ∨ (¬ p 3343) ∨ (¬ p 3256) ∨ (¬ p 3574) ∨ (¬ p 4598) ∨ (¬ p 3402) ∨ (¬ p 2247) ∨ (¬ p 3452) :=
  ElevenRUP.step66707 (p 2247) (p 2509) (p 2534) (p 3083) (p 3193) (p 3256) (p 3343) (p 3358) (p 3402) (p 3452) (p 3574) (p 4121) (p 4256) (p 4598) (p 5007) (p 5010) (p 5869) (p 5870) (derived43960 p h) (h 8369) (derived66422 p h) (h 8374) (h 8375) (derived41271 p h) (derived43963 p h) (h 12206) (h 33686) (derived66531 p h) (h 12212)

theorem derived66709 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5010) ∨ (¬ p 3359) ∨ (¬ p 3256) ∨ (¬ p 3574) ∨ (¬ p 4598) :=
  ElevenRUP.step66709 (p 2534) (p 3083) (p 3256) (p 3358) (p 3359) (p 3574) (p 4121) (p 4598) (p 4692) (p 4694) (p 5010) (h 8374) (h 8375) (derived41271 p h) (h 4830) (h 7567) (h 7572) (derived66366 p h)

theorem derived66712 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4856) ∨ (¬ p 4340) ∨ (¬ p 4871) ∨ (¬ p 3063) ∨ (¬ p 4341) ∨ (¬ p 4843) ∨ (¬ p 3256) :=
  ElevenRUP.step66712 (p 2363) (p 3063) (p 3256) (p 4078) (p 4340) (p 4341) (p 4347) (p 4358) (p 4600) (p 4602) (p 4843) (p 4856) (p 4871) (h 7981) (h 7983) (derived64438 p h) (derived51999 p h) (h 7332) (h 7326) (derived66349 p h)

theorem derived66713 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4600) ∨ (¬ p 3680) ∨ (¬ p 4134) ∨ (¬ p 3693) ∨ (¬ p 4191) ∨ (¬ p 2528) :=
  ElevenRUP.step66713 (p 2528) (p 2533) (p 3266) (p 3322) (p 3680) (p 3692) (p 3693) (p 4134) (p 4191) (p 4347) (p 4444) (p 4600) (p 5055) (p 5057) (p 5115) (p 5120) (h 5396) (h 8473) (derived66428 p h) (h 8478) (h 7324) (h 7326) (derived56571 p h) (derived55233 p h) (h 8652) (h 8646) (derived66438 p h)

theorem derived66717 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2313) ∨ (¬ p 4198) ∨ (¬ p 4533) ∨ (¬ p 2440) ∨ (¬ p 3879) ∨ (¬ p 2274) ∨ (¬ p 3662) ∨ (¬ p 2244) :=
  ElevenRUP.step66717 (p 2244) (p 2245) (p 2247) (p 2274) (p 2284) (p 2295) (p 2313) (p 2440) (p 2563) (p 2590) (p 2651) (p 2654) (p 2657) (p 2661) (p 2667) (p 2727) (p 3016) (p 3568) (p 3662) (p 3879) (p 3952) (p 3983) (p 4110) (p 4111) (p 4153) (p 4154) (p 4198) (p 4533) (p 4562) (p 4565) (p 4568) (p 4571) (p 4579) (p 4582) (p 4714) (p 4716) (p 4809) (p 4812) (p 4971) (p 4972) (p 4974) (h 2625) (h 2623) (derived60888 p h) (h 7624) (derived66369 p h) (h 7616) (h 7618) (h 20304) (derived43961 p h) (h 27148) (h 19752) (h 8280) (h 7857) (h 7226) (derived66415 p h) (derived66386 p h) (derived66341 p h) (h 8275) (h 7863) (h 7218) (derived44003 p h) (h 6201) (h 3435) (derived47738 p h) (derived66378 p h) (h 7237) (h 33740) (h 3449) (derived66342 p h) (h 7279) (h 7243) (derived66346 p h) (derived51734 p h) (h 7273)

theorem derived66718 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4484) ∨ (¬ p 4533) ∨ (¬ p 2589) ∨ (¬ p 2440) ∨ (¬ p 3879) ∨ (¬ p 2274) ∨ (¬ p 5224) ∨ (¬ p 3662) ∨ (¬ p 3822) ∨ (¬ p 2244) :=
  ElevenRUP.step66718 (p 2244) (p 2245) (p 2246) (p 2247) (p 2274) (p 2284) (p 2307) (p 2310) (p 2313) (p 2317) (p 2318) (p 2331) (p 2437) (p 2440) (p 2553) (p 2563) (p 2573) (p 2576) (p 2578) (p 2583) (p 2589) (p 2590) (p 2630) (p 2651) (p 2654) (p 2657) (p 2661) (p 2727) (p 2777) (p 2779) (p 2784) (p 2786) (p 2810) (p 2850) (p 2901) (p 2946) (p 2949) (p 2952) (p 2956) (p 2996) (p 3016) (p 3051) (p 3055) (p 3097) (p 3363) (p 3414) (p 3567) (p 3568) (p 3646) (p 3662) (p 3691) (p 3743) (p 3822) (p 3879) (p 3952) (p 4110) (p 4111) (p 4140) (p 4153) (p 4154) (p 4185) (p 4193) (p 4198) (p 4328) (p 4386) (p 4484) (p 4533) (p 4554) (p 4557) (p 4562) (p 4565) (p 4579) (p 4582) (p 4646) (p 4649) (p 4650) (p 4651) (p 4714) (p 4716) (p 4726) (p 4728) (p 4748) (p 4751) (p 4809) (p 4812) (p 4840) (p 4841) (p 4844) (p 4880) (p 4882) (p 4883) (p 4887) (p 4889) (p 4890) (p 4916) (p 4918) (p 4971) (p 4972) (p 4974) (p 4983) (p 4987) (p 5224) (h 20290) (h 8055) (derived66399 p h) (h 8053) (h 8049) (h 9860) (h 7202) (derived66340 p h) (h 7206) (h 2625) (h 2624) (h 2623) (h 7020) (h 7021) (h 7022) (derived41366 p h) (h 8321) (derived66419 p h) (h 8314) (derived66717 p h) (h 2756) (derived66343 p h) (h 2768) (h 2770) (h 5636) (h 3682) (derived66391 p h) (h 3696) (derived49446 p h) (h 7664) (derived66373 p h) (h 7668) (h 20692) (h 8040) (derived66398 p h) (h 8036) (derived63220 p h) (h 7624) (derived66369 p h) (h 7616) (h 7618) (h 20304) (h 3306) (derived47642 p h) (derived43961 p h) (h 27148) (h 19752) (h 8280) (h 3293) (h 7857) (derived62924 p h) (h 7226) (derived66415 p h) (derived66370 p h) (derived66386 p h) (h 8127) (derived66341 p h) (h 8275) (h 3278) (h 7863) (derived66403 p h) (h 7218) (h 25746) (derived40954 p h) (derived44003 p h) (h 8119) (h 6201) (derived44623 p h) (h 7453) (h 3435) (h 25522) (h 25390) (derived66356 p h) (derived66378 p h) (h 21894) (h 7951) (h 7448) (h 3449) (derived48093 p h) (derived45716 p h) (derived66394 p h) (h 4042) (h 7281) (h 7945) (derived66408 p h) (derived66346 p h) (h 4028) (h 7274) (derived64204 p h) (derived52981 p h) (h 7715) (h 7721) (derived66376 p h)

theorem derived66719 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2156) ∨ (¬ p 2274) ∨ (¬ p 3822) :=
  ElevenRUP.step66719 (p 2135) (p 2137) (p 2142) (p 2146) (p 2156) (p 2274) (p 3758) (p 3822) (p 4185) (p 4193) (p 4887) (p 4890) (h 20290) (h 8055) (derived66399 p h) (h 8051) (h 8049) (derived49213 p h) (h 5508) (h 2424) (h 2407) (derived66325 p h)

theorem derived66720 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4699) ∨ (¬ p 4533) ∨ (¬ p 3662) ∨ (¬ p 2244) ∨ (¬ p 2313) ∨ (¬ p 4198) ∨ (¬ p 2274) :=
  ElevenRUP.step66720 (p 2244) (p 2274) (p 2313) (p 2440) (p 3662) (p 3879) (p 4198) (p 4533) (p 4699) (h 7583) (h 7584) (derived66717 p h)

theorem derived66721 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3574) ∨ (¬ p 2737) ∨ (¬ p 4734) ∨ (¬ p 3055) ∨ (¬ p 4343) ∨ (¬ p 3905) ∨ (¬ p 2542) ∨ (¬ p 2589) ∨ (¬ p 3365) :=
  ElevenRUP.step66721 (p 2542) (p 2589) (p 2737) (p 2850) (p 3055) (p 3365) (p 3367) (p 3574) (p 3585) (p 3684) (p 3905) (p 4343) (p 4734) (p 4880) (p 4883) (p 5213) (p 5215) (derived54113 p h) (derived47342 p h) (h 8853) (h 8034) (derived66448 p h) (derived66398 p h) (h 8859) (h 8040) (derived49770 p h)

theorem derived66722 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4535) ∨ (¬ p 3662) ∨ (¬ p 2244) ∨ (¬ p 2313) ∨ (¬ p 4787) ∨ (¬ p 3365) ∨ (¬ p 4236) ∨ (¬ p 4484) ∨ (¬ p 2274) :=
  ElevenRUP.step66722 (p 2244) (p 2247) (p 2274) (p 2284) (p 2295) (p 2313) (p 2427) (p 2542) (p 2553) (p 2563) (p 2577) (p 2579) (p 2588) (p 2589) (p 2590) (p 2608) (p 2630) (p 2654) (p 2655) (p 2659) (p 2661) (p 2662) (p 2737) (p 2740) (p 2743) (p 2747) (p 2810) (p 3016) (p 3019) (p 3055) (p 3097) (p 3136) (p 3364) (p 3365) (p 3413) (p 3568) (p 3574) (p 3662) (p 3872) (p 3904) (p 3905) (p 3952) (p 3954) (p 4110) (p 4140) (p 4153) (p 4154) (p 4198) (p 4235) (p 4236) (p 4315) (p 4343) (p 4484) (p 4486) (p 4533) (p 4535) (p 4554) (p 4557) (p 4562) (p 4565) (p 4568) (p 4571) (p 4643) (p 4645) (p 4699) (p 4703) (p 4705) (p 4707) (p 4709) (p 4714) (p 4716) (p 4732) (p 4734) (p 4735) (p 4748) (p 4751) (p 4787) (p 4971) (p 4974) (p 5048) (p 5050) (h 2625) (h 7024) (h 7020) (h 9860) (h 7202) (derived66340 p h) (h 7207) (h 7206) (h 7140) (h 7142) (h 7144) (h 26538) (derived53718 p h) (derived60888 p h) (h 7624) (derived66369 p h) (h 7616) (h 7618) (h 22679) (derived51737 p h) (h 7435) (derived66355 p h) (h 7429) (derived66720 p h) (derived66367 p h) (h 7589) (h 7590) (h 6146) (h 3447) (derived66378 p h) (h 3433) (h 3437) (derived49377 p h) (h 15561) (derived65914 p h) (h 7721) (h 7226) (derived66376 p h) (derived66341 p h) (h 7713) (h 7714) (h 7715) (h 7218) (h 7220) (h 6408) (derived47356 p h) (h 6201) (derived46320 p h) (h 8462) (derived47738 p h) (h 7687) (derived66427 p h) (h 7237) (derived66374 p h) (h 8456) (derived66342 p h) (h 7681) (h 7683) (derived46288 p h) (h 7243) (h 3608) (derived66387 p h) (h 3622) (derived66721 p h) (h 8274) (derived66415 p h) (h 8279) (h 8280) (derived41816 p h) (derived48685 p h) (h 7601) (h 7607) (derived66368 p h)

theorem derived66727 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2553) ∨ (¬ p 2313) ∨ (¬ p 2659) ∨ (¬ p 3016) :=
  ElevenRUP.step66727 (p 2313) (p 2386) (p 2553) (p 2576) (p 2577) (p 2583) (p 2659) (p 3016) (h 15355) (derived48685 p h) (h 3291) (h 3277) (derived66370 p h)

theorem derived66733 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2588) ∨ (p 2797) ∨ (¬ p 2295) ∨ (¬ p 3146) ∨ (¬ p 3958) ∨ (¬ p 4704) ∨ (¬ p 3872) ∨ (¬ p 2274) ∨ (p 3822) ∨ (¬ p 2780) ∨ (¬ p 2881) ∨ (¬ p 2946) ∨ (¬ p 2811) ∨ (¬ p 2737) ∨ (¬ p 2307) :=
  ElevenRUP.step66733 (p 2122) (p 2177) (p 2190) (p 2274) (p 2295) (p 2299) (p 2307) (p 2352) (p 2363) (p 2383) (p 2459) (p 2553) (p 2576) (p 2578) (p 2583) (p 2584) (p 2588) (p 2598) (p 2630) (p 2737) (p 2780) (p 2797) (p 2811) (p 2881) (p 2911) (p 2946) (p 3019) (p 3146) (p 3325) (p 3367) (p 3389) (p 3581) (p 3585) (p 3644) (p 3759) (p 3822) (p 3872) (p 3921) (p 3956) (p 3958) (p 3989) (p 4342) (p 4343) (p 4347) (p 4348) (p 4375) (p 4389) (p 4470) (p 4474) (p 4500) (p 4502) (p 4505) (p 4508) (p 4594) (p 4597) (p 4600) (p 4602) (p 4665) (p 4667) (p 4704) (p 4707) (p 4709) (p 4726) (p 4728) (p 4748) (p 4751) (p 4921) (p 4923) (p 4971) (p 4974) (p 5213) (p 5215) (p 5219) (p 5223) (h 6984) (derived66324 p h) (h 6990) (h 9753) (h 14557) (derived51714 p h) (h 6589) (h 20173) (h 7607) (h 3278) (h 7056) (h 8872) (h 8273) (derived66368 p h) (derived66370 p h) (derived66330 p h) (derived66449 p h) (derived66415 p h) (h 7599) (h 7600) (h 3292) (h 7061) (h 7062) (h 8878) (h 8279) (h 22168) (h 20380) (h 6137) (derived60360 p h) (h 20127) (h 27541) (h 7073) (h 8138) (h 7670) (h 7721) (derived66331 p h) (derived66404 p h) (derived66373 p h) (derived66376 p h) (h 7078) (h 8144) (h 7663) (h 7714) (derived52009 p h) (h 8853) (derived66448 p h) (h 8859) (derived45031 p h) (derived44970 p h) (h 7315) (h 7487) (derived66348 p h) (derived66358 p h) (h 7309) (h 7481) (derived41157 p h) (derived43183 p h) (h 7326) (h 7332) (derived66349 p h)

theorem derived66734 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4748) ∨ (¬ p 3759) ∨ (¬ p 2553) ∨ (¬ p 2396) ∨ (¬ p 4715) ∨ (¬ p 4703) ∨ (¬ p 4785) ∨ (¬ p 2747) ∨ (¬ p 4734) ∨ (¬ p 2992) :=
  ElevenRUP.step66734 (p 2396) (p 2493) (p 2496) (p 2499) (p 2503) (p 2553) (p 2573) (p 2576) (p 2579) (p 2583) (p 2651) (p 2654) (p 2655) (p 2661) (p 2727) (p 2737) (p 2747) (p 2749) (p 2810) (p 2811) (p 2946) (p 2949) (p 2952) (p 2956) (p 2992) (p 3136) (p 3365) (p 3367) (p 3585) (p 3759) (p 4116) (p 4236) (p 4315) (p 4343) (p 4703) (p 4704) (p 4715) (p 4734) (p 4748) (p 4785) (p 4809) (p 4812) (p 5048) (p 5050) (p 5213) (p 5215) (h 7591) (h 7803) (h 3622) (h 3621) (h 7805) (derived53161 p h) (h 8456) (derived66427 p h) (h 8462) (derived51323 p h) (h 4028) (derived66408 p h) (h 4042) (h 7804) (h 7714) (h 7715) (derived52009 p h) (derived50005 p h) (h 3749) (h 8853) (h 7863) (h 3449) (derived66448 p h) (derived66386 p h) (derived66378 p h) (h 8859) (h 7856) (derived65966 p h) (h 3433) (derived46194 p h) (h 3127) (h 3293) (derived66362 p h) (derived66370 p h) (h 3141) (h 3279) (derived53224 p h)

theorem derived66735 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2630) ∨ (¬ p 2553) ∨ (¬ p 2963) ∨ (¬ p 4715) ∨ (¬ p 2542) ∨ (¬ p 4236) ∨ (¬ p 2737) ∨ (¬ p 4734) :=
  ElevenRUP.step66735 (p 2542) (p 2553) (p 2630) (p 2651) (p 2654) (p 2657) (p 2661) (p 2737) (p 2797) (p 2963) (p 3016) (p 4195) (p 4236) (p 4389) (p 4715) (p 4734) (p 4840) (p 4844) (p 4971) (p 4974) (derived62070 p h) (h 7953) (derived66394 p h) (h 7947) (derived51929 p h) (derived42791 p h) (h 8280) (h 3435) (derived66415 p h) (derived66378 p h) (h 8273) (h 3449) (derived49230 p h)

theorem derived66736 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2295) ∨ (¬ p 2396) ∨ (¬ p 3146) ∨ (¬ p 3958) ∨ (¬ p 4715) ∨ (¬ p 4703) ∨ (¬ p 3872) ∨ (¬ p 2274) ∨ (p 3822) ∨ (¬ p 2780) ∨ (¬ p 2881) ∨ (¬ p 4785) ∨ (¬ p 2747) ∨ (¬ p 4734) ∨ (¬ p 2307) ∨ (¬ p 2992) :=
  ElevenRUP.step66736 (p 2274) (p 2295) (p 2307) (p 2331) (p 2396) (p 2542) (p 2553) (p 2588) (p 2598) (p 2630) (p 2737) (p 2747) (p 2749) (p 2780) (p 2797) (p 2811) (p 2881) (p 2946) (p 2949) (p 2952) (p 2956) (p 2963) (p 2992) (p 3055) (p 3136) (p 3146) (p 3364) (p 3365) (p 3759) (p 3822) (p 3872) (p 3958) (p 4236) (p 4315) (p 4579) (p 4582) (p 4703) (p 4704) (p 4707) (p 4709) (p 4715) (p 4734) (p 4748) (p 4751) (p 4785) (p 5048) (p 5050) (p 5881) (p 5882) (h 7591) (h 7590) (h 7803) (h 3622) (h 3621) (h 7805) (derived53161 p h) (h 8456) (derived66427 p h) (h 8462) (derived51323 p h) (h 4028) (derived66408 p h) (h 4042) (h 7804) (derived45486 p h) (h 7281) (derived66346 p h) (h 7275) (derived62070 p h) (derived66733 p h) (h 7601) (derived66368 p h) (h 7607) (derived66735 p h) (h 7721) (derived66376 p h) (h 7713) (derived66734 p h) (h 6408) (h 12278) (h 9095) (derived66535 p h) (h 12280)

theorem derived66737 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2396) ∨ (¬ p 5057) ∨ (¬ p 3958) ∨ (¬ p 4715) ∨ (¬ p 4703) ∨ (¬ p 3309) ∨ (p 3549) ∨ (¬ p 3872) ∨ (¬ p 2274) ∨ (¬ p 2779) ∨ (¬ p 2780) ∨ (¬ p 3758) ∨ (¬ p 4903) ∨ (¬ p 2138) ∨ (¬ p 4785) ∨ (¬ p 3371) ∨ (¬ p 2747) ∨ (¬ p 4734) ∨ (¬ p 2307) ∨ (¬ p 4564) ∨ (¬ p 2992) :=
  ElevenRUP.step66737 (p 2122) (p 2138) (p 2177) (p 2190) (p 2274) (p 2295) (p 2299) (p 2307) (p 2363) (p 2396) (p 2459) (p 2532) (p 2533) (p 2619) (p 2668) (p 2737) (p 2743) (p 2747) (p 2749) (p 2761) (p 2779) (p 2780) (p 2811) (p 2829) (p 2881) (p 2946) (p 2949) (p 2952) (p 2956) (p 2963) (p 2972) (p 2992) (p 3073) (p 3105) (p 3136) (p 3146) (p 3266) (p 3309) (p 3324) (p 3325) (p 3365) (p 3371) (p 3547) (p 3548) (p 3549) (p 3568) (p 3583) (p 3657) (p 3680) (p 3694) (p 3758) (p 3791) (p 3822) (p 3872) (p 3923) (p 3941) (p 3958) (p 3987) (p 3989) (p 4075) (p 4189) (p 4236) (p 4243) (p 4260) (p 4313) (p 4315) (p 4318) (p 4319) (p 4322) (p 4337) (p 4347) (p 4348) (p 4363) (p 4381) (p 4385) (p 4426) (p 4442) (p 4444) (p 4452) (p 4470) (p 4474) (p 4500) (p 4502) (p 4503) (p 4505) (p 4508) (p 4564) (p 4568) (p 4571) (p 4579) (p 4582) (p 4600) (p 4602) (p 4665) (p 4667) (p 4703) (p 4715) (p 4734) (p 4739) (p 4743) (p 4755) (p 4758) (p 4761) (p 4768) (p 4772) (p 4785) (p 4822) (p 4826) (p 4827) (p 4840) (p 4844) (p 4873) (p 4876) (p 4903) (p 4905) (p 4937) (p 4941) (p 4992) (p 4996) (p 5024) (p 5029) (p 5048) (p 5050) (p 5057) (p 5115) (p 5120) (p 5140) (p 5143) (p 5304) (p 5306) (p 5396) (p 5401) (p 5469) (p 5474) (p 5555) (p 5559) (p 5561) (p 5643) (p 5648) (h 8479) (h 8478) (h 8477) (h 8705) (derived66440 p h) (h 8710) (h 8709) (h 5636) (h 6984) (derived66324 p h) (h 6990) (h 8094) (h 8092) (h 7803) (h 3622) (h 3621) (h 7805) (derived53161 p h) (h 8456) (derived66427 p h) (h 8462) (derived51323 p h) (h 4028) (derived66408 p h) (h 4042) (h 10031) (h 8461) (h 29019) (h 8017) (derived66397 p h) (h 8021) (h 7804) (derived66736 p h) (h 7243) (h 16173) (derived66342 p h) (h 7732) (h 7237) (derived66377 p h) (derived41403 p h) (h 17602) (derived45307 p h) (h 7741) (h 7056) (h 7946) (h 7275) (derived66330 p h) (derived66394 p h) (derived66346 p h) (h 7061) (h 7062) (h 7064) (h 7952) (h 7280) (h 20380) (h 6935) (h 5166) (h 6835) (derived64504 p h) (h 7073) (h 8334) (h 9038) (derived46120 p h) (derived46850 p h) (derived46848 p h) (h 7777) (derived66331 p h) (derived66420 p h) (derived66458 p h) (h 7908) (h 7487) (h 9727) (derived66381 p h) (h 7078) (h 8338) (h 9043) (derived66390 p h) (derived66358 p h) (derived66484 p h) (h 7771) (h 7902) (h 7904) (h 7479) (h 7481) (h 9722) (derived55133 p h) (derived54461 p h) (h 7326) (h 7704) (derived66349 p h) (derived66375 p h) (h 7332) (h 7698) (h 21751) (derived41140 p h) (derived54699 p h) (derived53989 p h) (h 8652) (h 8411) (h 10001) (derived66438 p h) (derived66424 p h) (derived66492 p h) (h 8646) (h 8405) (h 10007) (derived41740 p h) (derived55011 p h) (derived42554 p h) (h 9314) (h 8212) (h 9481) (derived66468 p h) (derived66411 p h) (derived66477 p h) (h 9308) (h 8206) (h 9487) (derived56274 p h)

theorem derived66738 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 5057) ∨ (¬ p 3958) ∨ (¬ p 4715) ∨ (¬ p 4703) ∨ (¬ p 3309) ∨ (p 3549) ∨ (¬ p 3872) ∨ (¬ p 2274) ∨ (¬ p 2779) ∨ (¬ p 2780) ∨ (¬ p 3758) ∨ (¬ p 4903) ∨ (¬ p 2138) ∨ (¬ p 4785) ∨ (¬ p 3371) ∨ (¬ p 2747) ∨ (¬ p 4734) ∨ (¬ p 2307) ∨ (¬ p 4564) ∨ (¬ p 2992) :=
  ElevenRUP.step66738 (p 2138) (p 2177) (p 2274) (p 2295) (p 2299) (p 2307) (p 2331) (p 2352) (p 2363) (p 2396) (p 2459) (p 2493) (p 2496) (p 2499) (p 2503) (p 2542) (p 2553) (p 2573) (p 2576) (p 2579) (p 2583) (p 2588) (p 2598) (p 2630) (p 2651) (p 2654) (p 2655) (p 2661) (p 2668) (p 2727) (p 2737) (p 2747) (p 2749) (p 2779) (p 2780) (p 2810) (p 2811) (p 2881) (p 2946) (p 2949) (p 2952) (p 2956) (p 2963) (p 2992) (p 3055) (p 3136) (p 3146) (p 3309) (p 3324) (p 3364) (p 3365) (p 3367) (p 3371) (p 3549) (p 3568) (p 3585) (p 3758) (p 3759) (p 3872) (p 3945) (p 3955) (p 3956) (p 3958) (p 4107) (p 4116) (p 4138) (p 4236) (p 4315) (p 4343) (p 4347) (p 4500) (p 4502) (p 4559) (p 4564) (p 4568) (p 4571) (p 4579) (p 4582) (p 4594) (p 4597) (p 4600) (p 4602) (p 4619) (p 4622) (p 4665) (p 4667) (p 4703) (p 4704) (p 4707) (p 4709) (p 4715) (p 4726) (p 4728) (p 4734) (p 4748) (p 4751) (p 4768) (p 4772) (p 4785) (p 4809) (p 4812) (p 4903) (p 5048) (p 5050) (p 5057) (p 5213) (p 5215) (h 7591) (h 7590) (h 8092) (derived65788 p h) (h 7803) (h 3622) (h 3621) (h 7805) (derived53161 p h) (h 8456) (derived66427 p h) (h 8462) (derived51323 p h) (h 4028) (derived66408 p h) (h 4042) (h 7804) (h 8479) (derived66737 p h) (h 7384) (derived66352 p h) (h 7378) (derived65751 p h) (derived66358 p h) (h 7486) (h 7487) (h 20089) (h 24089) (h 7062) (derived51714 p h) (derived41403 p h) (derived66330 p h) (h 7601) (h 7237) (h 7054) (h 7055) (derived66368 p h) (derived66342 p h) (derived41812 p h) (h 7607) (h 7243) (h 7326) (derived41813 p h) (derived48283 p h) (derived66349 p h) (h 7309) (h 7771) (h 7332) (derived66348 p h) (derived66381 p h) (h 7315) (h 7777) (derived45524 p h) (h 7281) (derived66346 p h) (h 7275) (derived66735 p h) (h 7721) (derived66376 p h) (h 7713) (h 7714) (h 7715) (h 6408) (derived52009 p h) (derived50005 p h) (h 3749) (h 9095) (h 8853) (h 7863) (h 3449) (h 7670) (derived66448 p h) (derived66386 p h) (derived66378 p h) (derived66373 p h) (h 8859) (h 7856) (derived65966 p h) (h 3433) (h 7663) (h 3127) (derived46189 p h) (derived66362 p h) (h 3293) (h 3141) (derived66370 p h) (derived53224 p h) (h 3279)

theorem derived66741 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4551) ∨ (¬ p 3189) ∨ (¬ p 3644) ∨ (¬ p 4653) ∨ (¬ p 4111) :=
  ElevenRUP.step66741 (p 2264) (p 2996) (p 3027) (p 3030) (p 3036) (p 3189) (p 3644) (p 4111) (p 4378) (p 4551) (p 4653) (h 7189) (h 7191) (derived48739 p h) (derived58487 p h) (h 4185) (h 4199) (derived66416 p h)

theorem derived66742 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3189) ∨ (¬ p 3527) ∨ (¬ p 3644) ∨ (¬ p 4653) ∨ (¬ p 4652) ∨ (¬ p 4111) :=
  ElevenRUP.step66742 (p 2996) (p 3030) (p 3036) (p 3038) (p 3189) (p 3527) (p 3553) (p 3644) (p 3919) (p 4111) (p 4547) (p 4551) (p 4652) (p 4653) (derived66741 p h) (derived66339 p h) (h 7183) (h 7185) (h 22466) (derived52473 p h) (h 4185) (h 4198) (derived66416 p h)

theorem derived66743 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4500) ∨ (¬ p 2138) ∨ (¬ p 4903) ∨ (¬ p 4619) ∨ (¬ p 2946) ∨ (¬ p 2963) ∨ (¬ p 4714) ∨ (¬ p 4703) ∨ (¬ p 4785) ∨ (¬ p 2747) :=
  ElevenRUP.step66743 (p 2138) (p 2192) (p 2241) (p 2244) (p 2247) (p 2251) (p 2274) (p 2295) (p 2299) (p 2307) (p 2310) (p 2313) (p 2317) (p 2331) (p 2341) (p 2352) (p 2363) (p 2417) (p 2427) (p 2437) (p 2459) (p 2493) (p 2496) (p 2499) (p 2503) (p 2542) (p 2553) (p 2573) (p 2576) (p 2579) (p 2583) (p 2588) (p 2598) (p 2619) (p 2630) (p 2641) (p 2651) (p 2654) (p 2655) (p 2661) (p 2707) (p 2717) (p 2727) (p 2737) (p 2743) (p 2747) (p 2748) (p 2749) (p 2774) (p 2777) (p 2779) (p 2780) (p 2784) (p 2797) (p 2810) (p 2811) (p 2870) (p 2881) (p 2901) (p 2911) (p 2925) (p 2928) (p 2932) (p 2934) (p 2946) (p 2963) (p 2992) (p 3055) (p 3093) (p 3097) (p 3136) (p 3156) (p 3189) (p 3246) (p 3266) (p 3276) (p 3309) (p 3346) (p 3355) (p 3364) (p 3365) (p 3366) (p 3367) (p 3371) (p 3389) (p 3425) (p 3461) (p 3471) (p 3527) (p 3540) (p 3541) (p 3548) (p 3549) (p 3551) (p 3564) (p 3568) (p 3576) (p 3583) (p 3585) (p 3588) (p 3644) (p 3659) (p 3662) (p 3687) (p 3690) (p 3692) (p 3694) (p 3742) (p 3745) (p 3746) (p 3747) (p 3758) (p 3759) (p 3820) (p 3872) (p 3873) (p 3876) (p 3920) (p 3941) (p 3956) (p 3958) (p 3969) (p 3983) (p 4042) (p 4107) (p 4111) (p 4116) (p 4118) (p 4136) (p 4137) (p 4138) (p 4154) (p 4169) (p 4173) (p 4191) (p 4195) (p 4236) (p 4241) (p 4243) (p 4244) (p 4245) (p 4312) (p 4313) (p 4315) (p 4320) (p 4330) (p 4336) (p 4343) (p 4360) (p 4365) (p 4396) (p 4425) (p 4444) (p 4445) (p 4500) (p 4511) (p 4515) (p 4554) (p 4557) (p 4558) (p 4559) (p 4562) (p 4563) (p 4564) (p 4565) (p 4568) (p 4571) (p 4579) (p 4582) (p 4586) (p 4589) (p 4594) (p 4597) (p 4600) (p 4602) (p 4619) (p 4620) (p 4634) (p 4637) (p 4639) (p 4643) (p 4644) (p 4645) (p 4649) (p 4651) (p 4652) (p 4653) (p 4665) (p 4667) (p 4703) (p 4704) (p 4707) (p 4709) (p 4714) (p 4715) (p 4726) (p 4728) (p 4732) (p 4734) (p 4735) (p 4739) (p 4743) (p 4748) (p 4751) (p 4755) (p 4758) (p 4785) (p 4792) (p 4795) (p 4799) (p 4803) (p 4809) (p 4812) (p 4840) (p 4841) (p 4844) (p 4873) (p 4876) (p 4893) (p 4896) (p 4903) (p 4916) (p 4918) (p 4921) (p 4923) (p 4956) (p 4958) (p 4960) (p 5014) (p 5016) (p 5019) (p 5048) (p 5050) (p 5055) (p 5057) (p 5061) (p 5064) (p 5073) (p 5077) (p 5081) (p 5084) (p 5085) (p 5101) (p 5103) (p 5115) (p 5120) (p 5122) (p 5123) (p 5125) (p 5130) (p 5180) (p 5185) (p 5196) (p 5200) (p 5201) (p 5213) (p 5215) (p 5246) (p 5251) (p 5256) (p 5259) (p 5304) (p 5306) (p 5320) (p 5323) (p 5555) (p 5558) (p 5561) (p 5567) (p 5568) (p 5571) (h 8090) (h 3620) (h 7804) (h 20425) (h 38119) (h 8240) (derived66413 p h) (h 8246) (h 20688) (h 7225) (derived66341 p h) (h 7222) (h 7221) (h 8311) (h 7281) (derived66346 p h) (h 7273) (h 3622) (h 7805) (h 4837) (h 7685) (derived66374 p h) (h 7683) (h 3621) (h 7803) (derived62070 p h) (h 7953) (derived66394 p h) (h 7947) (derived49583 p h) (h 7739) (derived66377 p h) (h 7733) (h 7679) (h 27638) (h 2639) (derived66336 p h) (h 2625) (h 7378) (derived46396 p h) (h 7237) (derived66342 p h) (h 7243) (derived54164 p h) (h 2756) (derived66343 p h) (h 2770) (h 8245) (h 31670) (h 7731) (h 6376) (h 8392) (derived66423 p h) (h 8385) (h 19537) (h 10031) (h 8456) (derived66427 p h) (h 8461) (h 29019) (h 8017) (derived66397 p h) (h 8021) (h 8248) (h 7219) (derived53120 p h) (h 7096) (derived66332 p h) (h 7090) (h 6606) (h 7945) (h 14306) (h 23885) (h 3697) (derived66391 p h) (h 3682) (h 6546) (h 6933) (h 7202) (derived66340 p h) (h 7207) (h 19100) (h 7620) (h 7619) (derived66738 p h) (derived66428 p h) (h 8473) (h 20084) (h 7487) (derived66358 p h) (h 7480) (h 8092) (h 8091) (h 7209) (derived62975 p h) (h 8127) (derived66403 p h) (h 8121) (h 7588) (h 30539) (derived51039 p h) (h 7435) (derived66355 p h) (h 7430) (h 7210) (h 7379) (h 7377) (h 7591) (h 7590) (h 7055) (h 7056) (h 37912) (derived51714 p h) (derived52582 p h) (derived47805 p h) (h 7332) (h 7601) (h 8496) (h 8074) (derived66349 p h) (derived66368 p h) (derived66429 p h) (derived66400 p h) (h 7328) (h 7606) (h 7607) (h 8489) (h 8066) (h 8067) (h 8068) (derived41813 p h) (derived66735 p h) (h 6676) (h 19003) (h 20417) (derived48827 p h) (h 7309) (h 7721) (h 8951) (h 7704) (derived66348 p h) (derived66376 p h) (derived66453 p h) (derived66375 p h) (h 7315) (h 7713) (h 7714) (h 7715) (h 8943) (h 7698) (h 6408) (derived52009 p h) (derived50005 p h) (h 3749) (derived46195 p h) (h 9095) (h 8853) (h 7863) (h 3449) (h 8646) (h 7670) (derived66448 p h) (derived66386 p h) (derived66378 p h) (derived66438 p h) (derived66373 p h) (h 8858) (h 8859) (h 7856) (h 7857) (derived65966 p h) (h 3433) (h 8652) (h 8653) (h 8654) (h 7663) (derived51415 p h) (h 3127) (h 6412) (h 7447) (derived66362 p h) (h 3978) (derived66356 p h) (h 3141) (derived66405 p h) (h 7453) (h 7454) (h 7455) (derived53224 p h) (h 3991) (derived64741 p h) (derived62601 p h) (h 3279) (h 6633) (h 8816) (h 8552) (derived66370 p h) (derived66446 p h) (derived66431 p h) (h 3293) (h 8821) (h 8822) (h 8557) (derived46172 p h) (derived46116 p h) (h 21328) (h 20121) (h 7418) (h 8144) (h 7823) (derived66354 p h) (derived66404 p h) (derived66384 p h) (h 7413) (h 8138) (h 7827) (derived58648 p h) (h 9038) (derived66458 p h) (h 9044) (derived49902 p h) (h 7840) (derived66385 p h) (h 7846) (derived49693 p h) (h 7292) (derived66347 p h) (h 7298) (derived52653 p h) (h 8776) (derived66444 p h) (h 8782) (derived66742 p h) (h 8540) (derived66430 p h) (h 8534) (derived57122 p h) (h 9108) (derived66460 p h) (h 9100) (h 9102) (derived44831 p h) (derived41334 p h) (h 8928) (h 8615) (derived66452 p h) (derived66436 p h) (h 8934) (h 8609) (derived42566 p h) (derived41331 p h) (h 8664) (h 9727) (derived66439 p h) (derived66484 p h) (h 8670) (h 9721) (derived53296 p h) (derived41327 p h) (h 9791) (h 9797) (derived66485 p h)

theorem derived66744 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4785) ∨ (¬ p 2946) ∨ (¬ p 2963) ∨ (¬ p 4714) ∨ (¬ p 4703) ∨ (¬ p 4903) ∨ (¬ p 2810) ∨ (¬ p 2747) ∨ (¬ p 4619) ∨ (¬ p 4500) :=
  ElevenRUP.step66744 (p 2132) (p 2135) (p 2138) (p 2142) (p 2747) (p 2810) (p 2811) (p 2946) (p 2963) (p 3365) (p 4315) (p 4500) (p 4619) (p 4703) (p 4704) (p 4714) (p 4785) (p 4903) (p 5048) (p 5050) (p 5051) (h 7591) (h 7804) (h 7805) (derived66743 p h) (h 20425) (h 2408) (h 8456) (derived66325 p h) (derived66427 p h) (h 2422) (h 8460) (derived48008 p h)

theorem derived66749 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2440) ∨ (¬ p 3016) ∨ (¬ p 2553) ∨ (¬ p 3527) ∨ (¬ p 2437) ∨ (¬ p 3644) :=
  ElevenRUP.step66749 (p 2406) (p 2437) (p 2440) (p 2441) (p 2553) (p 2925) (p 2927) (p 2932) (p 2934) (p 3016) (p 3238) (p 3527) (p 3644) (p 4627) (p 4630) (p 4643) (p 4645) (p 4646) (h 28361) (h 3977) (derived66405 p h) (h 3991) (h 3014) (derived46048 p h) (h 7427) (h 7401) (derived66355 p h) (derived66353 p h) (h 7436) (h 7395) (derived48170 p h)

theorem derived66750 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3553) ∨ (¬ p 4111) ∨ (¬ p 4652) ∨ (¬ p 3527) :=
  ElevenRUP.step66750 (p 3030) (p 3032) (p 3036) (p 3038) (p 3527) (p 3548) (p 3553) (p 4111) (p 4652) (h 9053) (h 29105) (derived52473 p h) (h 4184) (h 4198) (derived66416 p h)

theorem derived66760 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 2747) ∨ (¬ p 4191) ∨ (¬ p 3848) ∨ (¬ p 4118) ∨ (¬ p 2996) ∨ (¬ p 4360) ∨ (¬ p 4025) ∨ (¬ p 4278) ∨ (¬ p 3365) ∨ (¬ p 4653) ∨ (¬ p 4749) ∨ (¬ p 4477) ∨ (¬ p 3585) ∨ (¬ p 4732) ∨ (¬ p 3588) :=
  ElevenRUP.step66760 (p 2241) (p 2244) (p 2247) (p 2251) (p 2685) (p 2737) (p 2747) (p 2748) (p 2761) (p 2996) (p 3266) (p 3365) (p 3434) (p 3506) (p 3585) (p 3588) (p 3848) (p 3873) (p 3947) (p 3954) (p 4025) (p 4118) (p 4191) (p 4278) (p 4324) (p 4360) (p 4381) (p 4444) (p 4477) (p 4653) (p 4655) (p 4659) (p 4661) (p 4732) (p 4749) (p 4776) (p 4777) (p 4780) (p 4822) (p 4827) (p 5115) (p 5120) (p 5227) (p 5232) (p 5281) (p 5284) (p 5287) (h 7681) (h 7679) (h 3620) (h 3622) (derived51535 p h) (h 28879) (derived46273 p h) (h 2639) (h 7794) (h 8893) (derived66336 p h) (derived66382 p h) (derived66450 p h) (h 2625) (h 7787) (h 8899) (derived43941 p h) (derived59241 p h) (derived41192 p h) (h 8646) (h 7464) (h 7908) (derived66438 p h) (derived66357 p h) (derived66390 p h) (h 8652) (h 7469) (h 7902) (derived43940 p h) (derived48368 p h) (h 9002) (h 9008) (derived66456 p h)

theorem derived66765 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3742) ∨ (¬ p 2247) ∨ (¬ p 3644) ∨ (¬ p 3527) :=
  ElevenRUP.step66765 (p 2247) (p 2925) (p 2927) (p 2932) (p 2934) (p 3527) (p 3644) (p 3742) (p 4111) (p 4809) (p 4812) (p 4814) (h 28361) (h 3977) (derived66405 p h) (h 3991) (derived43271 p h) (derived62842 p h) (h 7857) (h 7865) (derived66386 p h)

theorem derived66767 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3389) ∨ (¬ p 4256) ∨ (¬ p 2437) ∨ (¬ p 2936) ∨ (¬ p 4383) ∨ (¬ p 3527) :=
  ElevenRUP.step66767 (p 2341) (p 2437) (p 2473) (p 2476) (p 2480) (p 2481) (p 2936) (p 3389) (p 3527) (p 3540) (p 3960) (p 4256) (p 4383) (p 4586) (p 4589) (p 5196) (p 5200) (p 5203) (h 9914) (derived54756 p h) (h 8816) (h 3079) (derived66446 p h) (derived66359 p h) (h 8824) (h 3091) (derived41713 p h) (derived57274 p h) (h 7298) (h 7291) (derived66347 p h)

theorem derived66768 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3540) ∨ (¬ p 2437) ∨ (¬ p 2727) ∨ (¬ p 2249) :=
  ElevenRUP.step66768 (p 2249) (p 2437) (p 2654) (p 2655) (p 2661) (p 2662) (p 2727) (p 3540) (h 6371) (derived48667 p h) (h 3447) (h 3433) (derived66378 p h)

theorem derived66770 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 3684) ∨ (¬ p 2230) ∨ (¬ p 4752) ∨ (¬ p 3365) :=
  ElevenRUP.step66770 (p 2230) (p 3362) (p 3365) (p 3684) (p 3759) (p 4726) (p 4728) (p 4752) (h 19839) (derived41082 p h) (h 7663) (h 7669) (derived66373 p h)

theorem derived66771 (p : Nat → Prop) (h : Inputs p) :
    (p 3016) ∨ (¬ p 3097) ∨ (¬ p 2573) ∨ (¬ p 3083) ∨ (¬ p 4186) ∨ (¬ p 2437) :=
  ElevenRUP.step66771 (p 2437) (p 2573) (p 3016) (p 3083) (p 3097) (p 3573) (p 3574) (p 3581) (p 4186) (p 4710) (p 4971) (p 4974) (p 5875) (p 5876) (h 8280) (h 36597) (derived66415 p h) (h 32074) (h 8274) (h 12242) (derived46891 p h) (derived66533 p h) (h 12246)

theorem derived66773 (p : Nat → Prop) (h : Inputs p) :
    (p 3425) ∨ (¬ p 2138) ∨ (¬ p 4235) ∨ (¬ p 3367) ∨ (¬ p 3055) :=
  ElevenRUP.step66773 (p 2138) (p 3055) (p 3367) (p 3425) (p 3471) (p 4136) (p 4235) (p 4344) (p 4893) (p 4896) (p 5256) (p 5259) (h 8945) (h 19003) (derived66453 p h) (h 8066) (h 8951) (derived66400 p h) (derived46228 p h) (h 8072)

theorem derived66777 (p : Nat → Prop) (h : Inputs p) :
    (¬ p 4347) ∨ (¬ p 4505) ∨ (¬ p 4520) ∨ (¬ p 2191) ∨ (¬ p 3646) :=
  ElevenRUP.step66777 (p 2191) (p 2192) (p 3369) (p 3555) (p 3646) (p 3989) (p 4173) (p 4347) (p 4505) (p 4506) (p 4511) (p 4515) (p 4520) (h 7073) (h 7072) (h 7107) (h 7105) (derived45034 p h) (derived44977 p h) (h 7096) (h 7090) (derived66332 p h)

end ElevenLogic
