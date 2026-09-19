import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step65771 (p2367 p4605 : Prop)
    (h65770 : p2367)
    (h7356 : (¬ p2367) ∨ p4605)
    : p4605 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4605) := (fun h => hn h);
    let u1 : p2367 := h65770;
    (Or.elim h7356 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65772 (p4605 p5838 : Prop)
    (h65771 : p4605)
    (h12044 : (¬ p4605) ∨ p5838)
    : p5838 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5838) := (fun h => hn h);
    let u1 : p4605 := h65771;
    (Or.elim h12044 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65773 (p410 p416 p2521 : Prop)
    (h3174 : (¬ p410) ∨ p2521)
    (h3175 : (¬ p416) ∨ p2521)
    (h456 : p410 ∨ p416)
    : p2521 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2521) := (fun h => hn h);
    let u1 : (¬ p410) := (Or.elim h3174 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p416) := (Or.elim h3175 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h456 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65774 (p2521 p2522 : Prop)
    (h65773 : p2521)
    (h3192 : (¬ p2521) ∨ p2522)
    : p2522 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2522) := (fun h => hn h);
    let u1 : p2521 := h65773;
    (Or.elim h3192 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65775 (p2522 p4691 : Prop)
    (h65774 : p2522)
    (h7580 : (¬ p2522) ∨ p4691)
    : p4691 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4691) := (fun h => hn h);
    let u1 : p2522 := h65774;
    (Or.elim h7580 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65776 (p4691 p5868 : Prop)
    (h65775 : p4691)
    (h12220 : (¬ p4691) ∨ p5868)
    : p5868 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5868) := (fun h => hn h);
    let u1 : p4691 := h65775;
    (Or.elim h12220 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65778 (p446 p452 p2556 : Prop)
    (h3237 : (¬ p446) ∨ p2556)
    (h3238 : (¬ p452) ∨ p2556)
    (h495 : p446 ∨ p452)
    : p2556 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2556) := (fun h => hn h);
    let u1 : (¬ p446) := (Or.elim h3237 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p452) := (Or.elim h3238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h495 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65779 (p2556 p2557 : Prop)
    (h65778 : p2556)
    (h3255 : (¬ p2556) ∨ p2557)
    : p2557 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2557) := (fun h => hn h);
    let u1 : p2556 := h65778;
    (Or.elim h3255 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65780 (p2557 p4713 : Prop)
    (h65779 : p2557)
    (h7631 : (¬ p2557) ∨ p4713)
    : p4713 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4713) := (fun h => hn h);
    let u1 : p2557 := h65779;
    (Or.elim h7631 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65781 (p4713 p5877 : Prop)
    (h65780 : p4713)
    (h12272 : (¬ p4713) ∨ p5877)
    : p5877 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5877) := (fun h => hn h);
    let u1 : p4713 := h65780;
    (Or.elim h12272 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65782 (p326 p332 p2420 : Prop)
    (h2974 : (¬ p326) ∨ p2420)
    (h2975 : (¬ p332) ∨ p2420)
    (h365 : p326 ∨ p332)
    : p2420 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2420) := (fun h => hn h);
    let u1 : (¬ p326) := (Or.elim h2974 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p332) := (Or.elim h2975 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h365 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65783 (p2420 p2421 : Prop)
    (h65782 : p2420)
    (h2992 : (¬ p2420) ∨ p2421)
    : p2421 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2421) := (fun h => hn h);
    let u1 : p2420 := h65782;
    (Or.elim h2992 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65784 (p2421 p4642 : Prop)
    (h65783 : p2421)
    (h7442 : (¬ p2421) ∨ p4642)
    : p4642 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4642) := (fun h => hn h);
    let u1 : p2421 := h65783;
    (Or.elim h7442 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65785 (p4642 p5853 : Prop)
    (h65784 : p4642)
    (h12132 : (¬ p4642) ∨ p5853)
    : p5853 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5853) := (fun h => hn h);
    let u1 : p4642 := h65784;
    (Or.elim h12132 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65786 (p2373 p2427 p2459 p2881 p3146 p3266 p4235 p4642 p4643 p4645 : Prop)
    (h65784 : p4642)
    (h51791 : (¬ p2427) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3266))
    (h60656 : (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p4235))
    (h7435 : p2427 ∨ (¬ p4645))
    (h7429 : p4235 ∨ (¬ p4643))
    (h7441 : (¬ p4642) ∨ p4643 ∨ p4645)
    : (¬ p3266) ∨ (¬ p2881) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4642 := h65784;
    let u6 : (¬ p2427) := (Or.elim h51791 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0))))))));
    let u7 : (¬ p4235) := (Or.elim h60656 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => r2))))));
    let u8 : (¬ p4645) := (Or.elim h7435 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    let u9 : (¬ p4643) := (Or.elim h7429 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    (Or.elim h7441 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (False.elim (u8 r1)))))))

theorem step65788 (p2177 p2881 p4275 p4553 p4554 p4557 p4559 : Prop)
    (h65724 : p4553)
    (h7210 : (¬ p4557) ∨ p4559)
    (h46823 : (¬ p2177) ∨ p4559)
    (h7214 : (¬ p4553) ∨ p4554 ∨ p4557)
    (h6838 : p2177 ∨ (¬ p2881) ∨ (¬ p4275))
    (h7201 : p4275 ∨ (¬ p4554))
    : p4559 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4559) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4553 := h65724;
    let u3 : (¬ p4557) := (Or.elim h7210 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p2177) := (Or.elim h46823 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4554 := (Or.elim h7214 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u3 r1))))));
    let u6 : (¬ p4275) := (Or.elim h6838 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h7201 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step65789 (p86 p92 p2180 : Prop)
    (h2498 : (¬ p86) ∨ p2180)
    (h2499 : (¬ p92) ∨ p2180)
    (h105 : p86 ∨ p92)
    : p2180 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2180) := (fun h => hn h);
    let u1 : (¬ p86) := (Or.elim h2498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p92) := (Or.elim h2499 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h105 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65790 (p2180 p2181 : Prop)
    (h65789 : p2180)
    (h2516 : (¬ p2180) ∨ p2181)
    : p2181 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2181) := (fun h => hn h);
    let u1 : p2180 := h65789;
    (Or.elim h2516 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65791 (p2181 p4504 : Prop)
    (h65790 : p2181)
    (h7086 : (¬ p2181) ∨ p4504)
    : p4504 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4504) := (fun h => hn h);
    let u1 : p2181 := h65790;
    (Or.elim h7086 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65792 (p4504 p5799 : Prop)
    (h65791 : p4504)
    (h11815 : (¬ p4504) ∨ p5799)
    : p5799 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5799) := (fun h => hn h);
    let u1 : p4504 := h65791;
    (Or.elim h11815 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65793 (p710 p716 p2843 : Prop)
    (h3812 : (¬ p710) ∨ p2843)
    (h3813 : (¬ p716) ∨ p2843)
    (h781 : p710 ∨ p716)
    : p2843 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2843) := (fun h => hn h);
    let u1 : (¬ p710) := (Or.elim h3812 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p716) := (Or.elim h3813 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h781 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65794 (p2843 p2844 : Prop)
    (h65793 : p2843)
    (h3830 : (¬ p2843) ∨ p2844)
    : p2844 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2844) := (fun h => hn h);
    let u1 : p2843 := h65793;
    (Or.elim h3830 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65795 (p2844 p4879 : Prop)
    (h65794 : p2844)
    (h8047 : (¬ p2844) ∨ p4879)
    : p4879 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4879) := (fun h => hn h);
    let u1 : p2844 := h65794;
    (Or.elim h8047 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65796 (p4879 p5931 : Prop)
    (h65795 : p4879)
    (h12591 : (¬ p4879) ∨ p5931)
    : p5931 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5931) := (fun h => hn h);
    let u1 : p4879 := h65795;
    (Or.elim h12591 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65798 (p302 p308 p2399 : Prop)
    (h2932 : (¬ p302) ∨ p2399)
    (h2933 : (¬ p308) ∨ p2399)
    (h339 : p302 ∨ p308)
    : p2399 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2399) := (fun h => hn h);
    let u1 : (¬ p302) := (Or.elim h2932 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p308) := (Or.elim h2933 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h339 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65799 (p2399 p2400 : Prop)
    (h65798 : p2399)
    (h2950 : (¬ p2399) ∨ p2400)
    : p2400 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2400) := (fun h => hn h);
    let u1 : p2399 := h65798;
    (Or.elim h2950 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65800 (p2400 p4626 : Prop)
    (h65799 : p2400)
    (h7408 : (¬ p2400) ∨ p4626)
    : p4626 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4626) := (fun h => hn h);
    let u1 : p2400 := h65799;
    (Or.elim h7408 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65801 (p4626 p5847 : Prop)
    (h65800 : p4626)
    (h12097 : (¬ p4626) ∨ p5847)
    : p5847 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5847) := (fun h => hn h);
    let u1 : p4626 := h65800;
    (Or.elim h12097 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65802 (p98 p104 p2193 : Prop)
    (h2519 : (¬ p98) ∨ p2193)
    (h2520 : (¬ p104) ∨ p2193)
    (h118 : p98 ∨ p104)
    : p2193 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2193) := (fun h => hn h);
    let u1 : (¬ p98) := (Or.elim h2519 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p104) := (Or.elim h2520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h118 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65803 (p2193 p2194 : Prop)
    (h65802 : p2193)
    (h2537 : (¬ p2193) ∨ p2194)
    : p2194 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2194) := (fun h => hn h);
    let u1 : p2193 := h65802;
    (Or.elim h2537 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65804 (p2194 p4510 : Prop)
    (h65803 : p2194)
    (h7103 : (¬ p2194) ∨ p4510)
    : p4510 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4510) := (fun h => hn h);
    let u1 : p2194 := h65803;
    (Or.elim h7103 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65805 (p4510 p5802 : Prop)
    (h65804 : p4510)
    (h11832 : (¬ p4510) ∨ p5802)
    : p5802 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5802) := (fun h => hn h);
    let u1 : p4510 := h65804;
    (Or.elim h11832 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65807 (p2138 p2589 p2870 p2891 p3366 p3371 p3905 p4034 p4210 p4235 p4244 p4418 p4731 p4732 p4734 p4735 p4872 p4873 p4876 : Prop)
    (h65699 : p4872)
    (h65532 : p4731)
    (h9153 : (¬ p2870) ∨ (¬ p4244))
    (h6814 : p2870 ∨ (¬ p2891) ∨ (¬ p4418))
    (h20333 : (¬ p2891) ∨ (¬ p4034) ∨ (¬ p4235))
    (h8016 : p4418 ∨ (¬ p4873))
    (h40558 : p4034 ∨ p4210)
    (h8029 : (¬ p4872) ∨ p4873 ∨ p4876)
    (h8022 : p3371 ∨ (¬ p4876))
    (h50628 : (¬ p2138) ∨ (¬ p2891) ∨ (¬ p3371) ∨ (¬ p4244) ∨ (¬ p4734))
    (h20629 : (¬ p2589) ∨ (¬ p3366) ∨ (¬ p3371) ∨ (¬ p3905) ∨ (¬ p4210))
    (h7683 : (¬ p4732) ∨ p4734)
    (h7685 : p3366 ∨ (¬ p4735))
    (h7693 : (¬ p4731) ∨ p4732 ∨ p4735)
    : (¬ p2891) ∨ (¬ p2589) ∨ (¬ p3905) ∨ (¬ p4244) ∨ (¬ p2138) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4872 := h65699;
    let u7 : p4731 := h65532;
    let u8 : (¬ p2870) := (Or.elim h9153 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u9 : (¬ p4418) := (Or.elim h6814 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => r1))));
    let u10 : (¬ p4034) := (Or.elim h20333 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u5))))));
    let u11 : (¬ p4873) := (Or.elim h8016 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u12 : p4210 := (Or.elim h40558 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : p4876 := (Or.elim h8029 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => r1))));
    let u14 : p3371 := (Or.elim h8022 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u15 : (¬ p4734) := (Or.elim h50628 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    let u16 : (¬ p3366) := (Or.elim h20629 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u12))))))))));
    let u17 : (¬ p4732) := (Or.elim h7683 (fun q0 => q0) (fun r0 => (False.elim (u15 r0))));
    let u18 : (¬ p4735) := (Or.elim h7685 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    (Or.elim h7693 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u17 q1))) (fun r1 => (False.elim (u18 r1)))))))

theorem step65808 (p674 p680 p2812 : Prop)
    (h3750 : (¬ p674) ∨ p2812)
    (h3751 : (¬ p680) ∨ p2812)
    (h742 : p674 ∨ p680)
    : p2812 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2812) := (fun h => hn h);
    let u1 : (¬ p674) := (Or.elim h3750 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p680) := (Or.elim h3751 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h742 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65809 (p2812 p2813 : Prop)
    (h65808 : p2812)
    (h3768 : (¬ p2812) ∨ p2813)
    : p2813 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2813) := (fun h => hn h);
    let u1 : p2812 := h65808;
    (Or.elim h3768 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65810 (p2813 p4855 : Prop)
    (h65809 : p2813)
    (h7996 : (¬ p2813) ∨ p4855)
    : p4855 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4855) := (fun h => hn h);
    let u1 : p2813 := h65809;
    (Or.elim h7996 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65811 (p4855 p5922 : Prop)
    (h65810 : p4855)
    (h12539 : (¬ p4855) ∨ p5922)
    : p5922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5922) := (fun h => hn h);
    let u1 : p4855 := h65810;
    (Or.elim h12539 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65812 (p1070 p1076 p3215 : Prop)
    (h4549 : (¬ p1070) ∨ p3215)
    (h4550 : (¬ p1076) ∨ p3215)
    (h1171 : p1070 ∨ p1076)
    : p3215 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3215) := (fun h => hn h);
    let u1 : (¬ p1070) := (Or.elim h4549 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1076) := (Or.elim h4550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1171 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65813 (p3215 p3216 : Prop)
    (h65812 : p3215)
    (h4567 : (¬ p3215) ∨ p3216)
    : p3216 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3216) := (fun h => hn h);
    let u1 : p3215 := h65812;
    (Or.elim h4567 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65814 (p3216 p5095 : Prop)
    (h65813 : p3216)
    (h8589 : (¬ p3216) ∨ p5095)
    : p5095 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5095) := (fun h => hn h);
    let u1 : p3216 := h65813;
    (Or.elim h8589 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65816 (p2138 p2373 p2563 p2619 p3097 p3694 p3758 p3988 p4110 p4235 p4405 p4441 p4504 p4505 p4508 p4713 p4714 p4716 p5886 p5887 p5888 : Prop)
    (h65780 : p4713)
    (h65791 : p4504)
    (h65618 : p5886)
    (h43029 : (¬ p2138) ∨ (¬ p2563) ∨ (¬ p3758) ∨ (¬ p4235))
    (h7624 : p2563 ∨ (¬ p4716))
    (h5920 : (¬ p2373) ∨ p2563 ∨ (¬ p3988))
    (h7630 : (¬ p4713) ∨ p4714 ∨ p4716)
    (h7071 : p3988 ∨ (¬ p4505))
    (h7618 : p4110 ∨ (¬ p4714))
    (h7085 : (¬ p4504) ∨ p4505 ∨ p4508)
    (h43959 : (¬ p2138) ∨ (¬ p2373) ∨ (¬ p3694) ∨ (¬ p4110))
    (h7077 : p4441 ∨ (¬ p4508))
    (h12309 : p3694 ∨ p5887)
    (h52622 : (¬ p2619) ∨ (¬ p3097) ∨ (¬ p3758) ∨ (¬ p4405) ∨ (¬ p4441))
    (h12322 : (¬ p5886) ∨ (¬ p5887) ∨ (¬ p5888))
    (h12316 : p2619 ∨ p5888)
    : (¬ p3758) ∨ (¬ p4405) ∨ (¬ p2373) ∨ (¬ p3097) ∨ (¬ p2138) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3758 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4713 := h65780;
    let u7 : p4504 := h65791;
    let u8 : p5886 := h65618;
    let u9 : (¬ p2563) := (Or.elim h43029 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5))))))));
    let u10 : (¬ p4716) := (Or.elim h7624 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u11 : (¬ p3988) := (Or.elim h5920 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => r1))));
    let u12 : p4714 := (Or.elim h7630 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u10 r1))))));
    let u13 : (¬ p4505) := (Or.elim h7071 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    let u14 : p4110 := (Or.elim h7618 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u15 : p4508 := (Or.elim h7085 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u13 q1))) (fun r1 => r1))));
    let u16 : (¬ p3694) := (Or.elim h43959 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u14))))))));
    let u17 : p4441 := (Or.elim h7077 (fun q0 => q0) (fun r0 => (False.elim (r0 u15))));
    let u18 : p5887 := (Or.elim h12309 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    let u19 : (¬ p2619) := (Or.elim h52622 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u17))))))))));
    let u20 : (¬ p5888) := (Or.elim h12322 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u18))) (fun r1 => r1))));
    (Or.elim h12316 (fun q0 => (False.elim (u19 q0))) (fun r0 => (False.elim (u20 r0)))))

theorem step65818 (p386 p392 p2486 : Prop)
    (h3105 : (¬ p386) ∨ p2486)
    (h3106 : (¬ p392) ∨ p2486)
    (h430 : p386 ∨ p392)
    : p2486 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2486) := (fun h => hn h);
    let u1 : (¬ p386) := (Or.elim h3105 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p392) := (Or.elim h3106 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h430 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65819 (p2486 p2487 : Prop)
    (h65818 : p2486)
    (h3123 : (¬ p2486) ∨ p2487)
    : p2487 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2487) := (fun h => hn h);
    let u1 : p2486 := h65818;
    (Or.elim h3123 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65820 (p2487 p4676 : Prop)
    (h65819 : p2487)
    (h7525 : (¬ p2487) ∨ p4676)
    : p4676 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4676) := (fun h => hn h);
    let u1 : p2487 := h65819;
    (Or.elim h7525 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65821 (p218 p224 p2324 : Prop)
    (h2784 : (¬ p218) ∨ p2324)
    (h2785 : (¬ p224) ∨ p2324)
    (h248 : p218 ∨ p224)
    : p2324 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2324) := (fun h => hn h);
    let u1 : (¬ p218) := (Or.elim h2784 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p224) := (Or.elim h2785 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h248 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65822 (p2324 p2325 : Prop)
    (h65821 : p2324)
    (h2802 : (¬ p2324) ∨ p2325)
    : p2325 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2325) := (fun h => hn h);
    let u1 : p2324 := h65821;
    (Or.elim h2802 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65823 (p2325 p4578 : Prop)
    (h65822 : p2325)
    (h7288 : (¬ p2325) ∨ p4578)
    : p4578 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4578) := (fun h => hn h);
    let u1 : p2325 := h65822;
    (Or.elim h7288 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65824 (p4578 p5826 : Prop)
    (h65823 : p4578)
    (h11972 : (¬ p4578) ∨ p5826)
    : p5826 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5826) := (fun h => hn h);
    let u1 : p4578 := h65823;
    (Or.elim h11972 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65825 (p650 p656 p2790 : Prop)
    (h3709 : (¬ p650) ∨ p2790)
    (h3710 : (¬ p656) ∨ p2790)
    (h716 : p650 ∨ p656)
    : p2790 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2790) := (fun h => hn h);
    let u1 : (¬ p650) := (Or.elim h3709 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p656) := (Or.elim h3710 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h716 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65826 (p2790 p2791 : Prop)
    (h65825 : p2790)
    (h3727 : (¬ p2790) ∨ p2791)
    : p2791 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2791) := (fun h => hn h);
    let u1 : p2790 := h65825;
    (Or.elim h3727 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65827 (p2791 p4839 : Prop)
    (h65826 : p2791)
    (h7960 : (¬ p2791) ∨ p4839)
    : p4839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4839) := (fun h => hn h);
    let u1 : p2791 := h65826;
    (Or.elim h7960 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65828 (p4839 p5916 : Prop)
    (h65827 : p4839)
    (h12500 : (¬ p4839) ∨ p5916)
    : p5916 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5916) := (fun h => hn h);
    let u1 : p4839 := h65827;
    (Or.elim h12500 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65829 (p602 p608 p2720 : Prop)
    (h3566 : (¬ p602) ∨ p2720)
    (h3567 : (¬ p608) ∨ p2720)
    (h664 : p602 ∨ p608)
    : p2720 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2720) := (fun h => hn h);
    let u1 : (¬ p602) := (Or.elim h3566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p608) := (Or.elim h3567 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h664 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65830 (p2720 p2721 : Prop)
    (h65829 : p2720)
    (h3584 : (¬ p2720) ∨ p2721)
    : p2721 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2721) := (fun h => hn h);
    let u1 : p2720 := h65829;
    (Or.elim h3584 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65831 (p2721 p4808 : Prop)
    (h65830 : p2721)
    (h7870 : (¬ p2721) ∨ p4808)
    : p4808 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4808) := (fun h => hn h);
    let u1 : p2721 := h65830;
    (Or.elim h7870 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65832 (p4808 p5910 : Prop)
    (h65831 : p4808)
    (h12462 : (¬ p4808) ∨ p5910)
    : p5910 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5910) := (fun h => hn h);
    let u1 : p4808 := h65831;
    (Or.elim h12462 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65834 (p530 p536 p2644 : Prop)
    (h3413 : (¬ p530) ∨ p2644)
    (h3414 : (¬ p536) ∨ p2644)
    (h586 : p530 ∨ p536)
    : p2644 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2644) := (fun h => hn h);
    let u1 : (¬ p530) := (Or.elim h3413 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p536) := (Or.elim h3414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h586 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65835 (p2644 p2645 : Prop)
    (h65834 : p2644)
    (h3431 : (¬ p2644) ∨ p2645)
    : p2645 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2645) := (fun h => hn h);
    let u1 : p2644 := h65834;
    (Or.elim h3431 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65836 (p2645 p4762 : Prop)
    (h65835 : p2645)
    (h7751 : (¬ p2645) ∨ p4762)
    : p4762 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4762) := (fun h => hn h);
    let u1 : p2645 := h65835;
    (Or.elim h7751 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65839 (p458 p464 p2566 : Prop)
    (h3257 : (¬ p458) ∨ p2566)
    (h3258 : (¬ p464) ∨ p2566)
    (h508 : p458 ∨ p464)
    : p2566 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2566) := (fun h => hn h);
    let u1 : (¬ p458) := (Or.elim h3257 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p464) := (Or.elim h3258 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h508 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65840 (p2566 p2567 : Prop)
    (h65839 : p2566)
    (h3275 : (¬ p2566) ∨ p2567)
    : p2567 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2567) := (fun h => hn h);
    let u1 : p2566 := h65839;
    (Or.elim h3275 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65841 (p2567 p4719 : Prop)
    (h65840 : p2567)
    (h7637 : (¬ p2567) ∨ p4719)
    : p4719 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4719) := (fun h => hn h);
    let u1 : p2567 := h65840;
    (Or.elim h7637 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65842 (p422 p428 p2535 : Prop)
    (h3195 : (¬ p422) ∨ p2535)
    (h3196 : (¬ p428) ∨ p2535)
    (h469 : p422 ∨ p428)
    : p2535 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2535) := (fun h => hn h);
    let u1 : (¬ p422) := (Or.elim h3195 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p428) := (Or.elim h3196 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h469 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65843 (p2535 p2536 : Prop)
    (h65842 : p2535)
    (h3213 : (¬ p2535) ∨ p2536)
    : p2536 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2536) := (fun h => hn h);
    let u1 : p2535 := h65842;
    (Or.elim h3213 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65844 (p2536 p4698 : Prop)
    (h65843 : p2536)
    (h7597 : (¬ p2536) ∨ p4698)
    : p4698 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4698) := (fun h => hn h);
    let u1 : p2536 := h65843;
    (Or.elim h7597 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65845 (p4698 p5871 : Prop)
    (h65844 : p4698)
    (h12237 : (¬ p4698) ∨ p5871)
    : p5871 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5871) := (fun h => hn h);
    let u1 : p4698 := h65844;
    (Or.elim h12237 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65846 (p314 p320 p2410 : Prop)
    (h2954 : (¬ p314) ∨ p2410)
    (h2955 : (¬ p320) ∨ p2410)
    (h352 : p314 ∨ p320)
    : p2410 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2410) := (fun h => hn h);
    let u1 : (¬ p314) := (Or.elim h2954 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p320) := (Or.elim h2955 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h352 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65847 (p2410 p2411 : Prop)
    (h65846 : p2410)
    (h2972 : (¬ p2410) ∨ p2411)
    : p2411 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2411) := (fun h => hn h);
    let u1 : p2410 := h65846;
    (Or.elim h2972 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65848 (p2411 p4633 : Prop)
    (h65847 : p2411)
    (h7425 : (¬ p2411) ∨ p4633)
    : p4633 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4633) := (fun h => hn h);
    let u1 : p2411 := h65847;
    (Or.elim h7425 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65849 (p4633 p5850 : Prop)
    (h65848 : p4633)
    (h12115 : (¬ p4633) ∨ p5850)
    : p5850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5850) := (fun h => hn h);
    let u1 : p4633 := h65848;
    (Or.elim h12115 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65851 (p434 p440 p2546 : Prop)
    (h3217 : (¬ p434) ∨ p2546)
    (h3218 : (¬ p440) ∨ p2546)
    (h482 : p434 ∨ p440)
    : p2546 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2546) := (fun h => hn h);
    let u1 : (¬ p434) := (Or.elim h3217 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p440) := (Or.elim h3218 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h482 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65852 (p2546 p2547 : Prop)
    (h65851 : p2546)
    (h3235 : (¬ p2546) ∨ p2547)
    : p2547 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2547) := (fun h => hn h);
    let u1 : p2546 := h65851;
    (Or.elim h3235 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65853 (p2547 p4706 : Prop)
    (h65852 : p2547)
    (h7614 : (¬ p2547) ∨ p4706)
    : p4706 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4706) := (fun h => hn h);
    let u1 : p2547 := h65852;
    (Or.elim h7614 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65854 (p4706 p5874 : Prop)
    (h65853 : p4706)
    (h12255 : (¬ p4706) ∨ p5874)
    : p5874 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5874) := (fun h => hn h);
    let u1 : p4706 := h65853;
    (Or.elim h12255 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65856 (p2230 p2246 p2331 p2542 p2651 p2654 p2656 p2661 p2727 p2963 p4154 p4245 p4319 p4389 p4578 p4579 p4582 p4715 p4755 p4762 : Prop)
    (h65823 : p4578)
    (h65836 : p4762)
    (h7731 : p4245 ∨ (¬ p4755))
    (h7732 : p4319 ∨ (¬ p4755))
    (h7733 : p4154 ∨ (¬ p4755))
    (h15125 : (¬ p2246) ∨ (¬ p2331) ∨ (¬ p4245) ∨ (¬ p4319))
    (h51526 : (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p4154) ∨ (¬ p4389) ∨ (¬ p4715))
    (h7281 : p2331 ∨ (¬ p4582))
    (h3434 : (¬ p2654) ∨ p2656)
    (h7287 : (¬ p4578) ∨ p4579 ∨ p4582)
    (h7750 : p2654 ∨ p2661 ∨ (¬ p4762))
    (h7275 : p2963 ∨ (¬ p4579))
    (h3449 : p2651 ∨ (¬ p2661))
    (h49230 : (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p4389) ∨ (¬ p4715))
    : (¬ p4755) ∨ (¬ p2542) ∨ (¬ p2246) ∨ (¬ p2727) ∨ (¬ p4389) ∨ (¬ p2230) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4578 := h65823;
    let u8 : p4762 := h65836;
    let u9 : p4245 := (Or.elim h7731 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u10 : p4319 := (Or.elim h7732 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u11 : p4154 := (Or.elim h7733 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u12 : (¬ p2331) := (Or.elim h15125 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (False.elim (r2 u10))))))));
    let u13 : (¬ p2656) := (Or.elim h51526 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u6))))))))))));
    let u14 : (¬ p4582) := (Or.elim h7281 (fun q0 => (False.elim (u12 q0))) (fun r0 => r0));
    let u15 : (¬ p2654) := (Or.elim h3434 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u16 : p4579 := (Or.elim h7287 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u14 r1))))));
    let u17 : p2661 := (Or.elim h7750 (fun q0 => (False.elim (u15 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u8))))));
    let u18 : p2963 := (Or.elim h7275 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    let u19 : p2651 := (Or.elim h3449 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    (Or.elim h49230 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u19))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u18))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step65857 (p542 p548 p2669 : Prop)
    (h3462 : (¬ p542) ∨ p2669)
    (h3463 : (¬ p548) ∨ p2669)
    (h599 : p542 ∨ p548)
    : p2669 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2669) := (fun h => hn h);
    let u1 : (¬ p542) := (Or.elim h3462 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p548) := (Or.elim h3463 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h599 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65858 (p2669 p2670 : Prop)
    (h65857 : p2669)
    (h3480 : (¬ p2669) ∨ p2670)
    : p2670 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2670) := (fun h => hn h);
    let u1 : p2669 := h65857;
    (Or.elim h3480 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65859 (p2670 p4767 : Prop)
    (h65858 : p2670)
    (h7784 : (¬ p2670) ∨ p4767)
    : p4767 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4767) := (fun h => hn h);
    let u1 : p2670 := h65858;
    (Or.elim h7784 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65860 (p4767 p5895 : Prop)
    (h65859 : p4767)
    (h12375 : (¬ p4767) ∨ p5895)
    : p5895 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5895) := (fun h => hn h);
    let u1 : p4767 := h65859;
    (Or.elim h12375 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65863 (p110 p116 p2203 : Prop)
    (h2541 : (¬ p110) ∨ p2203)
    (h2542 : (¬ p116) ∨ p2203)
    (h131 : p110 ∨ p116)
    : p2203 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2203) := (fun h => hn h);
    let u1 : (¬ p110) := (Or.elim h2541 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p116) := (Or.elim h2542 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h131 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65864 (p2203 p2204 : Prop)
    (h65863 : p2203)
    (h2559 : (¬ p2203) ∨ p2204)
    : p2204 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2204) := (fun h => hn h);
    let u1 : p2203 := h65863;
    (Or.elim h2559 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65865 (p2204 p4519 : Prop)
    (h65864 : p2204)
    (h7120 : (¬ p2204) ∨ p4519)
    : p4519 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4519) := (fun h => hn h);
    let u1 : p2204 := h65864;
    (Or.elim h7120 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65866 (p4519 p5805 : Prop)
    (h65865 : p4519)
    (h11850 : (¬ p4519) ∨ p5805)
    : p5805 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5805) := (fun h => hn h);
    let u1 : p4519 := h65865;
    (Or.elim h11850 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65869 (p2230 p2331 p2542 p2630 p2651 p2654 p2656 p2661 p2963 p4195 p4389 p4578 p4579 p4582 p4715 p4762 : Prop)
    (h65836 : p4762)
    (h65823 : p4578)
    (h50312 : (¬ p2230) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p4195) ∨ (¬ p4389) ∨ (¬ p4715))
    (h44438 : (¬ p2331) ∨ (¬ p2542) ∨ (¬ p2630) ∨ (¬ p4195))
    (h3434 : (¬ p2654) ∨ p2656)
    (h7281 : p2331 ∨ (¬ p4582))
    (h7750 : p2654 ∨ p2661 ∨ (¬ p4762))
    (h7287 : (¬ p4578) ∨ p4579 ∨ p4582)
    (h3449 : p2651 ∨ (¬ p2661))
    (h7275 : p2963 ∨ (¬ p4579))
    (h49230 : (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p4389) ∨ (¬ p4715))
    : (¬ p4195) ∨ (¬ p2230) ∨ (¬ p4389) ∨ (¬ p2630) ∨ (¬ p2542) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4195 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4762 := h65836;
    let u7 : p4578 := h65823;
    let u8 : (¬ p2656) := (Or.elim h50312 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5))))))))))));
    let u9 : (¬ p2331) := (Or.elim h44438 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0))))))));
    let u10 : (¬ p2654) := (Or.elim h3434 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u11 : (¬ p4582) := (Or.elim h7281 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u12 : p2661 := (Or.elim h7750 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u6))))));
    let u13 : p4579 := (Or.elim h7287 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u11 r1))))));
    let u14 : p2651 := (Or.elim h3449 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u15 : p2963 := (Or.elim h7275 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    (Or.elim h49230 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step65870 (p2630 p2657 p2737 p2740 p2743 p2747 p3055 p3366 p3367 p3683 p4236 p4731 p4732 p4734 p4735 p4751 p4787 p4815 : Prop)
    (h65613 : p4815)
    (h65532 : p4731)
    (h7719 : p3683 ∨ (¬ p4751))
    (h22900 : (¬ p2657) ∨ p3055 ∨ (¬ p3683) ∨ (¬ p4236))
    (h7721 : p2630 ∨ (¬ p4751))
    (h48009 : (¬ p2657) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p4787))
    (h4835 : (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3367))
    (h3608 : (¬ p2740) ∨ p2743)
    (h7685 : p3366 ∨ (¬ p4735))
    (h7875 : p2740 ∨ p2747 ∨ (¬ p4815))
    (h7693 : (¬ p4731) ∨ p4732 ∨ p4735)
    (h3622 : p2737 ∨ (¬ p2747))
    (h7683 : (¬ p4732) ∨ p4734)
    (h42791 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2737) ∨ (¬ p4236) ∨ (¬ p4734))
    : (¬ p3367) ∨ (¬ p4787) ∨ (¬ p4236) ∨ (¬ p2657) ∨ (¬ p4751) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4815 := h65613;
    let u6 : p4731 := h65532;
    let u7 : p3683 := (Or.elim h7719 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u8 : p3055 := (Or.elim h22900 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u2))))))));
    let u9 : p2630 := (Or.elim h7721 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u10 : (¬ p2743) := (Or.elim h48009 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u1))))))))));
    let u11 : (¬ p3366) := (Or.elim h4835 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u0))))));
    let u12 : (¬ p2740) := (Or.elim h3608 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u13 : (¬ p4735) := (Or.elim h7685 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    let u14 : p2747 := (Or.elim h7875 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u5))))));
    let u15 : p4732 := (Or.elim h7693 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u13 r1))))));
    let u16 : p2737 := (Or.elim h3622 (fun q0 => q0) (fun r0 => (False.elim (r0 u14))));
    let u17 : p4734 := (Or.elim h7683 (fun q0 => (False.elim (q0 u15))) (fun r0 => r0));
    (Or.elim h42791 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u16))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u17)))))))))))

theorem step65874 (p2230 p2406 p2498 p3238 p3379 p3591 p4079 p4257 p4626 p4627 p4630 p4715 p4866 p5192 : Prop)
    (h65800 : p4626)
    (h8804 : p4079 ∨ (¬ p5192))
    (h8805 : p3379 ∨ (¬ p5192))
    (h49538 : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3591) ∨ (¬ p4079) ∨ (¬ p4257) ∨ (¬ p4866))
    (h50238 : (¬ p2406) ∨ (¬ p2498) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p4715))
    (h7395 : p3238 ∨ (¬ p4627))
    (h7401 : p2406 ∨ (¬ p4630))
    (h7407 : (¬ p4626) ∨ p4627 ∨ p4630)
    : (¬ p5192) ∨ (¬ p2498) ∨ (¬ p4257) ∨ (¬ p4866) ∨ (¬ p3591) ∨ (¬ p2230) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4626 := h65800;
    let u8 : p4079 := (Or.elim h8804 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u9 : p3379 := (Or.elim h8805 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u10 : (¬ p3238) := (Or.elim h49538 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3))))))))))));
    let u11 : (¬ p2406) := (Or.elim h50238 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6))))))))));
    let u12 : (¬ p4627) := (Or.elim h7395 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : (¬ p4630) := (Or.elim h7401 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    (Or.elim h7407 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u12 q1))) (fun r1 => (False.elim (u13 r1)))))))

theorem step65879 (p338 p344 p2430 : Prop)
    (h2994 : (¬ p338) ∨ p2430)
    (h2995 : (¬ p344) ∨ p2430)
    (h378 : p338 ∨ p344)
    : p2430 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2430) := (fun h => hn h);
    let u1 : (¬ p338) := (Or.elim h2994 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p344) := (Or.elim h2995 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h378 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65880 (p2430 p2431 : Prop)
    (h65879 : p2430)
    (h3012 : (¬ p2430) ∨ p2431)
    : p2431 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2431) := (fun h => hn h);
    let u1 : p2430 := h65879;
    (Or.elim h3012 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65881 (p2431 p4648 : Prop)
    (h65880 : p2431)
    (h7460 : (¬ p2431) ∨ p4648)
    : p4648 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4648) := (fun h => hn h);
    let u1 : p2431 := h65880;
    (Or.elim h7460 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65882 (p4648 p5856 : Prop)
    (h65881 : p4648)
    (h12149 : (¬ p4648) ∨ p5856)
    : p5856 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5856) := (fun h => hn h);
    let u1 : p4648 := h65881;
    (Or.elim h12149 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65885 (p194 p200 p2288 : Prop)
    (h2713 : (¬ p194) ∨ p2288)
    (h2714 : (¬ p200) ∨ p2288)
    (h222 : p194 ∨ p200)
    : p2288 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2288) := (fun h => hn h);
    let u1 : (¬ p194) := (Or.elim h2713 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p200) := (Or.elim h2714 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h222 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65886 (p2288 p2289 : Prop)
    (h65885 : p2288)
    (h2731 : (¬ p2288) ∨ p2289)
    : p2289 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2289) := (fun h => hn h);
    let u1 : p2288 := h65885;
    (Or.elim h2731 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65887 (p2289 p4567 : Prop)
    (h65886 : p2289)
    (h7250 : (¬ p2289) ∨ p4567)
    : p4567 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4567) := (fun h => hn h);
    let u1 : p2289 := h65886;
    (Or.elim h7250 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65888 (p4567 p5823 : Prop)
    (h65887 : p4567)
    (h11955 : (¬ p4567) ∨ p5823)
    : p5823 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5823) := (fun h => hn h);
    let u1 : p4567 := h65887;
    (Or.elim h11955 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65889 (p374 p380 p2463 : Prop)
    (h3057 : (¬ p374) ∨ p2463)
    (h3058 : (¬ p380) ∨ p2463)
    (h417 : p374 ∨ p380)
    : p2463 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2463) := (fun h => hn h);
    let u1 : (¬ p374) := (Or.elim h3057 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p380) := (Or.elim h3058 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h417 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65890 (p2463 p2464 : Prop)
    (h65889 : p2463)
    (h3075 : (¬ p2463) ∨ p2464)
    : p2464 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2464) := (fun h => hn h);
    let u1 : p2463 := h65889;
    (Or.elim h3075 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65891 (p2464 p4670 : Prop)
    (h65890 : p2464)
    (h7499 : (¬ p2464) ∨ p4670)
    : p4670 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4670) := (fun h => hn h);
    let u1 : p2464 := h65890;
    (Or.elim h7499 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65893 (p242 p248 p2345 : Prop)
    (h2827 : (¬ p242) ∨ p2345)
    (h2828 : (¬ p248) ∨ p2345)
    (h274 : p242 ∨ p248)
    : p2345 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2345) := (fun h => hn h);
    let u1 : (¬ p242) := (Or.elim h2827 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p248) := (Or.elim h2828 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h274 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65894 (p2345 p2346 : Prop)
    (h65893 : p2345)
    (h2845 : (¬ p2345) ∨ p2346)
    : p2346 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2346) := (fun h => hn h);
    let u1 : p2345 := h65893;
    (Or.elim h2845 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65895 (p2346 p4593 : Prop)
    (h65894 : p2346)
    (h7322 : (¬ p2346) ∨ p4593)
    : p4593 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4593) := (fun h => hn h);
    let u1 : p2346 := h65894;
    (Or.elim h7322 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65896 (p4593 p5832 : Prop)
    (h65895 : p4593)
    (h12006 : (¬ p4593) ∨ p5832)
    : p5832 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5832) := (fun h => hn h);
    let u1 : p4593 := h65895;
    (Or.elim h12006 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65900 (p794 p800 p2915 : Prop)
    (h3956 : (¬ p794) ∨ p2915)
    (h3957 : (¬ p800) ∨ p2915)
    (h872 : p794 ∨ p800)
    : p2915 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2915) := (fun h => hn h);
    let u1 : (¬ p794) := (Or.elim h3956 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p800) := (Or.elim h3957 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h872 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65901 (p2915 p2916 : Prop)
    (h65900 : p2915)
    (h3974 : (¬ p2915) ∨ p2916)
    : p2916 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2916) := (fun h => hn h);
    let u1 : p2915 := h65900;
    (Or.elim h3974 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65902 (p2916 p4925 : Prop)
    (h65901 : p2916)
    (h8156 : (¬ p2916) ∨ p4925)
    : p4925 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4925) := (fun h => hn h);
    let u1 : p2916 := h65901;
    (Or.elim h8156 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65906 (p2579 p2630 p2654 p2655 p2659 p2797 p2810 p3016 p3984 p4747 p4748 p4751 p4787 : Prop)
    (h65606 : p4747)
    (h3437 : (¬ p2654) ∨ p2659)
    (h3433 : (¬ p2654) ∨ p2655)
    (h58281 : (¬ p2579) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p3016) ∨ (¬ p4787))
    (h41612 : (¬ p2579) ∨ (¬ p2659) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3984))
    (h7721 : p2630 ∨ (¬ p4751))
    (h7715 : p2810 ∨ (¬ p4748))
    (h7727 : (¬ p4747) ∨ p4748 ∨ p4751)
    : (¬ p2579) ∨ (¬ p2797) ∨ (¬ p3016) ∨ (¬ p3984) ∨ (¬ p4787) ∨ (¬ p2654) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4747 := h65606;
    let u7 : p2659 := (Or.elim h3437 (fun q0 => (False.elim (q0 u5))) (fun r0 => r0));
    let u8 : p2655 := (Or.elim h3433 (fun q0 => (False.elim (q0 u5))) (fun r0 => r0));
    let u9 : (¬ p2630) := (Or.elim h58281 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    let u10 : (¬ p2810) := (Or.elim h41612 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    let u11 : (¬ p4751) := (Or.elim h7721 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u12 : (¬ p4748) := (Or.elim h7715 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    (Or.elim h7727 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u12 q1))) (fun r1 => (False.elim (u11 r1)))))))

theorem step65907 (p2307 p2310 p2312 p2317 p2318 p2319 p2657 p3567 p3568 p3987 p4573 p4578 p4579 p4582 p4975 : Prop)
    (h65754 : p4573)
    (h65823 : p4578)
    (h2755 : (¬ p2310) ∨ p2312)
    (h5196 : p2312 ∨ p2318)
    (h7254 : p2310 ∨ p2317 ∨ (¬ p4573))
    (h2769 : (¬ p2317) ∨ p2319)
    (h2770 : p2307 ∨ (¬ p2317))
    (h5195 : (¬ p2318) ∨ (¬ p2319) ∨ (¬ p3567) ∨ (¬ p3568))
    (h49439 : (¬ p2307) ∨ (¬ p2657) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4975))
    (h7274 : p3567 ∨ (¬ p4579))
    (h7280 : p3987 ∨ (¬ p4582))
    (h7287 : (¬ p4578) ∨ p4579 ∨ p4582)
    : p2312 ∨ (¬ p4975) ∨ (¬ p3568) ∨ (¬ p2657) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2312) := (fun h => hn (Or.inl h));
    let u1 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4573 := h65754;
    let u5 : p4578 := h65823;
    let u6 : (¬ p2310) := (Or.elim h2755 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2318 := (Or.elim h5196 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u8 : p2317 := (Or.elim h7254 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u4))))));
    let u9 : p2319 := (Or.elim h2769 (fun q0 => (False.elim (q0 u8))) (fun r0 => r0));
    let u10 : p2307 := (Or.elim h2770 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u11 : (¬ p3567) := (Or.elim h5195 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    let u12 : (¬ p3987) := (Or.elim h49439 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    let u13 : (¬ p4579) := (Or.elim h7274 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    let u14 : (¬ p4582) := (Or.elim h7280 (fun q0 => (False.elim (u12 q0))) (fun r0 => r0));
    (Or.elim h7287 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u13 q1))) (fun r1 => (False.elim (u14 r1)))))))

theorem step65910 (p2274 p2608 p3093 p3549 p3591 p4366 p4427 p4514 p5013 p5014 p5019 p5140 : Prop)
    (h65583 : p5013)
    (h8704 : p4427 ∨ (¬ p5140))
    (h8705 : p3549 ∨ (¬ p5140))
    (h41837 : (¬ p2274) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427) ∨ (¬ p4514))
    (h47638 : (¬ p2274) ∨ (¬ p2608) ∨ (¬ p3549) ∨ (¬ p3591))
    (h8392 : p3093 ∨ (¬ p5019))
    (h8386 : p3591 ∨ (¬ p5014))
    (h8398 : (¬ p5013) ∨ p5014 ∨ p5019)
    : (¬ p5140) ∨ (¬ p4366) ∨ (¬ p4514) ∨ (¬ p2608) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5140 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5013 := h65583;
    let u6 : p4427 := (Or.elim h8704 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p3549 := (Or.elim h8705 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : (¬ p3093) := (Or.elim h41837 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2))))))))));
    let u9 : (¬ p3591) := (Or.elim h47638 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => r2))))));
    let u10 : (¬ p5019) := (Or.elim h8392 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : (¬ p5014) := (Or.elim h8386 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    (Or.elim h8398 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (False.elim (u10 r1)))))))

theorem step65914 (p2230 p2284 p2563 p2579 p2589 p2659 p2901 p3096 p3413 p3872 p4235 p4534 p4535 p4537 p4705 p4713 p4714 p4716 : Prop)
    (h65780 : p4713)
    (h65673 : p4534)
    (h6731 : (¬ p2284) ∨ p2901 ∨ (¬ p3872))
    (h20312 : (¬ p2563) ∨ (¬ p3872) ∨ (¬ p4235))
    (h41883 : (¬ p2589) ∨ (¬ p2659) ∨ (¬ p2901) ∨ (¬ p3413) ∨ (¬ p4235))
    (h7624 : p2563 ∨ (¬ p4716))
    (h7142 : p2589 ∨ (¬ p4535))
    (h7630 : (¬ p4713) ∨ p4714 ∨ p4716)
    (h7154 : (¬ p4534) ∨ p4535 ∨ p4537)
    (h7617 : p3096 ∨ (¬ p4714))
    (h7148 : p2230 ∨ (¬ p4537))
    (h41152 : (¬ p2230) ∨ (¬ p2284) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4705))
    : (¬ p4235) ∨ (¬ p2579) ∨ (¬ p2284) ∨ (¬ p2659) ∨ (¬ p4705) ∨ (¬ p3413) ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4235 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4713 := h65780;
    let u8 : p4534 := h65673;
    let u9 : p2901 := (Or.elim h6731 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u6))))));
    let u10 : (¬ p2563) := (Or.elim h20312 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (False.elim (r1 u0))))));
    let u11 : (¬ p2589) := (Or.elim h41883 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0))))))))));
    let u12 : (¬ p4716) := (Or.elim h7624 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : (¬ p4535) := (Or.elim h7142 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    let u14 : p4714 := (Or.elim h7630 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u12 r1))))));
    let u15 : p4537 := (Or.elim h7154 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u13 q1))) (fun r1 => r1))));
    let u16 : p3096 := (Or.elim h7617 (fun q0 => q0) (fun r0 => (False.elim (r0 u14))));
    let u17 : p2230 := (Or.elim h7148 (fun q0 => q0) (fun r0 => (False.elim (r0 u15))));
    (Or.elim h41152 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u16))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step65915 (p2230 p2284 p2542 p2563 p2579 p2589 p2659 p2911 p3016 p3389 p3413 p3540 p3646 p3741 p3872 p3904 p4110 p4235 p4534 p4535 p4537 p4642 p4643 p4645 p4705 p4713 p4714 p4716 p5195 p5196 p5200 : Prop)
    (h65496 : p5195)
    (h65784 : p4642)
    (h65673 : p4534)
    (h65780 : p4713)
    (h46915 : (¬ p2579) ∨ (¬ p2911) ∨ (¬ p3016) ∨ (¬ p3389))
    (h8822 : p3389 ∨ (¬ p5200))
    (h8828 : (¬ p5195) ∨ p5196 ∨ p5200)
    (h8816 : p3540 ∨ (¬ p5196))
    (h65914 : (¬ p4235) ∨ (¬ p2579) ∨ (¬ p2284) ∨ (¬ p2659) ∨ (¬ p4705) ∨ (¬ p3413) ∨ (¬ p3872))
    (h7429 : p4235 ∨ (¬ p4643))
    (h7441 : (¬ p4642) ∨ p4643 ∨ p4645)
    (h7434 : p3741 ∨ (¬ p4645))
    (h19841 : (¬ p2230) ∨ (¬ p3540) ∨ (¬ p3741))
    (h38156 : p2589 ∨ (¬ p3540) ∨ (¬ p3741))
    (h7148 : p2230 ∨ (¬ p4537))
    (h41609 : (¬ p2284) ∨ (¬ p2589) ∨ (¬ p2659) ∨ (¬ p3413) ∨ (¬ p4110))
    (h7154 : (¬ p4534) ∨ p4535 ∨ p4537)
    (h7618 : p4110 ∨ (¬ p4714))
    (h7140 : p3904 ∨ (¬ p4535))
    (h7630 : (¬ p4713) ∨ p4714 ∨ p4716)
    (h41572 : (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2659) ∨ (¬ p3646) ∨ (¬ p3904))
    (h7624 : p2563 ∨ (¬ p4716))
    : (¬ p2579) ∨ (¬ p2284) ∨ (¬ p2659) ∨ (¬ p3646) ∨ (¬ p4705) ∨ (¬ p2542) ∨ (¬ p3413) ∨ (¬ p2911) ∨ (¬ p3016) ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p5195 := h65496;
    let u11 : p4642 := h65784;
    let u12 : p4534 := h65673;
    let u13 : p4713 := h65780;
    let u14 : (¬ p3389) := (Or.elim h46915 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => r2))))));
    let u15 : (¬ p5200) := (Or.elim h8822 (fun q0 => (False.elim (u14 q0))) (fun r0 => r0));
    let u16 : p5196 := (Or.elim h8828 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u15 r1))))));
    let u17 : p3540 := (Or.elim h8816 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    let u18 : (¬ p4235) := (Or.elim h65914 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u9))))))))))))));
    let u19 : (¬ p4643) := (Or.elim h7429 (fun q0 => (False.elim (u18 q0))) (fun r0 => r0));
    let u20 : p4645 := (Or.elim h7441 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u19 q1))) (fun r1 => r1))));
    let u21 : p3741 := (Or.elim h7434 (fun q0 => q0) (fun r0 => (False.elim (r0 u20))));
    let u22 : (¬ p2230) := (Or.elim h19841 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u17))) (fun r1 => (False.elim (r1 u21))))));
    let u23 : p2589 := (Or.elim h38156 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u17))) (fun r1 => (False.elim (r1 u21))))));
    let u24 : (¬ p4537) := (Or.elim h7148 (fun q0 => (False.elim (u22 q0))) (fun r0 => r0));
    let u25 : (¬ p4110) := (Or.elim h41609 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u23))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => r3))))))));
    let u26 : p4535 := (Or.elim h7154 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u24 r1))))));
    let u27 : (¬ p4714) := (Or.elim h7618 (fun q0 => (False.elim (u25 q0))) (fun r0 => r0));
    let u28 : p3904 := (Or.elim h7140 (fun q0 => q0) (fun r0 => (False.elim (r0 u26))));
    let u29 : p4716 := (Or.elim h7630 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u27 q1))) (fun r1 => r1))));
    let u30 : (¬ p2563) := (Or.elim h41572 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u28))))))))));
    (Or.elim h7624 (fun q0 => (False.elim (u30 q0))) (fun r0 => (False.elim (r0 u29)))))

theorem step65917 (p2299 p2911 p2922 p2933 p3093 p3379 p3452 p4452 p5188 p5189 p5192 : Prop)
    (h65500 : p5188)
    (h45312 : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379))
    (h64862 : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p2933) ∨ (¬ p3093) ∨ (¬ p3452) ∨ (¬ p4452))
    (h8805 : p3379 ∨ (¬ p5192))
    (h8799 : p3452 ∨ (¬ p5189))
    (h8811 : (¬ p5188) ∨ p5189 ∨ p5192)
    : (¬ p2299) ∨ (¬ p2933) ∨ (¬ p2922) ∨ (¬ p4452) ∨ (¬ p3093) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5188 := h65500;
    let u7 : (¬ p3379) := (Or.elim h45312 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    let u8 : (¬ p3452) := (Or.elim h64862 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u3))))))))))));
    let u9 : (¬ p5192) := (Or.elim h8805 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u10 : (¬ p5189) := (Or.elim h8799 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    (Or.elim h8811 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (False.elim (u9 r1)))))))

theorem step65918 (p2177 p2299 p2493 p2496 p2499 p2503 p2553 p2911 p2922 p2925 p2928 p2932 p2933 p3093 p3309 p3379 p3452 p3920 p4452 p4499 p4500 p4502 p4676 p4709 p4925 p5143 p5188 p5189 p5192 : Prop)
    (h65820 : p4676)
    (h65902 : p4925)
    (h65748 : p4499)
    (h65500 : p5188)
    (h8711 : p3309 ∨ (¬ p5143))
    (h8710 : p4452 ∨ (¬ p5143))
    (h7607 : p2553 ∨ (¬ p4709))
    (h7606 : p3920 ∨ (¬ p4709))
    (h3127 : (¬ p2496) ∨ p2499)
    (h6412 : p2499 ∨ (¬ p2928) ∨ (¬ p3920))
    (h7524 : p2496 ∨ p2503 ∨ (¬ p4676))
    (h3978 : (¬ p2925) ∨ p2928)
    (h3141 : p2493 ∨ (¬ p2503))
    (h8155 : p2925 ∨ p2932 ∨ (¬ p4925))
    (h27159 : (¬ p2493) ∨ p2922 ∨ (¬ p3920))
    (h3990 : (¬ p2932) ∨ p2933)
    (h65917 : (¬ p2299) ∨ (¬ p2933) ∨ (¬ p2922) ∨ (¬ p4452) ∨ (¬ p3093) ∨ (¬ p2911))
    (h7056 : p2299 ∨ (¬ p4500))
    (h7068 : (¬ p4499) ∨ p4500 ∨ p4502)
    (h7062 : p2177 ∨ (¬ p4502))
    (h47943 : (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3452))
    (h42843 : (¬ p2177) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p3379))
    (h8799 : p3452 ∨ (¬ p5189))
    (h8805 : p3379 ∨ (¬ p5192))
    (h8811 : (¬ p5188) ∨ p5189 ∨ p5192)
    : p2499 ∨ (¬ p5143) ∨ (¬ p3093) ∨ (¬ p4709) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2499) := (fun h => hn (Or.inl h));
    let u1 : p5143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4709 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4676 := h65820;
    let u6 : p4925 := h65902;
    let u7 : p4499 := h65748;
    let u8 : p5188 := h65500;
    let u9 : p3309 := (Or.elim h8711 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u10 : p4452 := (Or.elim h8710 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u11 : p2553 := (Or.elim h7607 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u12 : p3920 := (Or.elim h7606 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u13 : (¬ p2496) := (Or.elim h3127 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u14 : (¬ p2928) := (Or.elim h6412 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u12))))));
    let u15 : p2503 := (Or.elim h7524 (fun q0 => (False.elim (u13 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u5))))));
    let u16 : (¬ p2925) := (Or.elim h3978 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    let u17 : p2493 := (Or.elim h3141 (fun q0 => q0) (fun r0 => (False.elim (r0 u15))));
    let u18 : p2932 := (Or.elim h8155 (fun q0 => (False.elim (u16 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u6))))));
    let u19 : p2922 := (Or.elim h27159 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u12))))));
    let u20 : p2933 := (Or.elim h3990 (fun q0 => (False.elim (q0 u18))) (fun r0 => r0));
    let u21 : (¬ p2299) := (Or.elim h65917 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u20))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u19))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4))))))))))));
    let u22 : (¬ p4500) := (Or.elim h7056 (fun q0 => (False.elim (u21 q0))) (fun r0 => r0));
    let u23 : p4502 := (Or.elim h7068 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u22 q1))) (fun r1 => r1))));
    let u24 : p2177 := (Or.elim h7062 (fun q0 => q0) (fun r0 => (False.elim (r0 u23))));
    let u25 : (¬ p3452) := (Or.elim h47943 (fun q0 => (False.elim (q0 u24))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => r2))))));
    let u26 : (¬ p3379) := (Or.elim h42843 (fun q0 => (False.elim (q0 u24))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u17))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => r2))))));
    let u27 : (¬ p5189) := (Or.elim h8799 (fun q0 => (False.elim (u25 q0))) (fun r0 => r0));
    let u28 : (¬ p5192) := (Or.elim h8805 (fun q0 => (False.elim (u26 q0))) (fun r0 => r0));
    (Or.elim h8811 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u27 q1))) (fun r1 => (False.elim (u28 r1)))))))

theorem step65920 (p2284 p2386 p2406 p2499 p3238 p3413 p3487 p3574 p3646 p3743 p4031 p4484 p4626 p4627 p4630 p4705 p4808 p4809 p4811 p4812 : Prop)
    (h65831 : p4808)
    (h65800 : p4626)
    (h7022 : p3646 ∨ (¬ p4484))
    (h7021 : p3743 ∨ (¬ p4484))
    (h6364 : (¬ p2499) ∨ (¬ p3487) ∨ p3574)
    (h54371 : (¬ p2284) ∨ (¬ p2386) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3743) ∨ (¬ p4705))
    (h7861 : p3487 ∨ (¬ p4812))
    (h7401 : p2406 ∨ (¬ p4630))
    (h7869 : (¬ p4808) ∨ p4809 ∨ p4812)
    (h7407 : (¬ p4626) ∨ p4627 ∨ p4630)
    (h7859 : (¬ p4809) ∨ p4811)
    (h7395 : p3238 ∨ (¬ p4627))
    (h41126 : (¬ p2284) ∨ (¬ p3238) ∨ (¬ p3413) ∨ (¬ p3646) ∨ (¬ p4031) ∨ (¬ p4811))
    : (¬ p2499) ∨ (¬ p4484) ∨ (¬ p2284) ∨ (¬ p4705) ∨ (¬ p3413) ∨ (¬ p4031) ∨ p3574 ∨ (¬ p2386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4484 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3574) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4808 := h65831;
    let u9 : p4626 := h65800;
    let u10 : p3646 := (Or.elim h7022 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u11 : p3743 := (Or.elim h7021 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u12 : (¬ p3487) := (Or.elim h6364 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u6 r1))))));
    let u13 : (¬ p2406) := (Or.elim h54371 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (False.elim (r4 u3))))))))))));
    let u14 : (¬ p4812) := (Or.elim h7861 (fun q0 => (False.elim (u12 q0))) (fun r0 => r0));
    let u15 : (¬ p4630) := (Or.elim h7401 (fun q0 => (False.elim (u13 q0))) (fun r0 => r0));
    let u16 : p4809 := (Or.elim h7869 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u14 r1))))));
    let u17 : p4627 := (Or.elim h7407 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u15 r1))))));
    let u18 : p4811 := (Or.elim h7859 (fun q0 => (False.elim (q0 u16))) (fun r0 => r0));
    let u19 : p3238 := (Or.elim h7395 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    (Or.elim h41126 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u19))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u18)))))))))))))

theorem step65921 (p638 p644 p2767 : Prop)
    (h3661 : (¬ p638) ∨ p2767)
    (h3662 : (¬ p644) ∨ p2767)
    (h703 : p638 ∨ p644)
    : p2767 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2767) := (fun h => hn h);
    let u1 : (¬ p638) := (Or.elim h3661 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p644) := (Or.elim h3662 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h703 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65922 (p2767 p2768 : Prop)
    (h65921 : p2767)
    (h3679 : (¬ p2767) ∨ p2768)
    : p2768 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2768) := (fun h => hn h);
    let u1 : p2767 := h65921;
    (Or.elim h3679 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65923 (p2768 p4833 : Prop)
    (h65922 : p2768)
    (h7921 : (¬ p2768) ∨ p4833)
    : p4833 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4833) := (fun h => hn h);
    let u1 : p2768 := h65922;
    (Or.elim h7921 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65924 (p26 p32 p2115 : Prop)
    (h2366 : (¬ p26) ∨ p2115)
    (h2367 : (¬ p32) ∨ p2115)
    (h40 : p26 ∨ p32)
    : p2115 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2115) := (fun h => hn h);
    let u1 : (¬ p26) := (Or.elim h2366 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p32) := (Or.elim h2367 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h40 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65925 (p2115 p2116 : Prop)
    (h65924 : p2115)
    (h2384 : (¬ p2115) ∨ p2116)
    : p2116 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2116) := (fun h => hn h);
    let u1 : p2115 := h65924;
    (Or.elim h2384 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65926 (p2116 p4469 : Prop)
    (h65925 : p2116)
    (h6997 : (¬ p2116) ∨ p4469)
    : p4469 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4469) := (fun h => hn h);
    let u1 : p2116 := h65925;
    (Or.elim h6997 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65927 (p4469 p5787 : Prop)
    (h65926 : p4469)
    (h11746 : (¬ p4469) ∨ p5787)
    : p5787 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5787) := (fun h => hn h);
    let u1 : p4469 := h65926;
    (Or.elim h11746 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65928 (p2122 p2177 p2553 p2598 p2774 p3055 p3422 p4725 p4726 p4728 : Prop)
    (h65591 : p4725)
    (h46418 : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p3422))
    (h56917 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2774) ∨ (¬ p3055))
    (h7670 : p2598 ∨ (¬ p4728))
    (h7664 : p3055 ∨ (¬ p4726))
    (h7676 : (¬ p4725) ∨ p4726 ∨ p4728)
    : (¬ p2177) ∨ (¬ p2122) ∨ (¬ p3422) ∨ (¬ p2774) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4725 := h65591;
    let u6 : (¬ p2598) := (Or.elim h46418 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    let u7 : (¬ p3055) := (Or.elim h56917 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    let u8 : (¬ p4728) := (Or.elim h7670 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    let u9 : (¬ p4726) := (Or.elim h7664 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    (Or.elim h7676 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (False.elim (u8 r1)))))))

theorem step65934 (p2132 p2142 p2143 p2156 p2284 p2780 p2860 p4428 p4886 p4887 p4890 p4906 : Prop)
    (h65741 : p4886)
    (h2420 : (¬ p2142) ∨ p2143)
    (h2422 : p2132 ∨ (¬ p2142))
    (h6640 : (¬ p2143) ∨ p2156 ∨ (¬ p2860))
    (h50691 : (¬ p2132) ∨ (¬ p2284) ∨ (¬ p2780) ∨ (¬ p4428) ∨ (¬ p4906))
    (h8057 : p2860 ∨ (¬ p4890))
    (h8050 : p4428 ∨ (¬ p4887))
    (h8063 : (¬ p4886) ∨ p4887 ∨ p4890)
    : (¬ p2142) ∨ p2156 ∨ (¬ p4906) ∨ (¬ p2284) ∨ (¬ p2780) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2142 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4886 := h65741;
    let u6 : p2143 := (Or.elim h2420 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u7 : p2132 := (Or.elim h2422 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : (¬ p2860) := (Or.elim h6640 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    let u9 : (¬ p4428) := (Or.elim h50691 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    let u10 : (¬ p4890) := (Or.elim h8057 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : (¬ p4887) := (Or.elim h8050 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    (Or.elim h8063 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (False.elim (u10 r1)))))))

theorem step65936 (p158 p164 p2257 : Prop)
    (h2651 : (¬ p158) ∨ p2257)
    (h2652 : (¬ p164) ∨ p2257)
    (h183 : p158 ∨ p164)
    : p2257 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2257) := (fun h => hn h);
    let u1 : (¬ p158) := (Or.elim h2651 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p164) := (Or.elim h2652 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h183 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65937 (p2257 p2258 : Prop)
    (h65936 : p2257)
    (h2669 : (¬ p2257) ∨ p2258)
    : p2258 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2258) := (fun h => hn h);
    let u1 : p2257 := h65936;
    (Or.elim h2669 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65938 (p2258 p4546 : Prop)
    (h65937 : p2258)
    (h7198 : (¬ p2258) ∨ p4546)
    : p4546 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4546) := (fun h => hn h);
    let u1 : p2258 := h65937;
    (Or.elim h7198 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65939 (p4546 p5814 : Prop)
    (h65938 : p4546)
    (h11903 : (¬ p4546) ∨ p5814)
    : p5814 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5814) := (fun h => hn h);
    let u1 : p4546 := h65938;
    (Or.elim h11903 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65942 (p350 p356 p2442 : Prop)
    (h3015 : (¬ p350) ∨ p2442)
    (h3016 : (¬ p356) ∨ p2442)
    (h391 : p350 ∨ p356)
    : p2442 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2442) := (fun h => hn h);
    let u1 : (¬ p350) := (Or.elim h3015 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p356) := (Or.elim h3016 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h391 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65943 (p2442 p2443 : Prop)
    (h65942 : p2442)
    (h3033 : (¬ p2442) ∨ p2443)
    : p2443 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2443) := (fun h => hn h);
    let u1 : p2442 := h65942;
    (Or.elim h3033 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65944 (p2443 p4654 : Prop)
    (h65943 : p2443)
    (h7477 : (¬ p2443) ∨ p4654)
    : p4654 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4654) := (fun h => hn h);
    let u1 : p2443 := h65943;
    (Or.elim h7477 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65945 (p4654 p5859 : Prop)
    (h65944 : p4654)
    (h12166 : (¬ p4654) ∨ p5859)
    : p5859 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5859) := (fun h => hn h);
    let u1 : p4654 := h65944;
    (Or.elim h12166 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65947 (p2192 p2210 p2608 p3093 p3369 p3646 p4338 p4377 p4515 p4519 p4520 p4523 : Prop)
    (h65865 : p4519)
    (h7095 : p4338 ∨ (¬ p4515))
    (h7096 : p2192 ∨ (¬ p4515))
    (h34923 : (¬ p2210) ∨ p3093 ∨ (¬ p4338))
    (h41882 : (¬ p2192) ∨ (¬ p2608) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p4377))
    (h7113 : p2210 ∨ (¬ p4523))
    (h7105 : p3369 ∨ (¬ p4520))
    (h7119 : (¬ p4519) ∨ p4520 ∨ p4523)
    : (¬ p4515) ∨ (¬ p3646) ∨ (¬ p2608) ∨ (¬ p4377) ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4515 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4519 := h65865;
    let u6 : p4338 := (Or.elim h7095 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p2192 := (Or.elim h7096 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : (¬ p2210) := (Or.elim h34923 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u6))))));
    let u9 : (¬ p3369) := (Or.elim h41882 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3))))))))));
    let u10 : (¬ p4523) := (Or.elim h7113 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : (¬ p4520) := (Or.elim h7105 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    (Or.elim h7119 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (False.elim (u10 r1)))))))

theorem step65949 (p2317 p2318 p2319 p2962 p3556 p3646 p3872 p4275 p4483 p4484 p4487 p4553 p4554 p4557 : Prop)
    (h65737 : p4483)
    (h65724 : p4553)
    (h2769 : (¬ p2317) ∨ p2319)
    (h2768 : (¬ p2317) ∨ p2318)
    (h7022 : p3646 ∨ (¬ p4484))
    (h6734 : (¬ p3556) ∨ p3646 ∨ (¬ p3872))
    (h7034 : (¬ p4483) ∨ p4484 ∨ p4487)
    (h7207 : p3872 ∨ (¬ p4557))
    (h7027 : p2962 ∨ (¬ p4487))
    (h7214 : (¬ p4553) ∨ p4554 ∨ p4557)
    (h13907 : (¬ p2318) ∨ (¬ p2319) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p4275))
    (h7201 : p4275 ∨ (¬ p4554))
    : p3646 ∨ (¬ p2317) ∨ (¬ p3556) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3646) := (fun h => hn (Or.inl h));
    let u1 : p2317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4483 := h65737;
    let u4 : p4553 := h65724;
    let u5 : p2319 := (Or.elim h2769 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u6 : p2318 := (Or.elim h2768 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u7 : (¬ p4484) := (Or.elim h7022 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u8 : (¬ p3872) := (Or.elim h6734 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => r1))));
    let u9 : p4487 := (Or.elim h7034 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => r1))));
    let u10 : (¬ p4557) := (Or.elim h7207 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : p2962 := (Or.elim h7027 (fun q0 => q0) (fun r0 => (False.elim (r0 u9))));
    let u12 : p4554 := (Or.elim h7214 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u10 r1))))));
    let u13 : (¬ p4275) := (Or.elim h13907 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h7201 (fun q0 => (False.elim (u13 q0))) (fun r0 => (False.elim (r0 u12)))))

theorem step65950 (p2210 p2284 p2608 p3555 p3591 p3957 p4173 p4282 p4511 p4512 p4519 p4520 p4523 p4955 p4956 p4957 p4958 : Prop)
    (h65661 : p4955)
    (h65865 : p4519)
    (h7090 : p4173 ∨ (¬ p4511))
    (h7089 : p3957 ∨ (¬ p4511))
    (h7088 : (¬ p4511) ∨ p4512)
    (h38297 : (¬ p2284) ∨ (¬ p3957) ∨ (¬ p4282) ∨ (¬ p4512))
    (h46321 : (¬ p2284) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p4173))
    (h8244 : p4282 ∨ (¬ p4958))
    (h7107 : p3555 ∨ (¬ p4520))
    (h8252 : (¬ p4955) ∨ p4956 ∨ p4958)
    (h7119 : (¬ p4519) ∨ p4520 ∨ p4523)
    (h8242 : (¬ p4956) ∨ p4957)
    (h7113 : p2210 ∨ (¬ p4523))
    (h48141 : (¬ p2210) ∨ (¬ p2284) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4957))
    : (¬ p2284) ∨ (¬ p4511) ∨ (¬ p3591) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4511 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4955 := h65661;
    let u5 : p4519 := h65865;
    let u6 : p4173 := (Or.elim h7090 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p3957 := (Or.elim h7089 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u8 : p4512 := (Or.elim h7088 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u9 : (¬ p4282) := (Or.elim h38297 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u8))))))));
    let u10 : (¬ p3555) := (Or.elim h46321 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u6))))))));
    let u11 : (¬ p4958) := (Or.elim h8244 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u12 : (¬ p4520) := (Or.elim h7107 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : p4956 := (Or.elim h8252 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u11 r1))))));
    let u14 : p4523 := (Or.elim h7119 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u12 q1))) (fun r1 => r1))));
    let u15 : p4957 := (Or.elim h8242 (fun q0 => (False.elim (q0 u13))) (fun r0 => r0));
    let u16 : p2210 := (Or.elim h7113 (fun q0 => q0) (fun r0 => (False.elim (r0 u14))));
    (Or.elim h48141 (fun q0 => (False.elim (q0 u16))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u15)))))))))))

theorem step65953 (p2493 p2496 p2498 p2499 p2503 p2608 p3379 p3422 p3452 p3591 p4676 p5188 p5189 p5192 p5214 : Prop)
    (h65820 : p4676)
    (h65500 : p5188)
    (h9329 : (¬ p2493) ∨ (¬ p2499))
    (h45490 : (¬ p2499) ∨ (¬ p2608) ∨ (¬ p3422) ∨ (¬ p3452))
    (h3141 : p2493 ∨ (¬ p2503))
    (h8799 : p3452 ∨ (¬ p5189))
    (h7524 : p2496 ∨ p2503 ∨ (¬ p4676))
    (h8811 : (¬ p5188) ∨ p5189 ∨ p5192)
    (h3126 : (¬ p2496) ∨ p2498)
    (h8805 : p3379 ∨ (¬ p5192))
    (h41933 : (¬ p2498) ∨ (¬ p3379) ∨ (¬ p3422) ∨ (¬ p3591) ∨ (¬ p5214))
    : (¬ p2499) ∨ (¬ p3422) ∨ (¬ p5214) ∨ (¬ p3591) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4676 := h65820;
    let u6 : p5188 := h65500;
    let u7 : (¬ p2493) := (Or.elim h9329 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : (¬ p3452) := (Or.elim h45490 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    let u9 : (¬ p2503) := (Or.elim h3141 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u10 : (¬ p5189) := (Or.elim h8799 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : p2496 := (Or.elim h7524 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (False.elim (r1 u5))))));
    let u12 : p5192 := (Or.elim h8811 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => r1))));
    let u13 : p2498 := (Or.elim h3126 (fun q0 => (False.elim (q0 u11))) (fun r0 => r0));
    let u14 : p3379 := (Or.elim h8805 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    (Or.elim h41933 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step65955 (p2542 p2619 p3693 p3878 p4256 p4355 p4437 p4605 p4606 p4609 p4885 p5007 : Prop)
    (h65771 : p4605)
    (h8367 : p3878 ∨ (¬ p5007))
    (h8368 : p4437 ∨ (¬ p5007))
    (h8369 : p4256 ∨ (¬ p5007))
    (h25935 : (¬ p2542) ∨ (¬ p3878) ∨ (¬ p4355) ∨ (¬ p4437))
    (h51071 : (¬ p2542) ∨ (¬ p2619) ∨ (¬ p3693) ∨ (¬ p4256) ∨ (¬ p4885))
    (h7348 : p4355 ∨ (¬ p4609))
    (h7342 : p3693 ∨ (¬ p4606))
    (h7355 : (¬ p4605) ∨ p4606 ∨ p4609)
    : (¬ p5007) ∨ (¬ p2542) ∨ (¬ p4885) ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5007 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4605 := h65771;
    let u5 : p3878 := (Or.elim h8367 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p4437 := (Or.elim h8368 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p4256 := (Or.elim h8369 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : (¬ p4355) := (Or.elim h25935 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u6))))))));
    let u9 : (¬ p3693) := (Or.elim h51071 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u2))))))))));
    let u10 : (¬ p4609) := (Or.elim h7348 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : (¬ p4606) := (Or.elim h7342 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    (Or.elim h7355 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (False.elim (u10 r1)))))))

theorem step65956 (p2373 p2619 p2850 p3096 p3582 p3584 p3880 p4509 p4605 p4606 p4609 p4715 : Prop)
    (h65771 : p4605)
    (h57959 : (¬ p2619) ∨ (¬ p3582) ∨ (¬ p3584) ∨ (¬ p3880) ∨ (¬ p4715))
    (h64242 : (¬ p2373) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3584) ∨ (¬ p4509))
    (h7343 : p3880 ∨ (¬ p4606))
    (h7349 : p2373 ∨ (¬ p4609))
    (h7355 : (¬ p4605) ∨ p4606 ∨ p4609)
    : (¬ p3584) ∨ (¬ p3582) ∨ (¬ p2850) ∨ (¬ p4715) ∨ (¬ p3096) ∨ (¬ p4509) ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3584 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4605 := h65771;
    let u8 : (¬ p3880) := (Or.elim h57959 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    let u9 : (¬ p2373) := (Or.elim h64242 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5))))))))));
    let u10 : (¬ p4606) := (Or.elim h7343 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : (¬ p4609) := (Or.elim h7349 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    (Or.elim h7355 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (False.elim (u11 r1)))))))

theorem step65957 (p2608 p2891 p3369 p3556 p3571 p3645 p4377 p4431 p4519 p4520 p4523 p4912 : Prop)
    (h65865 : p4519)
    (h8108 : p3571 ∨ (¬ p4912))
    (h8109 : p4431 ∨ (¬ p4912))
    (h8110 : p2891 ∨ (¬ p4912))
    (h13537 : (¬ p3556) ∨ (¬ p3571) ∨ (¬ p3645) ∨ (¬ p4431))
    (h41696 : (¬ p2608) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3556) ∨ (¬ p4377))
    (h7111 : p3645 ∨ (¬ p4523))
    (h7105 : p3369 ∨ (¬ p4520))
    (h7119 : (¬ p4519) ∨ p4520 ∨ p4523)
    : (¬ p4912) ∨ (¬ p4377) ∨ (¬ p3556) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4912 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4519 := h65865;
    let u5 : p3571 := (Or.elim h8108 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p4431 := (Or.elim h8109 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p2891 := (Or.elim h8110 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : (¬ p3645) := (Or.elim h13537 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u6))))))));
    let u9 : (¬ p3369) := (Or.elim h41696 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1))))))))));
    let u10 : (¬ p4523) := (Or.elim h7111 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : (¬ p4520) := (Or.elim h7105 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    (Or.elim h7119 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (False.elim (u10 r1)))))))

theorem step65959 (p2210 p2608 p2860 p3555 p3591 p3957 p4173 p4519 p4520 p4523 p4875 : Prop)
    (h65865 : p4519)
    (h50504 : (¬ p2210) ∨ (¬ p2860) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4875))
    (h63592 : (¬ p2608) ∨ (¬ p2860) ∨ (¬ p3555) ∨ (¬ p4173))
    (h7113 : p2210 ∨ (¬ p4523))
    (h7107 : p3555 ∨ (¬ p4520))
    (h7119 : (¬ p4519) ∨ p4520 ∨ p4523)
    : (¬ p2860) ∨ (¬ p3957) ∨ (¬ p4173) ∨ (¬ p3591) ∨ (¬ p4875) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4519 := h65865;
    let u7 : (¬ p2210) := (Or.elim h50504 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    let u8 : (¬ p3555) := (Or.elim h63592 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    let u9 : (¬ p4523) := (Or.elim h7113 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u10 : (¬ p4520) := (Or.elim h7107 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    (Or.elim h7119 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (False.elim (u9 r1)))))))

theorem step65965 (p2619 p2949 p2950 p2952 p3136 p3156 p3497 p3758 p4120 p4787 p5060 p5061 p5064 : Prop)
    (h65559 : p5060)
    (h4026 : (¬ p2949) ∨ p2950)
    (h4028 : (¬ p2949) ∨ p2952)
    (h50247 : (¬ p2950) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p4120) ∨ (¬ p4787))
    (h42885 : (¬ p2619) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3758))
    (h8496 : p3156 ∨ (¬ p5064))
    (h8490 : p3497 ∨ (¬ p5061))
    (h8502 : (¬ p5060) ∨ p5061 ∨ p5064)
    : (¬ p2949) ∨ (¬ p3136) ∨ (¬ p4787) ∨ (¬ p3758) ∨ (¬ p4120) ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2949 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5060 := h65559;
    let u7 : p2950 := (Or.elim h4026 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u8 : p2952 := (Or.elim h4028 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u9 : (¬ p3156) := (Or.elim h50247 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    let u10 : (¬ p3497) := (Or.elim h42885 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    let u11 : (¬ p5064) := (Or.elim h8496 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u12 : (¬ p5061) := (Or.elim h8490 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    (Or.elim h8502 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u12 q1))) (fun r1 => (False.elim (u11 r1)))))))

theorem step65966 (p2499 p2992 p3016 p3402 p3574 p4111 p4241 p4703 p4704 p4715 p4809 p4970 p4971 p4974 : Prop)
    (h65653 : p4970)
    (h7591 : (¬ p4703) ∨ p4704)
    (h7588 : p4241 ∨ (¬ p4703))
    (h7855 : p3402 ∨ (¬ p4809))
    (h7857 : p4111 ∨ (¬ p4809))
    (h48656 : (¬ p2499) ∨ (¬ p2992) ∨ (¬ p3016) ∨ (¬ p3402) ∨ (¬ p4704))
    (h41275 : (¬ p2992) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4715))
    (h8280 : p3016 ∨ (¬ p4974))
    (h8274 : p3574 ∨ (¬ p4971))
    (h8286 : (¬ p4970) ∨ p4971 ∨ p4974)
    : (¬ p4809) ∨ (¬ p4703) ∨ (¬ p2499) ∨ (¬ p4715) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4809 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4703 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4970 := h65653;
    let u6 : p4704 := (Or.elim h7591 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u7 : p4241 := (Or.elim h7588 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u8 : p3402 := (Or.elim h7855 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u9 : p4111 := (Or.elim h7857 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u10 : (¬ p3016) := (Or.elim h48656 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u6))))))))));
    let u11 : (¬ p3574) := (Or.elim h41275 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u3))))))))));
    let u12 : (¬ p4974) := (Or.elim h8280 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : (¬ p4971) := (Or.elim h8274 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    (Or.elim h8286 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u13 q1))) (fun r1 => (False.elim (u12 r1)))))))

theorem step65973 (p2427 p2440 p2589 p2870 p3556 p3582 p3698 p4031 p4235 p4534 p4535 p4537 p4642 p4643 p4645 p4727 p4753 p4879 p4880 p4883 : Prop)
    (h65784 : p4642)
    (h65795 : p4879)
    (h65673 : p4534)
    (h7435 : p2427 ∨ (¬ p4645))
    (h6374 : p2427 ∨ (¬ p2870) ∨ (¬ p3698))
    (h7441 : (¬ p4642) ∨ p4643 ∨ p4645)
    (h8033 : p3698 ∨ (¬ p4880))
    (h7429 : p4235 ∨ (¬ p4643))
    (h8046 : (¬ p4879) ∨ p4880 ∨ p4883)
    (h8039 : p3582 ∨ (¬ p4883))
    (h48557 : (¬ p2589) ∨ (¬ p2870) ∨ (¬ p3582) ∨ (¬ p4235) ∨ (¬ p4727))
    (h42204 : (¬ p2440) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3582) ∨ (¬ p4031) ∨ (¬ p4753))
    (h7142 : p2589 ∨ (¬ p4535))
    (h7146 : p4031 ∨ (¬ p4537))
    (h7154 : (¬ p4534) ∨ p4535 ∨ p4537)
    : p2427 ∨ (¬ p4727) ∨ (¬ p4753) ∨ (¬ p2440) ∨ (¬ p2870) ∨ (¬ p3556) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : p4727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4642 := h65784;
    let u7 : p4879 := h65795;
    let u8 : p4534 := h65673;
    let u9 : (¬ p4645) := (Or.elim h7435 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u10 : (¬ p3698) := (Or.elim h6374 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => r1))));
    let u11 : p4643 := (Or.elim h7441 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u9 r1))))));
    let u12 : (¬ p4880) := (Or.elim h8033 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : p4235 := (Or.elim h7429 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    let u14 : p4883 := (Or.elim h8046 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u12 q1))) (fun r1 => r1))));
    let u15 : p3582 := (Or.elim h8039 (fun q0 => q0) (fun r0 => (False.elim (r0 u14))));
    let u16 : (¬ p2589) := (Or.elim h48557 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (False.elim (r3 u1))))))))));
    let u17 : (¬ p4031) := (Or.elim h42204 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u15))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u2))))))))))));
    let u18 : (¬ p4535) := (Or.elim h7142 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    let u19 : (¬ p4537) := (Or.elim h7146 (fun q0 => (False.elim (u17 q0))) (fun r0 => r0));
    (Or.elim h7154 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u18 q1))) (fun r1 => (False.elim (u19 r1)))))))

theorem step65976 (p2132 p2427 p2542 p2589 p2598 p2654 p2659 p2661 p2662 p2850 p2870 p3556 p3582 p3698 p3904 p4235 p4535 p4642 p4643 p4645 p4725 p4726 p4727 p4728 p4762 p4879 p4880 p4883 : Prop)
    (h65836 : p4762)
    (h65795 : p4879)
    (h65591 : p4725)
    (h65784 : p4642)
    (h7140 : p3904 ∨ (¬ p4535))
    (h7142 : p2589 ∨ (¬ p4535))
    (h6146 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2662))
    (h3447 : (¬ p2661) ∨ p2662)
    (h7750 : p2654 ∨ p2661 ∨ (¬ p4762))
    (h3437 : (¬ p2654) ∨ p2659)
    (h42468 : (¬ p2542) ∨ (¬ p2659) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3698) ∨ (¬ p3904))
    (h8033 : p3698 ∨ (¬ p4880))
    (h8046 : (¬ p4879) ∨ p4880 ∨ p4883)
    (h8039 : p3582 ∨ (¬ p4883))
    (h8040 : p2850 ∨ (¬ p4883))
    (h25038 : p2132 ∨ (¬ p2598) ∨ (¬ p3582))
    (h7670 : p2598 ∨ (¬ p4728))
    (h7676 : (¬ p4725) ∨ p4726 ∨ p4728)
    (h7666 : (¬ p4726) ∨ p4727)
    (h50295 : (¬ p2427) ∨ (¬ p2850) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4727))
    (h48557 : (¬ p2589) ∨ (¬ p2870) ∨ (¬ p3582) ∨ (¬ p4235) ∨ (¬ p4727))
    (h7435 : p2427 ∨ (¬ p4645))
    (h7429 : p4235 ∨ (¬ p4643))
    (h7441 : (¬ p4642) ∨ p4643 ∨ p4645)
    : (¬ p4535) ∨ (¬ p2542) ∨ p2132 ∨ (¬ p2870) ∨ (¬ p3556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4535 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4762 := h65836;
    let u6 : p4879 := h65795;
    let u7 : p4725 := h65591;
    let u8 : p4642 := h65784;
    let u9 : p3904 := (Or.elim h7140 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u10 : p2589 := (Or.elim h7142 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u11 : (¬ p2662) := (Or.elim h6146 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => r1))));
    let u12 : (¬ p2661) := (Or.elim h3447 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u13 : p2654 := (Or.elim h7750 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u12 q1))) (fun r1 => (False.elim (r1 u5))))));
    let u14 : p2659 := (Or.elim h3437 (fun q0 => (False.elim (q0 u13))) (fun r0 => r0));
    let u15 : (¬ p3698) := (Or.elim h42468 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u9))))))))))));
    let u16 : (¬ p4880) := (Or.elim h8033 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u17 : p4883 := (Or.elim h8046 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u16 q1))) (fun r1 => r1))));
    let u18 : p3582 := (Or.elim h8039 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    let u19 : p2850 := (Or.elim h8040 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    let u20 : (¬ p2598) := (Or.elim h25038 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u18))))));
    let u21 : (¬ p4728) := (Or.elim h7670 (fun q0 => (False.elim (u20 q0))) (fun r0 => r0));
    let u22 : p4726 := (Or.elim h7676 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u21 r1))))));
    let u23 : p4727 := (Or.elim h7666 (fun q0 => (False.elim (q0 u22))) (fun r0 => r0));
    let u24 : (¬ p2427) := (Or.elim h50295 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u19))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (False.elim (r3 u23))))))))));
    let u25 : (¬ p4235) := (Or.elim h48557 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u18))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u23))))))))));
    let u26 : (¬ p4645) := (Or.elim h7435 (fun q0 => (False.elim (u24 q0))) (fun r0 => r0));
    let u27 : (¬ p4643) := (Or.elim h7429 (fun q0 => (False.elim (u25 q0))) (fun r0 => r0));
    (Or.elim h7441 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u27 q1))) (fun r1 => (False.elim (u26 r1)))))))

theorem step65977 (p2737 p2740 p2743 p2747 p3365 p3583 p3952 p3954 p4315 p4316 p4815 : Prop)
    (h65613 : p4815)
    (h48955 : (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3583) ∨ (¬ p3952) ∨ (¬ p4316))
    (h46288 : (¬ p2743) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4315))
    (h3622 : p2737 ∨ (¬ p2747))
    (h3608 : (¬ p2740) ∨ p2743)
    (h7875 : p2740 ∨ p2747 ∨ (¬ p4815))
    : (¬ p3952) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p4316) ∨ (¬ p3583) ∨ (¬ p3954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4815 := h65613;
    let u7 : (¬ p2737) := (Or.elim h48955 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3))))))))));
    let u8 : (¬ p2743) := (Or.elim h46288 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2))))))));
    let u9 : (¬ p2747) := (Or.elim h3622 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u10 : (¬ p2740) := (Or.elim h3608 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h7875 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (False.elim (r1 u6)))))))

theorem step65978 (p782 p788 p2904 : Prop)
    (h3934 : (¬ p782) ∨ p2904)
    (h3935 : (¬ p788) ∨ p2904)
    (h859 : p782 ∨ p788)
    : p2904 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2904) := (fun h => hn h);
    let u1 : (¬ p782) := (Or.elim h3934 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p788) := (Or.elim h3935 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h859 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65979 (p2904 p2905 : Prop)
    (h65978 : p2904)
    (h3952 : (¬ p2904) ∨ p2905)
    : p2905 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2905) := (fun h => hn h);
    let u1 : p2904 := h65978;
    (Or.elim h3952 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65980 (p2905 p4920 : Prop)
    (h65979 : p2905)
    (h8151 : (¬ p2905) ∨ p4920)
    : p4920 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4920) := (fun h => hn h);
    let u1 : p2905 := h65979;
    (Or.elim h8151 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65981 (p4920 p5949 : Prop)
    (h65980 : p4920)
    (h12696 : (¬ p4920) ∨ p5949)
    : p5949 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5949) := (fun h => hn h);
    let u1 : p4920 := h65980;
    (Or.elim h12696 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65984 (p2156 p2295 p2553 p2954 p3097 p3556 p3646 p4275 p4336 p4483 p4484 p4487 p4554 p4718 : Prop)
    (h65737 : p4483)
    (h7201 : p4275 ∨ (¬ p4554))
    (h7202 : p3097 ∨ (¬ p4554))
    (h57162 : (¬ p2156) ∨ (¬ p2553) ∨ (¬ p3556) ∨ (¬ p4275) ∨ (¬ p4718))
    (h42065 : (¬ p2295) ∨ (¬ p2954) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4336))
    (h7028 : p2156 ∨ (¬ p4487))
    (h7022 : p3646 ∨ (¬ p4484))
    (h7034 : (¬ p4483) ∨ p4484 ∨ p4487)
    : (¬ p4554) ∨ (¬ p2295) ∨ (¬ p2553) ∨ (¬ p4718) ∨ (¬ p3556) ∨ (¬ p2954) ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4554 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4483 := h65737;
    let u8 : p4275 := (Or.elim h7201 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u9 : p3097 := (Or.elim h7202 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u10 : (¬ p2156) := (Or.elim h57162 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u3))))))))));
    let u11 : (¬ p3646) := (Or.elim h42065 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u6))))))))));
    let u12 : (¬ p4487) := (Or.elim h7028 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : (¬ p4484) := (Or.elim h7022 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    (Or.elim h7034 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u13 q1))) (fun r1 => (False.elim (u12 r1)))))))

theorem step65988 (p2156 p2166 p2190 p2191 p2210 p2241 p2244 p2247 p2251 p2252 p2284 p2307 p2352 p2373 p2406 p2417 p2427 p2437 p2440 p2459 p2528 p2534 p2542 p2563 p2619 p2651 p2654 p2657 p2661 p2747 p2748 p2750 p2881 p2891 p2901 p2949 p2950 p2956 p2957 p2992 p3016 p3073 p3093 p3136 p3146 p3156 p3246 p3309 p3399 p3449 p3486 p3497 p3549 p3554 p3555 p3556 p3569 p3574 p3583 p3591 p3631 p3644 p3646 p3660 p3690 p3692 p3741 p3742 p3743 p3817 p3860 p3872 p3880 p3906 p3954 p3956 p3957 p3989 p4031 p4110 p4111 p4116 p4119 p4173 p4203 p4235 p4242 p4243 p4256 p4261 p4278 p4340 p4348 p4355 p4359 p4366 p4483 p4484 p4487 p4490 p4491 p4495 p4501 p4504 p4505 p4508 p4511 p4512 p4519 p4520 p4523 p4533 p4534 p4535 p4537 p4540 p4593 p4594 p4597 p4605 p4606 p4609 p4626 p4627 p4629 p4630 p4633 p4634 p4639 p4642 p4643 p4645 p4648 p4649 p4651 p4664 p4665 p4667 p4668 p4669 p4691 p4692 p4694 p4699 p4700 p4701 p4713 p4714 p4716 p4738 p4739 p4741 p4743 p4762 p4809 p4872 p4873 p4876 p4899 p4900 p4903 p4906 p4907 p4908 p4909 p4912 p4931 p4955 p4956 p4957 p4958 p4970 p4971 p4974 p4999 p5000 p5003 p5013 p5014 p5019 p5047 p5048 p5049 p5050 p5054 p5055 p5057 p5060 p5061 p5064 p5100 p5101 p5103 p5139 p5140 p5143 p5204 p5205 p5209 p5237 p5238 p5241 p5310 p5311 p5314 p5315 p5355 p5356 p5361 : Prop)
    (h65737 : p4483)
    (h65784 : p4642)
    (h65649 : p4899)
    (h65673 : p4534)
    (h65780 : p4713)
    (h65653 : p4970)
    (h65687 : p4931)
    (h65836 : p4762)
    (h65800 : p4626)
    (h65661 : p4955)
    (h65567 : p5047)
    (h65520 : p5139)
    (h65681 : p4907)
    (h65690 : p4490)
    (h65881 : p4648)
    (h65694 : p4664)
    (h65556 : p4540)
    (h65775 : p4691)
    (h65865 : p4519)
    (h65699 : p4872)
    (h65583 : p5013)
    (h65492 : p5204)
    (h65617 : p4738)
    (h65895 : p4593)
    (h65424 : p5355)
    (h65444 : p5310)
    (h65791 : p4504)
    (h65540 : p5100)
    (h65771 : p4605)
    (h65559 : p5060)
    (h65848 : p4633)
    (h65476 : p5237)
    (h65563 : p5054)
    (h65597 : p4999)
    (h7582 : (¬ p4699) ∨ p4700)
    (h3620 : (¬ p2747) ∨ p2748)
    (h7857 : p4111 ∨ (¬ p4809))
    (h19996 : (¬ p2748) ∨ (¬ p3136) ∨ (¬ p4111) ∨ (¬ p4700))
    (h8462 : p3136 ∨ (¬ p5050))
    (h8468 : (¬ p5047) ∨ p5048 ∨ p5050)
    (h8458 : p4906 ∨ (¬ p5048))
    (h8457 : (¬ p5048) ∨ p5049)
    (h20017 : (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4700))
    (h8246 : p2992 ∨ (¬ p4958))
    (h8252 : (¬ p4955) ∨ p4956 ∨ p4958)
    (h8242 : (¬ p4956) ∨ p4957)
    (h7584 : p2440 ∨ (¬ p4699))
    (h9451 : (¬ p2440) ∨ (¬ p2542))
    (h7856 : p4116 ∨ (¬ p4809))
    (h6867 : (¬ p2406) ∨ p2542 ∨ (¬ p4116))
    (h7401 : p2406 ∨ (¬ p4630))
    (h7407 : (¬ p4626) ∨ p4627 ∨ p4630)
    (h7397 : (¬ p4627) ∨ p4629)
    (h6731 : (¬ p2284) ∨ p2901 ∨ (¬ p3872))
    (h30502 : (¬ p2284) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3872))
    (h4040 : (¬ p2956) ∨ p2957)
    (h8182 : p2949 ∨ p2956 ∨ (¬ p4931))
    (h4026 : (¬ p2949) ∨ p2950)
    (h7585 : (¬ p4699) ∨ p4701)
    (h55129 : (¬ p2651) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3556) ∨ (¬ p4701))
    (h3449 : p2651 ∨ (¬ p2661))
    (h7750 : p2654 ∨ p2661 ∨ (¬ p4762))
    (h3435 : (¬ p2654) ∨ p2657)
    (h6734 : (¬ p3556) ∨ p3646 ∨ (¬ p3872))
    (h9440 : (¬ p2563) ∨ (¬ p4110))
    (h7618 : p4110 ∨ (¬ p4714))
    (h7630 : (¬ p4713) ∨ p4714 ∨ p4716)
    (h7622 : p4203 ∨ (¬ p4716))
    (h20348 : (¬ p2156) ∨ (¬ p3556) ∨ (¬ p3872))
    (h23019 : p2156 ∨ (¬ p2563) ∨ (¬ p4031))
    (h7146 : p4031 ∨ (¬ p4537))
    (h7154 : (¬ p4534) ∨ p4535 ∨ p4537)
    (h7144 : p4533 ∨ (¬ p4535))
    (h57213 : (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3646) ∨ (¬ p4203) ∨ (¬ p4533))
    (h8280 : p3016 ∨ (¬ p4974))
    (h8286 : (¬ p4970) ∨ p4971 ∨ p4974)
    (h8274 : p3574 ∨ (¬ p4971))
    (h20312 : (¬ p2563) ∨ (¬ p3872) ∨ (¬ p4235))
    (h7429 : p4235 ∨ (¬ p4643))
    (h7441 : (¬ p4642) ∨ p4643 ∨ p4645)
    (h7433 : p3569 ∨ (¬ p4645))
    (h20717 : (¬ p2881) ∨ (¬ p3569) ∨ (¬ p3644))
    (h8092 : p2881 ∨ (¬ p4903))
    (h8098 : (¬ p4899) ∨ p4900 ∨ p4903)
    (h8084 : p4119 ∨ (¬ p4900))
    (h7434 : p3741 ∨ (¬ p4645))
    (h7623 : p3660 ∨ (¬ p4716))
    (h5739 : p2427 ∨ (¬ p2563) ∨ (¬ p3872))
    (h3623 : (¬ p2747) ∨ p2750)
    (h7028 : p2156 ∨ (¬ p4487))
    (h7034 : (¬ p4483) ∨ p4484 ∨ p4487)
    (h7021 : p3743 ∨ (¬ p4484))
    (h7088 : (¬ p4511) ∨ p4512)
    (h7089 : p3957 ∨ (¬ p4511))
    (h7090 : p4173 ∨ (¬ p4511))
    (h41942 : (¬ p2284) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3743) ∨ (¬ p4512) ∨ (¬ p4957))
    (h41459 : (¬ p2563) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p4173) ∨ (¬ p4533))
    (h8705 : p3549 ∨ (¬ p5140))
    (h8110 : p2891 ∨ (¬ p4912))
    (h6798 : (¬ p2166) ∨ p2891 ∨ (¬ p4119))
    (h8717 : (¬ p5139) ∨ p5140 ∨ p5143)
    (h8116 : (¬ p4907) ∨ p4908 ∨ p4912)
    (h7045 : p2166 ∨ (¬ p4495))
    (h8711 : p3309 ∨ (¬ p5143))
    (h8102 : p3554 ∨ (¬ p4908))
    (h8103 : (¬ p4908) ∨ p4909)
    (h8104 : p3486 ∨ (¬ p4908))
    (h7051 : (¬ p4490) ∨ p4491 ∨ p4495)
    (h6682 : p2191 ∨ (¬ p3486) ∨ (¬ p4119))
    (h63238 : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p3486) ∨ (¬ p3569) ∨ (¬ p4629))
    (h7038 : p3906 ∨ (¬ p4491))
    (h7453 : p2437 ∨ (¬ p4651))
    (h7459 : (¬ p4648) ∨ p4649 ∨ p4651)
    (h7447 : p3742 ∨ (¬ p4649))
    (h44724 : (¬ p2657) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4348))
    (h43271 : (¬ p2247) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4111))
    (h7481 : p4348 ∨ (¬ p4665))
    (h2625 : (¬ p2244) ∨ p2247)
    (h7493 : (¬ p4664) ∨ p4665 ∨ p4667)
    (h7159 : p2244 ∨ p2251 ∨ (¬ p4540))
    (h7487 : p2459 ∨ (¬ p4667))
    (h7488 : (¬ p4667) ∨ p4668)
    (h7489 : (¬ p4667) ∨ p4669)
    (h2637 : (¬ p2251) ∨ p2252)
    (h2639 : p2241 ∨ (¬ p2251))
    (h45831 : (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p4256))
    (h42642 : (¬ p2241) ∨ (¬ p2563) ∨ (¬ p3555) ∨ (¬ p4173))
    (h41389 : (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p5049))
    (h7567 : p2534 ∨ (¬ p4692))
    (h7107 : p3555 ∨ (¬ p4520))
    (h8017 : p3583 ∨ (¬ p4873))
    (h7579 : (¬ p4691) ∨ p4692 ∨ p4694)
    (h7119 : (¬ p4519) ∨ p4520 ∨ p4523)
    (h8029 : (¬ p4872) ∨ p4873 ∨ p4876)
    (h7573 : p2528 ∨ (¬ p4694))
    (h7113 : p2210 ∨ (¬ p4523))
    (h8021 : p4243 ∨ (¬ p4876))
    (h48141 : (¬ p2210) ∨ (¬ p2284) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4957))
    (h41864 : (¬ p2210) ∨ (¬ p2427) ∨ (¬ p4366) ∨ (¬ p4629) ∨ (¬ p4909))
    (h6718 : p2166 ∨ (¬ p2619) ∨ (¬ p4243))
    (h8386 : p3591 ∨ (¬ p5014))
    (h8833 : p4366 ∨ (¬ p5205))
    (h7704 : p2619 ∨ (¬ p4743))
    (h8398 : (¬ p5013) ∨ p5014 ∨ p5019)
    (h8845 : (¬ p5204) ∨ p5205 ∨ p5209)
    (h7710 : (¬ p4738) ∨ p4739 ∨ p4743)
    (h8392 : p3093 ∨ (¬ p5019))
    (h8839 : p3399 ∨ (¬ p5209))
    (h7696 : p4359 ∨ (¬ p4739))
    (h7699 : (¬ p4739) ∨ p4741)
    (h50065 : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p3954) ∨ (¬ p3956) ∨ (¬ p4501))
    (h63123 : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p3954) ∨ (¬ p4668))
    (h53159 : (¬ p3093) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4243) ∨ (¬ p4512) ∨ (¬ p4741))
    (h7309 : p3956 ∨ (¬ p4594))
    (h9217 : p3631 ∨ (¬ p5361))
    (h9061 : p4242 ∨ (¬ p5311))
    (h7321 : (¬ p4593) ∨ p4594 ∨ p4597)
    (h9223 : (¬ p5355) ∨ p5356 ∨ p5361)
    (h9073 : (¬ p5310) ∨ p5311 ∨ p5314)
    (h7315 : p2352 ∨ (¬ p4597))
    (h9211 : p3817 ∨ (¬ p5356))
    (h9065 : (¬ p5314) ∨ p5315)
    (h40917 : (¬ p2352) ∨ (¬ p3646) ∨ (¬ p3660) ∨ (¬ p3989) ∨ (¬ p4533))
    (h59744 : (¬ p2901) ∨ (¬ p3246) ∨ (¬ p3554) ∨ (¬ p3817) ∨ (¬ p4957))
    (h7073 : p3989 ∨ (¬ p4505))
    (h8615 : p3246 ∨ (¬ p5103))
    (h7085 : (¬ p4504) ∨ p4505 ∨ p4508)
    (h8621 : (¬ p5100) ∨ p5101 ∨ p5103)
    (h7078 : p2190 ∨ (¬ p4508))
    (h8609 : p3690 ∨ (¬ p5101))
    (h6866 : (¬ p2190) ∨ p2373 ∨ (¬ p2563))
    (h6279 : (¬ p2190) ∨ (¬ p3880) ∨ p4110)
    (h5078 : (¬ p2190) ∨ (¬ p2284) ∨ (¬ p3497))
    (h51491 : (¬ p2417) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p3741) ∨ (¬ p4533))
    (h42140 : (¬ p2210) ∨ (¬ p2373) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p4629))
    (h7343 : p3880 ∨ (¬ p4606))
    (h8490 : p3497 ∨ (¬ p5061))
    (h7418 : p2417 ∨ (¬ p4639))
    (h8911 : p3860 ∨ (¬ p5238))
    (h7355 : (¬ p4605) ∨ p4606 ∨ p4609)
    (h8502 : (¬ p5060) ∨ p5061 ∨ p5064)
    (h7424 : (¬ p4633) ∨ p4634 ∨ p4639)
    (h8923 : (¬ p5237) ∨ p5238 ∨ p5241)
    (h7348 : p4355 ∨ (¬ p4609))
    (h8496 : p3156 ∨ (¬ p5064))
    (h7412 : p4278 ∨ (¬ p4634))
    (h8917 : p3449 ∨ (¬ p5241))
    (h54486 : (¬ p2191) ∨ (¬ p2528) ∨ (¬ p3692) ∨ (¬ p4355) ∨ (¬ p4629))
    (h61025 : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3742) ∨ (¬ p3954) ∨ (¬ p4278) ∨ (¬ p4669))
    (h8473 : p3692 ∨ (¬ p5055))
    (h8357 : p3073 ∨ (¬ p5003))
    (h8485 : (¬ p5054) ∨ p5055 ∨ p5057)
    (h8363 : (¬ p4999) ∨ p5000 ∨ p5003)
    (h8479 : p3146 ∨ (¬ p5057))
    (h8351 : p4261 ∨ (¬ p5000))
    (h63200 : (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4906))
    (h40482 : (¬ p4261) ∨ p4340 ∨ (¬ p5315))
    : (¬ p4511) ∨ (¬ p4256) ∨ (¬ p4809) ∨ (¬ p4699) ∨ (¬ p4501) ∨ (¬ p3644) ∨ (¬ p2307) ∨ (¬ p2563) ∨ (¬ p2747) ∨ (¬ p3954) ∨ (¬ p2284) ∨ (¬ p3872) ∨ (¬ p3556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4511 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4809 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p4483 := h65737;
    let u14 : p4642 := h65784;
    let u15 : p4899 := h65649;
    let u16 : p4534 := h65673;
    let u17 : p4713 := h65780;
    let u18 : p4970 := h65653;
    let u19 : p4931 := h65687;
    let u20 : p4762 := h65836;
    let u21 : p4626 := h65800;
    let u22 : p4955 := h65661;
    let u23 : p5047 := h65567;
    let u24 : p5139 := h65520;
    let u25 : p4907 := h65681;
    let u26 : p4490 := h65690;
    let u27 : p4648 := h65881;
    let u28 : p4664 := h65694;
    let u29 : p4540 := h65556;
    let u30 : p4691 := h65775;
    let u31 : p4519 := h65865;
    let u32 : p4872 := h65699;
    let u33 : p5013 := h65583;
    let u34 : p5204 := h65492;
    let u35 : p4738 := h65617;
    let u36 : p4593 := h65895;
    let u37 : p5355 := h65424;
    let u38 : p5310 := h65444;
    let u39 : p4504 := h65791;
    let u40 : p5100 := h65540;
    let u41 : p4605 := h65771;
    let u42 : p5060 := h65559;
    let u43 : p4633 := h65848;
    let u44 : p5237 := h65476;
    let u45 : p5054 := h65563;
    let u46 : p4999 := h65597;
    let u47 : p4700 := (Or.elim h7582 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    let u48 : p2748 := (Or.elim h3620 (fun q0 => (False.elim (q0 u8))) (fun r0 => r0));
    let u49 : p4111 := (Or.elim h7857 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u50 : (¬ p3136) := (Or.elim h19996 (fun q0 => (False.elim (q0 u48))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u49))) (fun r2 => (False.elim (r2 u47))))))));
    let u51 : (¬ p5050) := (Or.elim h8462 (fun q0 => (False.elim (u50 q0))) (fun r0 => r0));
    let u52 : p5048 := (Or.elim h8468 (fun q0 => (False.elim (q0 u23))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u51 r1))))));
    let u53 : p4906 := (Or.elim h8458 (fun q0 => q0) (fun r0 => (False.elim (r0 u52))));
    let u54 : p5049 := (Or.elim h8457 (fun q0 => (False.elim (q0 u52))) (fun r0 => r0));
    let u55 : (¬ p2992) := (Or.elim h20017 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u49))) (fun r1 => (False.elim (r1 u47))))));
    let u56 : (¬ p4958) := (Or.elim h8246 (fun q0 => (False.elim (u55 q0))) (fun r0 => r0));
    let u57 : p4956 := (Or.elim h8252 (fun q0 => (False.elim (q0 u22))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u56 r1))))));
    let u58 : p4957 := (Or.elim h8242 (fun q0 => (False.elim (q0 u57))) (fun r0 => r0));
    let u59 : p2440 := (Or.elim h7584 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u60 : (¬ p2542) := (Or.elim h9451 (fun q0 => (False.elim (q0 u59))) (fun r0 => r0));
    let u61 : p4116 := (Or.elim h7856 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u62 : (¬ p2406) := (Or.elim h6867 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u60 q1))) (fun r1 => (False.elim (r1 u61))))));
    let u63 : (¬ p4630) := (Or.elim h7401 (fun q0 => (False.elim (u62 q0))) (fun r0 => r0));
    let u64 : p4627 := (Or.elim h7407 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u63 r1))))));
    let u65 : p4629 := (Or.elim h7397 (fun q0 => (False.elim (q0 u64))) (fun r0 => r0));
    let u66 : p2901 := (Or.elim h6731 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u11))))));
    let u67 : (¬ p2957) := (Or.elim h30502 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (False.elim (r2 u11))))))));
    let u68 : (¬ p2956) := (Or.elim h4040 (fun q0 => q0) (fun r0 => (False.elim (u67 r0))));
    let u69 : p2949 := (Or.elim h8182 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u68 q1))) (fun r1 => (False.elim (r1 u19))))));
    let u70 : p2950 := (Or.elim h4026 (fun q0 => (False.elim (q0 u69))) (fun r0 => r0));
    let u71 : p4701 := (Or.elim h7585 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    let u72 : (¬ p2651) := (Or.elim h55129 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u66))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u70))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (False.elim (r3 u71))))))))));
    let u73 : (¬ p2661) := (Or.elim h3449 (fun q0 => (False.elim (u72 q0))) (fun r0 => r0));
    let u74 : p2654 := (Or.elim h7750 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u73 q1))) (fun r1 => (False.elim (r1 u20))))));
    let u75 : p2657 := (Or.elim h3435 (fun q0 => (False.elim (q0 u74))) (fun r0 => r0));
    let u76 : p3646 := (Or.elim h6734 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u11))))));
    let u77 : (¬ p4110) := (Or.elim h9440 (fun q0 => (False.elim (q0 u7))) (fun r0 => r0));
    let u78 : (¬ p4714) := (Or.elim h7618 (fun q0 => (False.elim (u77 q0))) (fun r0 => r0));
    let u79 : p4716 := (Or.elim h7630 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u78 q1))) (fun r1 => r1))));
    let u80 : p4203 := (Or.elim h7622 (fun q0 => q0) (fun r0 => (False.elim (r0 u79))));
    let u81 : (¬ p2156) := (Or.elim h20348 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (False.elim (r1 u11))))));
    let u82 : (¬ p4031) := (Or.elim h23019 (fun q0 => (False.elim (u81 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => r1))));
    let u83 : (¬ p4537) := (Or.elim h7146 (fun q0 => (False.elim (u82 q0))) (fun r0 => r0));
    let u84 : p4535 := (Or.elim h7154 (fun q0 => (False.elim (q0 u16))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u83 r1))))));
    let u85 : p4533 := (Or.elim h7144 (fun q0 => q0) (fun r0 => (False.elim (r0 u84))));
    let u86 : (¬ p3016) := (Or.elim h57213 (fun q0 => (False.elim (q0 u59))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u76))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u80))) (fun r3 => (False.elim (r3 u85))))))))));
    let u87 : (¬ p4974) := (Or.elim h8280 (fun q0 => (False.elim (u86 q0))) (fun r0 => r0));
    let u88 : p4971 := (Or.elim h8286 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u87 r1))))));
    let u89 : p3574 := (Or.elim h8274 (fun q0 => q0) (fun r0 => (False.elim (r0 u88))));
    let u90 : (¬ p4235) := (Or.elim h20312 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => r1))));
    let u91 : (¬ p4643) := (Or.elim h7429 (fun q0 => (False.elim (u90 q0))) (fun r0 => r0));
    let u92 : p4645 := (Or.elim h7441 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u91 q1))) (fun r1 => r1))));
    let u93 : p3569 := (Or.elim h7433 (fun q0 => q0) (fun r0 => (False.elim (r0 u92))));
    let u94 : (¬ p2881) := (Or.elim h20717 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u93))) (fun r1 => (False.elim (r1 u5))))));
    let u95 : (¬ p4903) := (Or.elim h8092 (fun q0 => (False.elim (u94 q0))) (fun r0 => r0));
    let u96 : p4900 := (Or.elim h8098 (fun q0 => (False.elim (q0 u15))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u95 r1))))));
    let u97 : p4119 := (Or.elim h8084 (fun q0 => q0) (fun r0 => (False.elim (r0 u96))));
    let u98 : p3741 := (Or.elim h7434 (fun q0 => q0) (fun r0 => (False.elim (r0 u92))));
    let u99 : p3660 := (Or.elim h7623 (fun q0 => q0) (fun r0 => (False.elim (r0 u79))));
    let u100 : p2427 := (Or.elim h5739 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (False.elim (r1 u11))))));
    let u101 : p2750 := (Or.elim h3623 (fun q0 => (False.elim (q0 u8))) (fun r0 => r0));
    let u102 : (¬ p4487) := (Or.elim h7028 (fun q0 => (False.elim (u81 q0))) (fun r0 => r0));
    let u103 : p4484 := (Or.elim h7034 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u102 r1))))));
    let u104 : p3743 := (Or.elim h7021 (fun q0 => q0) (fun r0 => (False.elim (r0 u103))));
    let u105 : p4512 := (Or.elim h7088 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u106 : p3957 := (Or.elim h7089 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u107 : p4173 := (Or.elim h7090 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u108 : (¬ p3549) := (Or.elim h41942 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u104))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u105))) (fun r4 => (False.elim (r4 u58))))))))))));
    let u109 : (¬ p2891) := (Or.elim h41459 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u107))) (fun r3 => (False.elim (r3 u85))))))))));
    let u110 : (¬ p5140) := (Or.elim h8705 (fun q0 => (False.elim (u108 q0))) (fun r0 => r0));
    let u111 : (¬ p4912) := (Or.elim h8110 (fun q0 => (False.elim (u109 q0))) (fun r0 => r0));
    let u112 : (¬ p2166) := (Or.elim h6798 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u109 q1))) (fun r1 => (False.elim (r1 u97))))));
    let u113 : p5143 := (Or.elim h8717 (fun q0 => (False.elim (q0 u24))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u110 q1))) (fun r1 => r1))));
    let u114 : p4908 := (Or.elim h8116 (fun q0 => (False.elim (q0 u25))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u111 r1))))));
    let u115 : (¬ p4495) := (Or.elim h7045 (fun q0 => (False.elim (u112 q0))) (fun r0 => r0));
    let u116 : p3309 := (Or.elim h8711 (fun q0 => q0) (fun r0 => (False.elim (r0 u113))));
    let u117 : p3554 := (Or.elim h8102 (fun q0 => q0) (fun r0 => (False.elim (r0 u114))));
    let u118 : p4909 := (Or.elim h8103 (fun q0 => (False.elim (q0 u114))) (fun r0 => r0));
    let u119 : p3486 := (Or.elim h8104 (fun q0 => q0) (fun r0 => (False.elim (r0 u114))));
    let u120 : p4491 := (Or.elim h7051 (fun q0 => (False.elim (q0 u26))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u115 r1))))));
    let u121 : p2191 := (Or.elim h6682 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u119))) (fun r1 => (False.elim (r1 u97))))));
    let u122 : (¬ p2437) := (Or.elim h63238 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u59))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u119))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u93))) (fun r3 => (False.elim (r3 u65))))))))));
    let u123 : p3906 := (Or.elim h7038 (fun q0 => q0) (fun r0 => (False.elim (r0 u120))));
    let u124 : (¬ p4651) := (Or.elim h7453 (fun q0 => (False.elim (u122 q0))) (fun r0 => r0));
    let u125 : p4649 := (Or.elim h7459 (fun q0 => (False.elim (q0 u27))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u124 r1))))));
    let u126 : p3742 := (Or.elim h7447 (fun q0 => q0) (fun r0 => (False.elim (r0 u125))));
    let u127 : (¬ p4348) := (Or.elim h44724 (fun q0 => (False.elim (q0 u75))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u126))) (fun r2 => r2))))));
    let u128 : (¬ p2247) := (Or.elim h43271 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u126))) (fun r2 => (False.elim (r2 u49))))))));
    let u129 : (¬ p4665) := (Or.elim h7481 (fun q0 => (False.elim (u127 q0))) (fun r0 => r0));
    let u130 : (¬ p2244) := (Or.elim h2625 (fun q0 => q0) (fun r0 => (False.elim (u128 r0))));
    let u131 : p4667 := (Or.elim h7493 (fun q0 => (False.elim (q0 u28))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u129 q1))) (fun r1 => r1))));
    let u132 : p2251 := (Or.elim h7159 (fun q0 => (False.elim (u130 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u29))))));
    let u133 : p2459 := (Or.elim h7487 (fun q0 => q0) (fun r0 => (False.elim (r0 u131))));
    let u134 : p4668 := (Or.elim h7488 (fun q0 => (False.elim (q0 u131))) (fun r0 => r0));
    let u135 : p4669 := (Or.elim h7489 (fun q0 => (False.elim (q0 u131))) (fun r0 => r0));
    let u136 : p2252 := (Or.elim h2637 (fun q0 => (False.elim (q0 u132))) (fun r0 => r0));
    let u137 : p2241 := (Or.elim h2639 (fun q0 => q0) (fun r0 => (False.elim (r0 u132))));
    let u138 : (¬ p2534) := (Or.elim h45831 (fun q0 => (False.elim (q0 u133))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u75))) (fun r2 => (False.elim (r2 u1))))))));
    let u139 : (¬ p3555) := (Or.elim h42642 (fun q0 => (False.elim (q0 u137))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u107))))))));
    let u140 : (¬ p3583) := (Or.elim h41389 (fun q0 => (False.elim (q0 u137))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u48))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (False.elim (r3 u54))))))))));
    let u141 : (¬ p4692) := (Or.elim h7567 (fun q0 => (False.elim (u138 q0))) (fun r0 => r0));
    let u142 : (¬ p4520) := (Or.elim h7107 (fun q0 => (False.elim (u139 q0))) (fun r0 => r0));
    let u143 : (¬ p4873) := (Or.elim h8017 (fun q0 => (False.elim (u140 q0))) (fun r0 => r0));
    let u144 : p4694 := (Or.elim h7579 (fun q0 => (False.elim (q0 u30))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u141 q1))) (fun r1 => r1))));
    let u145 : p4523 := (Or.elim h7119 (fun q0 => (False.elim (q0 u31))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u142 q1))) (fun r1 => r1))));
    let u146 : p4876 := (Or.elim h8029 (fun q0 => (False.elim (q0 u32))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u143 q1))) (fun r1 => r1))));
    let u147 : p2528 := (Or.elim h7573 (fun q0 => q0) (fun r0 => (False.elim (r0 u144))));
    let u148 : p2210 := (Or.elim h7113 (fun q0 => q0) (fun r0 => (False.elim (r0 u145))));
    let u149 : p4243 := (Or.elim h8021 (fun q0 => q0) (fun r0 => (False.elim (r0 u146))));
    let u150 : (¬ p3591) := (Or.elim h48141 (fun q0 => (False.elim (q0 u148))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u106))) (fun r3 => (False.elim (r3 u58))))))))));
    let u151 : (¬ p4366) := (Or.elim h41864 (fun q0 => (False.elim (q0 u148))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u100))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u65))) (fun r3 => (False.elim (r3 u118))))))))));
    let u152 : (¬ p2619) := (Or.elim h6718 (fun q0 => (False.elim (u112 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u149))))));
    let u153 : (¬ p5014) := (Or.elim h8386 (fun q0 => (False.elim (u150 q0))) (fun r0 => r0));
    let u154 : (¬ p5205) := (Or.elim h8833 (fun q0 => (False.elim (u151 q0))) (fun r0 => r0));
    let u155 : (¬ p4743) := (Or.elim h7704 (fun q0 => (False.elim (u152 q0))) (fun r0 => r0));
    let u156 : p5019 := (Or.elim h8398 (fun q0 => (False.elim (q0 u33))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u153 q1))) (fun r1 => r1))));
    let u157 : p5209 := (Or.elim h8845 (fun q0 => (False.elim (q0 u34))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u154 q1))) (fun r1 => r1))));
    let u158 : p4739 := (Or.elim h7710 (fun q0 => (False.elim (q0 u35))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u155 r1))))));
    let u159 : p3093 := (Or.elim h8392 (fun q0 => q0) (fun r0 => (False.elim (r0 u156))));
    let u160 : p3399 := (Or.elim h8839 (fun q0 => q0) (fun r0 => (False.elim (r0 u157))));
    let u161 : p4359 := (Or.elim h7696 (fun q0 => q0) (fun r0 => (False.elim (r0 u158))));
    let u162 : p4741 := (Or.elim h7699 (fun q0 => (False.elim (q0 u158))) (fun r0 => r0));
    let u163 : (¬ p3956) := (Or.elim h50065 (fun q0 => (False.elim (q0 u136))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u75))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u101))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u159))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u116))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u89))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u4))))))))))))))))));
    let u164 : (¬ p3631) := (Or.elim h63123 (fun q0 => (False.elim (q0 u136))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u75))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u101))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u160))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u126))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u134))))))))))))))))));
    let u165 : (¬ p4242) := (Or.elim h53159 (fun q0 => (False.elim (q0 u159))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u149))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u105))) (fun r4 => (False.elim (r4 u162))))))))))));
    let u166 : (¬ p4594) := (Or.elim h7309 (fun q0 => (False.elim (u163 q0))) (fun r0 => r0));
    let u167 : (¬ p5361) := (Or.elim h9217 (fun q0 => (False.elim (u164 q0))) (fun r0 => r0));
    let u168 : (¬ p5311) := (Or.elim h9061 (fun q0 => (False.elim (u165 q0))) (fun r0 => r0));
    let u169 : p4597 := (Or.elim h7321 (fun q0 => (False.elim (q0 u36))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u166 q1))) (fun r1 => r1))));
    let u170 : p5356 := (Or.elim h9223 (fun q0 => (False.elim (q0 u37))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u167 r1))))));
    let u171 : p5314 := (Or.elim h9073 (fun q0 => (False.elim (q0 u38))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u168 q1))) (fun r1 => r1))));
    let u172 : p2352 := (Or.elim h7315 (fun q0 => q0) (fun r0 => (False.elim (r0 u169))));
    let u173 : p3817 := (Or.elim h9211 (fun q0 => q0) (fun r0 => (False.elim (r0 u170))));
    let u174 : p5315 := (Or.elim h9065 (fun q0 => (False.elim (q0 u171))) (fun r0 => r0));
    let u175 : (¬ p3989) := (Or.elim h40917 (fun q0 => (False.elim (q0 u172))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u76))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u99))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u85))))))))));
    let u176 : (¬ p3246) := (Or.elim h59744 (fun q0 => (False.elim (q0 u66))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u117))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u173))) (fun r3 => (False.elim (r3 u58))))))))));
    let u177 : (¬ p4505) := (Or.elim h7073 (fun q0 => (False.elim (u175 q0))) (fun r0 => r0));
    let u178 : (¬ p5103) := (Or.elim h8615 (fun q0 => (False.elim (u176 q0))) (fun r0 => r0));
    let u179 : p4508 := (Or.elim h7085 (fun q0 => (False.elim (q0 u39))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u177 q1))) (fun r1 => r1))));
    let u180 : p5101 := (Or.elim h8621 (fun q0 => (False.elim (q0 u40))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u178 r1))))));
    let u181 : p2190 := (Or.elim h7078 (fun q0 => q0) (fun r0 => (False.elim (r0 u179))));
    let u182 : p3690 := (Or.elim h8609 (fun q0 => q0) (fun r0 => (False.elim (r0 u180))));
    let u183 : p2373 := (Or.elim h6866 (fun q0 => (False.elim (q0 u181))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u7))))));
    let u184 : (¬ p3880) := (Or.elim h6279 (fun q0 => (False.elim (q0 u181))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u77 r1))))));
    let u185 : (¬ p3497) := (Or.elim h5078 (fun q0 => (False.elim (q0 u181))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => r1))));
    let u186 : (¬ p2417) := (Or.elim h51491 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u182))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u98))) (fun r3 => (False.elim (r3 u85))))))))));
    let u187 : (¬ p3860) := (Or.elim h42140 (fun q0 => (False.elim (q0 u148))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u183))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u123))) (fun r3 => (False.elim (r3 u65))))))))));
    let u188 : (¬ p4606) := (Or.elim h7343 (fun q0 => (False.elim (u184 q0))) (fun r0 => r0));
    let u189 : (¬ p5061) := (Or.elim h8490 (fun q0 => (False.elim (u185 q0))) (fun r0 => r0));
    let u190 : (¬ p4639) := (Or.elim h7418 (fun q0 => (False.elim (u186 q0))) (fun r0 => r0));
    let u191 : (¬ p5238) := (Or.elim h8911 (fun q0 => (False.elim (u187 q0))) (fun r0 => r0));
    let u192 : p4609 := (Or.elim h7355 (fun q0 => (False.elim (q0 u41))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u188 q1))) (fun r1 => r1))));
    let u193 : p5064 := (Or.elim h8502 (fun q0 => (False.elim (q0 u42))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u189 q1))) (fun r1 => r1))));
    let u194 : p4634 := (Or.elim h7424 (fun q0 => (False.elim (q0 u43))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u190 r1))))));
    let u195 : p5241 := (Or.elim h8923 (fun q0 => (False.elim (q0 u44))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u191 q1))) (fun r1 => r1))));
    let u196 : p4355 := (Or.elim h7348 (fun q0 => q0) (fun r0 => (False.elim (r0 u192))));
    let u197 : p3156 := (Or.elim h8496 (fun q0 => q0) (fun r0 => (False.elim (r0 u193))));
    let u198 : p4278 := (Or.elim h7412 (fun q0 => q0) (fun r0 => (False.elim (r0 u194))));
    let u199 : p3449 := (Or.elim h8917 (fun q0 => q0) (fun r0 => (False.elim (r0 u195))));
    let u200 : (¬ p3692) := (Or.elim h54486 (fun q0 => (False.elim (q0 u121))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u147))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u196))) (fun r3 => (False.elim (r3 u65))))))))));
    let u201 : (¬ p3073) := (Or.elim h61025 (fun q0 => (False.elim (q0 u136))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u75))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u101))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u199))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u126))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u198))) (fun r7 => (False.elim (r7 u135))))))))))))))))));
    let u202 : (¬ p5055) := (Or.elim h8473 (fun q0 => (False.elim (u200 q0))) (fun r0 => r0));
    let u203 : (¬ p5003) := (Or.elim h8357 (fun q0 => (False.elim (u201 q0))) (fun r0 => r0));
    let u204 : p5057 := (Or.elim h8485 (fun q0 => (False.elim (q0 u45))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u202 q1))) (fun r1 => r1))));
    let u205 : p5000 := (Or.elim h8363 (fun q0 => (False.elim (q0 u46))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u203 r1))))));
    let u206 : p3146 := (Or.elim h8479 (fun q0 => q0) (fun r0 => (False.elim (r0 u204))));
    let u207 : p4261 := (Or.elim h8351 (fun q0 => q0) (fun r0 => (False.elim (r0 u205))));
    let u208 : (¬ p4340) := (Or.elim h63200 (fun q0 => (False.elim (q0 u206))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u197))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u161))) (fun r3 => (False.elim (r3 u53))))))))));
    (Or.elim h40482 (fun q0 => (False.elim (q0 u207))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u208 q1))) (fun r1 => (False.elim (r1 u174)))))))

theorem step65989 (p2241 p2747 p2748 p2750 p2891 p3369 p3371 p3556 p3583 p3954 p4872 p4873 p4876 p5049 : Prop)
    (h65699 : p4872)
    (h3623 : (¬ p2747) ∨ p2750)
    (h3620 : (¬ p2747) ∨ p2748)
    (h42613 : (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3371) ∨ (¬ p3556))
    (h41389 : (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p5049))
    (h8022 : p3371 ∨ (¬ p4876))
    (h8017 : p3583 ∨ (¬ p4873))
    (h8029 : (¬ p4872) ∨ p4873 ∨ p4876)
    : (¬ p2241) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p5049) ∨ (¬ p2747) ∨ (¬ p3954) ∨ (¬ p3556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4872 := h65699;
    let u8 : p2750 := (Or.elim h3623 (fun q0 => (False.elim (q0 u4))) (fun r0 => r0));
    let u9 : p2748 := (Or.elim h3620 (fun q0 => (False.elim (q0 u4))) (fun r0 => r0));
    let u10 : (¬ p3371) := (Or.elim h42613 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u6))))))))))));
    let u11 : (¬ p3583) := (Or.elim h41389 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3))))))))));
    let u12 : (¬ p4876) := (Or.elim h8022 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : (¬ p4873) := (Or.elim h8017 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    (Or.elim h8029 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u13 q1))) (fun r1 => (False.elim (u12 r1)))))))

theorem step65990 (p2135 p2136 p2142 p2143 p2437 p2440 p2696 p2870 p3055 p3364 p3365 p3556 p3569 p3574 p3876 p4244 p4478 p4784 p4785 p4788 p4882 p4892 p4893 p4896 p5049 : Prop)
    (h65630 : p4892)
    (h65646 : p4478)
    (h65602 : p4784)
    (h63237 : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p3569) ∨ (¬ p4244) ∨ (¬ p4882))
    (h53915 : (¬ p2437) ∨ (¬ p3055) ∨ (¬ p3574) ∨ (¬ p3876))
    (h8068 : p4244 ∨ (¬ p4893))
    (h6855 : (¬ p2143) ∨ (¬ p3556) ∨ p4244)
    (h6408 : p3055 ∨ (¬ p3364) ∨ (¬ p3365))
    (h8080 : (¬ p4892) ∨ p4893 ∨ p4896)
    (h2420 : (¬ p2142) ∨ p2143)
    (h7805 : p3365 ∨ (¬ p4785))
    (h8074 : p2870 ∨ (¬ p4896))
    (h7001 : p2135 ∨ p2142 ∨ (¬ p4478))
    (h7817 : (¬ p4784) ∨ p4785 ∨ p4788)
    (h2406 : (¬ p2135) ∨ p2136)
    (h7811 : p2696 ∨ (¬ p4788))
    (h50242 : (¬ p2136) ∨ (¬ p2696) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p5049))
    : (¬ p2437) ∨ (¬ p3876) ∨ (¬ p4882) ∨ (¬ p5049) ∨ (¬ p3364) ∨ (¬ p3574) ∨ (¬ p2440) ∨ (¬ p3569) ∨ (¬ p3556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4892 := h65630;
    let u10 : p4478 := h65646;
    let u11 : p4784 := h65602;
    let u12 : (¬ p4244) := (Or.elim h63237 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    let u13 : (¬ p3055) := (Or.elim h53915 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u1))))))));
    let u14 : (¬ p4893) := (Or.elim h8068 (fun q0 => (False.elim (u12 q0))) (fun r0 => r0));
    let u15 : (¬ p2143) := (Or.elim h6855 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (False.elim (u12 r1))))));
    let u16 : (¬ p3365) := (Or.elim h6408 (fun q0 => (False.elim (u13 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => r1))));
    let u17 : p4896 := (Or.elim h8080 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u14 q1))) (fun r1 => r1))));
    let u18 : (¬ p2142) := (Or.elim h2420 (fun q0 => q0) (fun r0 => (False.elim (u15 r0))));
    let u19 : (¬ p4785) := (Or.elim h7805 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    let u20 : p2870 := (Or.elim h8074 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    let u21 : p2135 := (Or.elim h7001 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u18 q1))) (fun r1 => (False.elim (r1 u10))))));
    let u22 : p4788 := (Or.elim h7817 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u19 q1))) (fun r1 => r1))));
    let u23 : p2136 := (Or.elim h2406 (fun q0 => (False.elim (q0 u21))) (fun r0 => r0));
    let u24 : p2696 := (Or.elim h7811 (fun q0 => q0) (fun r0 => (False.elim (r0 u22))));
    (Or.elim h50242 (fun q0 => (False.elim (q0 u23))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u24))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u20))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step65991 (p2156 p2192 p2241 p2244 p2247 p2251 p2284 p2307 p2437 p2440 p2563 p2630 p2747 p2748 p2750 p2850 p3016 p3136 p3201 p3364 p3369 p3371 p3556 p3569 p3574 p3583 p3644 p3645 p3646 p3684 p3742 p3872 p3876 p3954 p4031 p4110 p4111 p4186 p4203 p4235 p4256 p4343 p4501 p4510 p4511 p4515 p4519 p4520 p4523 p4533 p4534 p4535 p4537 p4540 p4642 p4643 p4645 p4648 p4649 p4651 p4699 p4700 p4713 p4714 p4716 p4747 p4748 p4751 p4809 p4872 p4873 p4876 p4879 p4880 p4882 p4883 p4970 p4971 p4974 p5047 p5048 p5049 p5050 p5080 p5081 p5084 : Prop)
    (h65784 : p4642)
    (h65673 : p4534)
    (h65780 : p4713)
    (h65653 : p4970)
    (h65606 : p4747)
    (h65567 : p5047)
    (h65795 : p4879)
    (h65548 : p5080)
    (h65881 : p4648)
    (h65556 : p4540)
    (h65804 : p4510)
    (h65699 : p4872)
    (h65865 : p4519)
    (h6734 : (¬ p3556) ∨ p3646 ∨ (¬ p3872))
    (h9440 : (¬ p2563) ∨ (¬ p4110))
    (h7618 : p4110 ∨ (¬ p4714))
    (h7630 : (¬ p4713) ∨ p4714 ∨ p4716)
    (h7622 : p4203 ∨ (¬ p4716))
    (h20348 : (¬ p2156) ∨ (¬ p3556) ∨ (¬ p3872))
    (h23019 : p2156 ∨ (¬ p2563) ∨ (¬ p4031))
    (h7146 : p4031 ∨ (¬ p4537))
    (h7154 : (¬ p4534) ∨ p4535 ∨ p4537)
    (h7144 : p4533 ∨ (¬ p4535))
    (h7584 : p2440 ∨ (¬ p4699))
    (h57213 : (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3646) ∨ (¬ p4203) ∨ (¬ p4533))
    (h8280 : p3016 ∨ (¬ p4974))
    (h8286 : (¬ p4970) ∨ p4971 ∨ p4974)
    (h8274 : p3574 ∨ (¬ p4971))
    (h7582 : (¬ p4699) ∨ p4700)
    (h20312 : (¬ p2563) ∨ (¬ p3872) ∨ (¬ p4235))
    (h7429 : p4235 ∨ (¬ p4643))
    (h7441 : (¬ p4642) ∨ p4643 ∨ p4645)
    (h7433 : p3569 ∨ (¬ p4645))
    (h3623 : (¬ p2747) ∨ p2750)
    (h3620 : (¬ p2747) ∨ p2748)
    (h7857 : p4111 ∨ (¬ p4809))
    (h35728 : (¬ p2630) ∨ (¬ p2748) ∨ (¬ p4111))
    (h19996 : (¬ p2748) ∨ (¬ p3136) ∨ (¬ p4111) ∨ (¬ p4700))
    (h7721 : p2630 ∨ (¬ p4751))
    (h8462 : p3136 ∨ (¬ p5050))
    (h7727 : (¬ p4747) ∨ p4748 ∨ p4751)
    (h8468 : (¬ p5047) ∨ p5048 ∨ p5050)
    (h7713 : p3364 ∨ (¬ p4748))
    (h7714 : p4343 ∨ (¬ p4748))
    (h8457 : (¬ p5048) ∨ p5049)
    (h6594 : (¬ p2440) ∨ p3684 ∨ (¬ p4343))
    (h19857 : (¬ p2440) ∨ (¬ p2850) ∨ (¬ p4343))
    (h51291 : (¬ p3201) ∨ (¬ p3556) ∨ (¬ p3569) ∨ (¬ p3684) ∨ (¬ p4533))
    (h8040 : p2850 ∨ (¬ p4883))
    (h8558 : p3201 ∨ (¬ p5084))
    (h8046 : (¬ p4879) ∨ p4880 ∨ p4883)
    (h8564 : (¬ p5080) ∨ p5081 ∨ p5084)
    (h8036 : (¬ p4880) ∨ p4882)
    (h8552 : p3876 ∨ (¬ p5081))
    (h65990 : (¬ p2437) ∨ (¬ p3876) ∨ (¬ p4882) ∨ (¬ p5049) ∨ (¬ p3364) ∨ (¬ p3574) ∨ (¬ p2440) ∨ (¬ p3569) ∨ (¬ p3556))
    (h7453 : p2437 ∨ (¬ p4651))
    (h7459 : (¬ p4648) ∨ p4649 ∨ p4651)
    (h7447 : p3742 ∨ (¬ p4649))
    (h43271 : (¬ p2247) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4111))
    (h6402 : (¬ p3742) ∨ (¬ p4186) ∨ p4256)
    (h2625 : (¬ p2244) ∨ p2247)
    (h65988 : (¬ p4511) ∨ (¬ p4256) ∨ (¬ p4809) ∨ (¬ p4699) ∨ (¬ p4501) ∨ (¬ p3644) ∨ (¬ p2307) ∨ (¬ p2563) ∨ (¬ p2747) ∨ (¬ p3954) ∨ (¬ p2284) ∨ (¬ p3872) ∨ (¬ p3556))
    (h7159 : p2244 ∨ p2251 ∨ (¬ p4540))
    (h7102 : (¬ p4510) ∨ p4511 ∨ p4515)
    (h2639 : p2241 ∨ (¬ p2251))
    (h7096 : p2192 ∨ (¬ p4515))
    (h41389 : (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p5049))
    (h5323 : (¬ p2192) ∨ (¬ p3645) ∨ (¬ p3646))
    (h8017 : p3583 ∨ (¬ p4873))
    (h7111 : p3645 ∨ (¬ p4523))
    (h8029 : (¬ p4872) ∨ p4873 ∨ p4876)
    (h7119 : (¬ p4519) ∨ p4520 ∨ p4523)
    (h8022 : p3371 ∨ (¬ p4876))
    (h7105 : p3369 ∨ (¬ p4520))
    (h53017 : (¬ p2192) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3369) ∨ (¬ p3371) ∨ (¬ p3646))
    : (¬ p4809) ∨ (¬ p4699) ∨ (¬ p4501) ∨ (¬ p3644) ∨ (¬ p4186) ∨ (¬ p2307) ∨ (¬ p2563) ∨ (¬ p2747) ∨ (¬ p3954) ∨ (¬ p2284) ∨ (¬ p3872) ∨ (¬ p3556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4809 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4642 := h65784;
    let u13 : p4534 := h65673;
    let u14 : p4713 := h65780;
    let u15 : p4970 := h65653;
    let u16 : p4747 := h65606;
    let u17 : p5047 := h65567;
    let u18 : p4879 := h65795;
    let u19 : p5080 := h65548;
    let u20 : p4648 := h65881;
    let u21 : p4540 := h65556;
    let u22 : p4510 := h65804;
    let u23 : p4872 := h65699;
    let u24 : p4519 := h65865;
    let u25 : p3646 := (Or.elim h6734 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u10))))));
    let u26 : (¬ p4110) := (Or.elim h9440 (fun q0 => (False.elim (q0 u6))) (fun r0 => r0));
    let u27 : (¬ p4714) := (Or.elim h7618 (fun q0 => (False.elim (u26 q0))) (fun r0 => r0));
    let u28 : p4716 := (Or.elim h7630 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u27 q1))) (fun r1 => r1))));
    let u29 : p4203 := (Or.elim h7622 (fun q0 => q0) (fun r0 => (False.elim (r0 u28))));
    let u30 : (¬ p2156) := (Or.elim h20348 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (False.elim (r1 u10))))));
    let u31 : (¬ p4031) := (Or.elim h23019 (fun q0 => (False.elim (u30 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => r1))));
    let u32 : (¬ p4537) := (Or.elim h7146 (fun q0 => (False.elim (u31 q0))) (fun r0 => r0));
    let u33 : p4535 := (Or.elim h7154 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u32 r1))))));
    let u34 : p4533 := (Or.elim h7144 (fun q0 => q0) (fun r0 => (False.elim (r0 u33))));
    let u35 : p2440 := (Or.elim h7584 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u36 : (¬ p3016) := (Or.elim h57213 (fun q0 => (False.elim (q0 u35))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u25))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u29))) (fun r3 => (False.elim (r3 u34))))))))));
    let u37 : (¬ p4974) := (Or.elim h8280 (fun q0 => (False.elim (u36 q0))) (fun r0 => r0));
    let u38 : p4971 := (Or.elim h8286 (fun q0 => (False.elim (q0 u15))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u37 r1))))));
    let u39 : p3574 := (Or.elim h8274 (fun q0 => q0) (fun r0 => (False.elim (r0 u38))));
    let u40 : p4700 := (Or.elim h7582 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u41 : (¬ p4235) := (Or.elim h20312 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => r1))));
    let u42 : (¬ p4643) := (Or.elim h7429 (fun q0 => (False.elim (u41 q0))) (fun r0 => r0));
    let u43 : p4645 := (Or.elim h7441 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u42 q1))) (fun r1 => r1))));
    let u44 : p3569 := (Or.elim h7433 (fun q0 => q0) (fun r0 => (False.elim (r0 u43))));
    let u45 : p2750 := (Or.elim h3623 (fun q0 => (False.elim (q0 u7))) (fun r0 => r0));
    let u46 : p2748 := (Or.elim h3620 (fun q0 => (False.elim (q0 u7))) (fun r0 => r0));
    let u47 : p4111 := (Or.elim h7857 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u48 : (¬ p2630) := (Or.elim h35728 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u46))) (fun r1 => (False.elim (r1 u47))))));
    let u49 : (¬ p3136) := (Or.elim h19996 (fun q0 => (False.elim (q0 u46))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u47))) (fun r2 => (False.elim (r2 u40))))))));
    let u50 : (¬ p4751) := (Or.elim h7721 (fun q0 => (False.elim (u48 q0))) (fun r0 => r0));
    let u51 : (¬ p5050) := (Or.elim h8462 (fun q0 => (False.elim (u49 q0))) (fun r0 => r0));
    let u52 : p4748 := (Or.elim h7727 (fun q0 => (False.elim (q0 u16))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u50 r1))))));
    let u53 : p5048 := (Or.elim h8468 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u51 r1))))));
    let u54 : p3364 := (Or.elim h7713 (fun q0 => q0) (fun r0 => (False.elim (r0 u52))));
    let u55 : p4343 := (Or.elim h7714 (fun q0 => q0) (fun r0 => (False.elim (r0 u52))));
    let u56 : p5049 := (Or.elim h8457 (fun q0 => (False.elim (q0 u53))) (fun r0 => r0));
    let u57 : p3684 := (Or.elim h6594 (fun q0 => (False.elim (q0 u35))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u55))))));
    let u58 : (¬ p2850) := (Or.elim h19857 (fun q0 => (False.elim (q0 u35))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u55))))));
    let u59 : (¬ p3201) := (Or.elim h51291 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u44))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u57))) (fun r3 => (False.elim (r3 u34))))))))));
    let u60 : (¬ p4883) := (Or.elim h8040 (fun q0 => (False.elim (u58 q0))) (fun r0 => r0));
    let u61 : (¬ p5084) := (Or.elim h8558 (fun q0 => (False.elim (u59 q0))) (fun r0 => r0));
    let u62 : p4880 := (Or.elim h8046 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u60 r1))))));
    let u63 : p5081 := (Or.elim h8564 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u61 r1))))));
    let u64 : p4882 := (Or.elim h8036 (fun q0 => (False.elim (q0 u62))) (fun r0 => r0));
    let u65 : p3876 := (Or.elim h8552 (fun q0 => q0) (fun r0 => (False.elim (r0 u63))));
    let u66 : (¬ p2437) := (Or.elim h65990 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u65))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u64))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u56))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u54))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u39))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u35))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u44))) (fun r7 => (False.elim (r7 u11))))))))))))))))));
    let u67 : (¬ p4651) := (Or.elim h7453 (fun q0 => (False.elim (u66 q0))) (fun r0 => r0));
    let u68 : p4649 := (Or.elim h7459 (fun q0 => (False.elim (q0 u20))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u67 r1))))));
    let u69 : p3742 := (Or.elim h7447 (fun q0 => q0) (fun r0 => (False.elim (r0 u68))));
    let u70 : (¬ p2247) := (Or.elim h43271 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u69))) (fun r2 => (False.elim (r2 u47))))))));
    let u71 : p4256 := (Or.elim h6402 (fun q0 => (False.elim (q0 u69))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => r1))));
    let u72 : (¬ p2244) := (Or.elim h2625 (fun q0 => q0) (fun r0 => (False.elim (u70 r0))));
    let u73 : (¬ p4511) := (Or.elim h65988 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u71))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11))))))))))))))))))))))))));
    let u74 : p2251 := (Or.elim h7159 (fun q0 => (False.elim (u72 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u21))))));
    let u75 : p4515 := (Or.elim h7102 (fun q0 => (False.elim (q0 u22))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u73 q1))) (fun r1 => r1))));
    let u76 : p2241 := (Or.elim h2639 (fun q0 => q0) (fun r0 => (False.elim (r0 u74))));
    let u77 : p2192 := (Or.elim h7096 (fun q0 => q0) (fun r0 => (False.elim (r0 u75))));
    let u78 : (¬ p3583) := (Or.elim h41389 (fun q0 => (False.elim (q0 u76))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u46))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u56))))))))));
    let u79 : (¬ p3645) := (Or.elim h5323 (fun q0 => (False.elim (q0 u77))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u25))))));
    let u80 : (¬ p4873) := (Or.elim h8017 (fun q0 => (False.elim (u78 q0))) (fun r0 => r0));
    let u81 : (¬ p4523) := (Or.elim h7111 (fun q0 => (False.elim (u79 q0))) (fun r0 => r0));
    let u82 : p4876 := (Or.elim h8029 (fun q0 => (False.elim (q0 u23))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u80 q1))) (fun r1 => r1))));
    let u83 : p4520 := (Or.elim h7119 (fun q0 => (False.elim (q0 u24))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u81 r1))))));
    let u84 : p3371 := (Or.elim h8022 (fun q0 => q0) (fun r0 => (False.elim (r0 u82))));
    let u85 : p3369 := (Or.elim h7105 (fun q0 => q0) (fun r0 => (False.elim (r0 u83))));
    (Or.elim h53017 (fun q0 => (False.elim (q0 u77))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u76))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u45))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u85))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u84))) (fun r4 => (False.elim (r4 u25)))))))))))))

theorem step65992 (p2135 p2136 p2142 p2143 p2696 p2870 p3556 p4478 p5049 : Prop)
    (h65646 : p4478)
    (h6884 : (¬ p2143) ∨ (¬ p2870) ∨ (¬ p3556))
    (h50242 : (¬ p2136) ∨ (¬ p2696) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p5049))
    (h2420 : (¬ p2142) ∨ p2143)
    (h2406 : (¬ p2135) ∨ p2136)
    (h7001 : p2135 ∨ p2142 ∨ (¬ p4478))
    : (¬ p2870) ∨ (¬ p2696) ∨ (¬ p5049) ∨ (¬ p3556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4478 := h65646;
    let u5 : (¬ p2143) := (Or.elim h6884 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3))))));
    let u6 : (¬ p2136) := (Or.elim h50242 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2))))))))));
    let u7 : (¬ p2142) := (Or.elim h2420 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u8 : (¬ p2135) := (Or.elim h2406 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h7001 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step65993 (p878 p884 p3020 : Prop)
    (h4163 : (¬ p878) ∨ p3020)
    (h4164 : (¬ p884) ∨ p3020)
    (h963 : p878 ∨ p884)
    : p3020 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3020) := (fun h => hn h);
    let u1 : (¬ p878) := (Or.elim h4163 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p884) := (Or.elim h4164 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h963 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65994 (p3020 p3021 : Prop)
    (h65993 : p3020)
    (h4181 : (¬ p3020) ∨ p3021)
    : p3021 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3021) := (fun h => hn h);
    let u1 : p3020 := h65993;
    (Or.elim h4181 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65995 (p3021 p4977 : Prop)
    (h65994 : p3021)
    (h8292 : (¬ p3021) ∨ p4977)
    : p4977 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4977) := (fun h => hn h);
    let u1 : p3021 := h65994;
    (Or.elim h8292 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65996 (p398 p404 p2511 : Prop)
    (h3154 : (¬ p398) ∨ p2511)
    (h3155 : (¬ p404) ∨ p2511)
    (h443 : p398 ∨ p404)
    : p2511 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2511) := (fun h => hn h);
    let u1 : (¬ p398) := (Or.elim h3154 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p404) := (Or.elim h3155 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h443 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step65997 (p2511 p2512 : Prop)
    (h65996 : p2511)
    (h3172 : (¬ p2511) ∨ p2512)
    : p2512 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2512) := (fun h => hn h);
    let u1 : p2511 := h65996;
    (Or.elim h3172 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65998 (p2512 p4682 : Prop)
    (h65997 : p2512)
    (h7563 : (¬ p2512) ∨ p4682)
    : p4682 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4682) := (fun h => hn h);
    let u1 : p2512 := h65997;
    (Or.elim h7563 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step65999 (p4682 p5865 : Prop)
    (h65998 : p4682)
    (h12202 : (¬ p4682) ∨ p5865)
    : p5865 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5865) := (fun h => hn h);
    let u1 : p4682 := h65998;
    (Or.elim h12202 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step66003 (p2252 p2427 p2563 p2750 p2819 p2881 p2891 p2901 p2952 p3051 p3054 p3093 p3548 p3554 p3556 p3570 p3646 p3952 p3954 p4024 p4133 p4173 p4244 p4320 p4533 p4629 p4882 p4899 p4900 p4903 p4907 p4908 p4912 p4915 p4916 p4918 p4982 p4983 p4987 : Prop)
    (h65681 : p4907)
    (h65642 : p4982)
    (h65649 : p4899)
    (h65729 : p4915)
    (h43934 : (¬ p2563) ∨ (¬ p2891) ∨ (¬ p3054) ∨ (¬ p4173) ∨ (¬ p4244))
    (h51441 : (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4244) ∨ (¬ p4882))
    (h8110 : p2891 ∨ (¬ p4912))
    (h8321 : p3051 ∨ (¬ p4987))
    (h8116 : (¬ p4907) ∨ p4908 ∨ p4912)
    (h8327 : (¬ p4982) ∨ p4983 ∨ p4987)
    (h8102 : p3554 ∨ (¬ p4908))
    (h8315 : p3556 ∨ (¬ p4983))
    (h40975 : (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4629))
    (h63244 : (¬ p2563) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3952) ∨ (¬ p4533))
    (h8092 : p2881 ∨ (¬ p4903))
    (h8127 : p2901 ∨ (¬ p4918))
    (h8098 : (¬ p4899) ∨ p4900 ∨ p4903)
    (h8133 : (¬ p4915) ∨ p4916 ∨ p4918)
    (h8086 : p3570 ∨ (¬ p4900))
    (h8121 : p4320 ∨ (¬ p4916))
    (h55177 : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2819) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3570) ∨ (¬ p3954) ∨ (¬ p4024) ∨ (¬ p4133) ∨ (¬ p4320))
    : (¬ p4244) ∨ (¬ p2819) ∨ (¬ p3548) ∨ (¬ p4133) ∨ (¬ p4024) ∨ (¬ p3054) ∨ (¬ p4533) ∨ (¬ p3646) ∨ (¬ p3093) ∨ (¬ p2952) ∨ (¬ p2750) ∨ (¬ p4173) ∨ (¬ p4629) ∨ (¬ p2252) ∨ (¬ p3952) ∨ (¬ p2427) ∨ (¬ p2563) ∨ (¬ p3954) ∨ (¬ p4882) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4244 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))));
    let u19 : p4907 := h65681;
    let u20 : p4982 := h65642;
    let u21 : p4899 := h65649;
    let u22 : p4915 := h65729;
    let u23 : (¬ p2891) := (Or.elim h43934 (fun q0 => (False.elim (q0 u16))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (False.elim (r3 u0))))))))));
    let u24 : (¬ p3051) := (Or.elim h51441 (fun q0 => (False.elim (q0 u16))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u18))))))))));
    let u25 : (¬ p4912) := (Or.elim h8110 (fun q0 => (False.elim (u23 q0))) (fun r0 => r0));
    let u26 : (¬ p4987) := (Or.elim h8321 (fun q0 => (False.elim (u24 q0))) (fun r0 => r0));
    let u27 : p4908 := (Or.elim h8116 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u25 r1))))));
    let u28 : p4983 := (Or.elim h8327 (fun q0 => (False.elim (q0 u20))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u26 r1))))));
    let u29 : p3554 := (Or.elim h8102 (fun q0 => q0) (fun r0 => (False.elim (r0 u27))));
    let u30 : p3556 := (Or.elim h8315 (fun q0 => q0) (fun r0 => (False.elim (r0 u28))));
    let u31 : (¬ p2881) := (Or.elim h40975 (fun q0 => (False.elim (q0 u15))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u29))) (fun r3 => (False.elim (r3 u12))))))))));
    let u32 : (¬ p2901) := (Or.elim h63244 (fun q0 => (False.elim (q0 u16))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u30))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (False.elim (r3 u6))))))))));
    let u33 : (¬ p4903) := (Or.elim h8092 (fun q0 => (False.elim (u31 q0))) (fun r0 => r0));
    let u34 : (¬ p4918) := (Or.elim h8127 (fun q0 => (False.elim (u32 q0))) (fun r0 => r0));
    let u35 : p4900 := (Or.elim h8098 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u33 r1))))));
    let u36 : p4916 := (Or.elim h8133 (fun q0 => (False.elim (q0 u22))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u34 r1))))));
    let u37 : p3570 := (Or.elim h8086 (fun q0 => q0) (fun r0 => (False.elim (r0 u35))));
    let u38 : p4320 := (Or.elim h8121 (fun q0 => q0) (fun r0 => (False.elim (r0 u36))));
    (Or.elim h55177 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u37))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u17))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u38)))))))))))))))))))))

theorem step66004 (p2299 p2528 p2657 p3644 p3742 p3875 p4348 p4712 p4920 p4921 p4923 : Prop)
    (h65980 : p4920)
    (h49237 : (¬ p2299) ∨ (¬ p2528) ∨ (¬ p3875) ∨ (¬ p4348) ∨ (¬ p4712))
    (h44724 : (¬ p2657) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4348))
    (h8143 : p3875 ∨ (¬ p4923))
    (h8138 : p3644 ∨ (¬ p4921))
    (h8150 : (¬ p4920) ∨ p4921 ∨ p4923)
    : (¬ p4348) ∨ (¬ p2528) ∨ (¬ p2299) ∨ (¬ p2657) ∨ (¬ p3742) ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4348 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4920 := h65980;
    let u7 : (¬ p3875) := (Or.elim h49237 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5))))))))));
    let u8 : (¬ p3644) := (Or.elim h44724 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0))))))));
    let u9 : (¬ p4923) := (Or.elim h8143 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u10 : (¬ p4921) := (Or.elim h8138 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    (Or.elim h8150 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (False.elim (u9 r1)))))))

theorem step66005 (p2143 p2166 p2177 p2187 p2192 p2210 p2220 p2230 p2241 p2244 p2247 p2251 p2252 p2253 p2254 p2274 p2284 p2299 p2363 p2396 p2406 p2417 p2427 p2437 p2440 p2449 p2459 p2509 p2518 p2528 p2534 p2563 p2588 p2619 p2630 p2651 p2654 p2657 p2661 p2685 p2717 p2740 p2741 p2747 p2748 p2750 p2753 p2761 p2774 p2777 p2780 p2784 p2797 p2819 p2829 p2850 p2860 p2870 p2881 p2901 p2911 p2946 p2949 p2951 p2952 p2956 p2992 p2995 p3051 p3054 p3063 p3073 p3083 p3093 p3125 p3136 p3146 p3246 p3266 p3309 p3319 p3322 p3323 p3399 p3412 p3449 p3452 p3461 p3483 p3527 p3548 p3549 p3555 p3574 p3576 p3588 p3591 p3644 p3645 p3646 p3659 p3662 p3688 p3690 p3692 p3694 p3696 p3697 p3742 p3744 p3745 p3868 p3872 p3873 p3880 p3917 p3920 p3923 p3945 p3947 p3952 p3954 p3955 p3956 p3957 p3969 p3989 p4024 p4026 p4037 p4110 p4111 p4112 p4116 p4133 p4140 p4153 p4154 p4173 p4191 p4193 p4200 p4202 p4203 p4235 p4241 p4243 p4244 p4256 p4261 p4278 p4316 p4317 p4320 p4330 p4343 p4344 p4347 p4348 p4355 p4358 p4381 p4384 p4441 p4444 p4452 p4490 p4491 p4492 p4495 p4499 p4500 p4501 p4502 p4504 p4505 p4508 p4510 p4511 p4512 p4515 p4519 p4520 p4523 p4526 p4527 p4530 p4533 p4534 p4535 p4537 p4540 p4557 p4558 p4561 p4562 p4565 p4593 p4594 p4597 p4599 p4600 p4602 p4605 p4606 p4609 p4610 p4618 p4619 p4620 p4622 p4626 p4627 p4629 p4630 p4633 p4634 p4639 p4642 p4643 p4645 p4646 p4648 p4649 p4651 p4654 p4655 p4659 p4664 p4665 p4667 p4682 p4683 p4686 p4691 p4692 p4694 p4698 p4699 p4700 p4703 p4706 p4707 p4709 p4712 p4713 p4714 p4716 p4732 p4738 p4739 p4743 p4747 p4748 p4751 p4762 p4775 p4776 p4778 p4780 p4791 p4792 p4795 p4798 p4799 p4803 p4809 p4815 p4821 p4822 p4827 p4831 p4833 p4839 p4840 p4842 p4844 p4855 p4856 p4860 p4864 p4865 p4868 p4872 p4873 p4874 p4876 p4879 p4880 p4882 p4883 p4886 p4887 p4890 p4892 p4893 p4896 p4899 p4900 p4901 p4903 p4915 p4916 p4918 p4920 p4921 p4923 p4931 p4955 p4956 p4958 p4991 p4992 p4996 p4999 p5000 p5003 p5006 p5007 p5010 p5013 p5014 p5019 p5041 p5042 p5044 p5047 p5048 p5050 p5054 p5055 p5057 p5100 p5101 p5103 p5114 p5115 p5120 p5139 p5140 p5143 p5146 p5147 p5151 p5188 p5189 p5192 p5194 p5245 p5246 p5251 p5262 p5263 p5268 p5272 p5273 p5277 p5303 p5304 p5306 p5499 p5500 p5503 p5506 p5554 p5555 p5558 p5561 p5562 p5566 p5567 p5568 p5571 : Prop)
    (h65784 : p4642)
    (h65780 : p4713)
    (h65853 : p4706)
    (h65733 : p4561)
    (h65844 : p4698)
    (h65661 : p4955)
    (h65556 : p4540)
    (h65881 : p4648)
    (h65800 : p4626)
    (h65804 : p4510)
    (h65613 : p4815)
    (h65865 : p4519)
    (h65500 : p5188)
    (h65520 : p5139)
    (h65606 : p4747)
    (h65567 : p5047)
    (h65827 : p4839)
    (h65709 : p4775)
    (h65836 : p4762)
    (h65687 : p4931)
    (h65699 : p4872)
    (h65583 : p5013)
    (h65673 : p4534)
    (h65795 : p4879)
    (h65741 : p4886)
    (h65716 : p4864)
    (h65622 : p4791)
    (h65771 : p4605)
    (h65748 : p4499)
    (h65923 : p4833)
    (h65626 : p4798)
    (h65998 : p4682)
    (h65448 : p5303)
    (h65895 : p4593)
    (h65791 : p4504)
    (h65634 : p5006)
    (h65638 : p4991)
    (h65810 : p4855)
    (h65758 : p4599)
    (h65597 : p4999)
    (h65630 : p4892)
    (h65729 : p4915)
    (h65649 : p4899)
    (h65540 : p5100)
    (h65720 : p4618)
    (h65944 : p4654)
    (h65571 : p5041)
    (h65460 : p5272)
    (h65516 : p5146)
    (h65464 : p5262)
    (h65775 : p4691)
    (h65694 : p4664)
    (h65980 : p4920)
    (h65848 : p4633)
    (h65587 : p4821)
    (h65528 : p5114)
    (h65356 : p5554)
    (h65472 : p5245)
    (h65376 : p5499)
    (h65352 : p5566)
    (h65705 : p4526)
    (h65617 : p4738)
    (h65690 : p4490)
    (h65563 : p5054)
    (h7857 : p4111 ∨ (¬ p4809))
    (h7856 : p4116 ∨ (¬ p4809))
    (h7208 : p2274 ∨ (¬ p4557))
    (h9440 : (¬ p2563) ∨ (¬ p4110))
    (h7618 : p4110 ∨ (¬ p4714))
    (h7630 : (¬ p4713) ∨ p4714 ∨ p4716)
    (h7622 : p4203 ∨ (¬ p4716))
    (h6680 : (¬ p2274) ∨ (¬ p2588) ∨ (¬ p4203))
    (h7601 : p2588 ∨ (¬ p4707))
    (h7613 : (¬ p4706) ∨ p4707 ∨ p4709)
    (h7609 : (¬ p4709) ∨ p4712)
    (h7606 : p3920 ∨ (¬ p4709))
    (h7207 : p3872 ∨ (¬ p4557))
    (h20312 : (¬ p2563) ∨ (¬ p3872) ∨ (¬ p4235))
    (h7429 : p4235 ∨ (¬ p4643))
    (h7441 : (¬ p4642) ∨ p4643 ∨ p4645)
    (h7436 : (¬ p4645) ∨ p4646)
    (h5739 : p2427 ∨ (¬ p2563) ∨ (¬ p3872))
    (h7209 : (¬ p4557) ∨ p4558)
    (h7206 : p4140 ∨ (¬ p4557))
    (h7681 : p3954 ∨ (¬ p4732))
    (h7680 : p2753 ∨ (¬ p4732))
    (h7679 : p3873 ∨ (¬ p4732))
    (h7226 : p2284 ∨ (¬ p4565))
    (h6533 : p2284 ∨ (¬ p2563) ∨ (¬ p4241))
    (h7232 : (¬ p4561) ∨ p4562 ∨ p4565)
    (h7588 : p4241 ∨ (¬ p4703))
    (h7218 : p4153 ∨ (¬ p4562))
    (h7219 : p3745 ∨ (¬ p4562))
    (h7220 : p3952 ∨ (¬ p4562))
    (h7596 : (¬ p4698) ∨ p4699 ∨ p4703)
    (h7582 : (¬ p4699) ∨ p4700)
    (h7584 : p2440 ∨ (¬ p4699))
    (h27082 : p3662 ∨ (¬ p4111) ∨ (¬ p4700))
    (h20017 : (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4700))
    (h46112 : (¬ p2247) ∨ (¬ p2563) ∨ (¬ p3952) ∨ (¬ p4111) ∨ (¬ p4700))
    (h52915 : (¬ p2437) ∨ (¬ p2563) ∨ (¬ p3952) ∨ (¬ p4646) ∨ (¬ p4700))
    (h20082 : (¬ p2406) ∨ (¬ p2440) ∨ (¬ p4116))
    (h6201 : (¬ p3662) ∨ (¬ p4153) ∨ p4154)
    (h8246 : p2992 ∨ (¬ p4958))
    (h2625 : (¬ p2244) ∨ p2247)
    (h7453 : p2437 ∨ (¬ p4651))
    (h7401 : p2406 ∨ (¬ p4630))
    (h8252 : (¬ p4955) ∨ p4956 ∨ p4958)
    (h7159 : p2244 ∨ p2251 ∨ (¬ p4540))
    (h7459 : (¬ p4648) ∨ p4649 ∨ p4651)
    (h7407 : (¬ p4626) ∨ p4627 ∨ p4630)
    (h8239 : p3412 ∨ (¬ p4956))
    (h2637 : (¬ p2251) ∨ p2252)
    (h2638 : (¬ p2251) ∨ p2253)
    (h2639 : p2241 ∨ (¬ p2251))
    (h2640 : (¬ p2251) ∨ p2254)
    (h7445 : p4112 ∨ (¬ p4649))
    (h7447 : p3742 ∨ (¬ p4649))
    (h7393 : p4202 ∨ (¬ p4627))
    (h7397 : (¬ p4627) ∨ p4629)
    (h6237 : (¬ p3412) ∨ (¬ p3952) ∨ p4173)
    (h20007 : (¬ p2192) ∨ (¬ p3412) ∨ (¬ p3952))
    (h6267 : (¬ p2241) ∨ (¬ p2741) ∨ (¬ p3954))
    (h6413 : p3574 ∨ (¬ p3742) ∨ (¬ p3920))
    (h42642 : (¬ p2241) ∨ (¬ p2563) ∨ (¬ p3555) ∨ (¬ p4173))
    (h7096 : p2192 ∨ (¬ p4515))
    (h3606 : (¬ p2740) ∨ p2741)
    (h7107 : p3555 ∨ (¬ p4520))
    (h6295 : (¬ p3452) ∨ p3555 ∨ (¬ p4202))
    (h7102 : (¬ p4510) ∨ p4511 ∨ p4515)
    (h7875 : p2740 ∨ p2747 ∨ (¬ p4815))
    (h7119 : (¬ p4519) ∨ p4520 ∨ p4523)
    (h8799 : p3452 ∨ (¬ p5189))
    (h7088 : (¬ p4511) ∨ p4512)
    (h7089 : p3957 ∨ (¬ p4511))
    (h3620 : (¬ p2747) ∨ p2748)
    (h3623 : (¬ p2747) ∨ p2750)
    (h7111 : p3645 ∨ (¬ p4523))
    (h7113 : p2210 ∨ (¬ p4523))
    (h8811 : (¬ p5188) ∨ p5189 ∨ p5192)
    (h61082 : (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p4629))
    (h35728 : (¬ p2630) ∨ (¬ p2748) ∨ (¬ p4111))
    (h19996 : (¬ p2748) ∨ (¬ p3136) ∨ (¬ p4111) ∨ (¬ p4700))
    (h33848 : (¬ p2748) ∨ (¬ p2797) ∨ (¬ p4154))
    (h38656 : (¬ p2685) ∨ (¬ p2748) ∨ (¬ p4111) ∨ (¬ p4112))
    (h51595 : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p4111))
    (h49229 : (¬ p2253) ∨ (¬ p2750) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3954))
    (h29892 : (¬ p2210) ∨ (¬ p3954) ∨ (¬ p4874))
    (h41941 : (¬ p2210) ∨ (¬ p2563) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4629))
    (h8807 : (¬ p5192) ∨ p5194)
    (h8705 : p3549 ∨ (¬ p5140))
    (h7721 : p2630 ∨ (¬ p4751))
    (h8462 : p3136 ∨ (¬ p5050))
    (h7953 : p2797 ∨ (¬ p4844))
    (h7794 : p2685 ∨ (¬ p4780))
    (h3449 : p2651 ∨ (¬ p2661))
    (h4042 : p2946 ∨ (¬ p2956))
    (h8015 : (¬ p4873) ∨ p4874)
    (h8386 : p3591 ∨ (¬ p5014))
    (h59873 : (¬ p2230) ∨ (¬ p2563) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p5194))
    (h8717 : (¬ p5139) ∨ p5140 ∨ p5143)
    (h7727 : (¬ p4747) ∨ p4748 ∨ p4751)
    (h8468 : (¬ p5047) ∨ p5048 ∨ p5050)
    (h7959 : (¬ p4839) ∨ p4840 ∨ p4844)
    (h7800 : (¬ p4775) ∨ p4776 ∨ p4780)
    (h7750 : p2654 ∨ p2661 ∨ (¬ p4762))
    (h8182 : p2949 ∨ p2956 ∨ (¬ p4931))
    (h8029 : (¬ p4872) ∨ p4873 ∨ p4876)
    (h8398 : (¬ p5013) ∨ p5014 ∨ p5019)
    (h7148 : p2230 ∨ (¬ p4537))
    (h8710 : p4452 ∨ (¬ p5143))
    (h8711 : p3309 ∨ (¬ p5143))
    (h7714 : p4343 ∨ (¬ p4748))
    (h8455 : p4316 ∨ (¬ p5048))
    (h7948 : (¬ p4840) ∨ p4842)
    (h7789 : (¬ p4776) ∨ p4778)
    (h3435 : (¬ p2654) ∨ p2657)
    (h4027 : (¬ p2949) ∨ p2951)
    (h4028 : (¬ p2949) ∨ p2952)
    (h8021 : p4243 ∨ (¬ p4876))
    (h8392 : p3093 ∨ (¬ p5019))
    (h7154 : (¬ p4534) ∨ p4535 ∨ p4537)
    (h19857 : (¬ p2440) ∨ (¬ p2850) ∨ (¬ p4343))
    (h20521 : (¬ p2860) ∨ (¬ p3952) ∨ (¬ p4316))
    (h49201 : (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4842))
    (h41580 : (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4778))
    (h5865 : (¬ p2951) ∨ p3646 ∨ (¬ p3952))
    (h44033 : (¬ p2563) ∨ (¬ p2952) ∨ (¬ p3880) ∨ (¬ p3952))
    (h17146 : p2143 ∨ (¬ p3645) ∨ (¬ p4243))
    (h25108 : (¬ p3093) ∨ p3399 ∨ (¬ p4452))
    (h52571 : (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3954))
    (h7144 : p4533 ∨ (¬ p4535))
    (h8040 : p2850 ∨ (¬ p4883))
    (h8057 : p2860 ∨ (¬ p4890))
    (h8000 : p3688 ∨ (¬ p4865))
    (h7823 : p3588 ∨ (¬ p4792))
    (h7343 : p3880 ∨ (¬ p4606))
    (h7062 : p2177 ∨ (¬ p4502))
    (h8046 : (¬ p4879) ∨ p4880 ∨ p4883)
    (h8063 : (¬ p4886) ∨ p4887 ∨ p4890)
    (h8012 : (¬ p4864) ∨ p4865 ∨ p4868)
    (h7835 : (¬ p4791) ∨ p4792 ∨ p4795)
    (h7355 : (¬ p4605) ∨ p4606 ∨ p4609)
    (h7068 : (¬ p4499) ∨ p4500 ∨ p4502)
    (h8032 : p3054 ∨ (¬ p4880))
    (h8049 : p4193 ∨ (¬ p4887))
    (h8004 : p4024 ∨ (¬ p4868))
    (h8006 : p2829 ∨ (¬ p4868))
    (h7827 : p3576 ∨ (¬ p4795))
    (h7348 : p4355 ∨ (¬ p4609))
    (h7350 : (¬ p4609) ∨ p4610)
    (h7054 : p3955 ∨ (¬ p4500))
    (h7056 : p2299 ∨ (¬ p4500))
    (h7057 : (¬ p4500) ∨ p4501)
    (h7058 : p4133 ∨ (¬ p4500))
    (h42276 : (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3873))
    (h42709 : (¬ p2299) ∨ (¬ p2717) ∨ (¬ p3399) ∨ (¬ p3576) ∨ (¬ p3954))
    (h41927 : (¬ p2518) ∨ (¬ p2563) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4610))
    (h60034 : (¬ p2299) ∨ (¬ p3093) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4452))
    (h50065 : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p3954) ∨ (¬ p3956) ∨ (¬ p4501))
    (h60774 : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p3989) ∨ (¬ p4501))
    (h3683 : (¬ p2777) ∨ p2780)
    (h7846 : p2717 ∨ (¬ p4803))
    (h7556 : p2518 ∨ (¬ p4686))
    (h9044 : p3527 ∨ (¬ p5306))
    (h7309 : p3956 ∨ (¬ p4594))
    (h7073 : p3989 ∨ (¬ p4505))
    (h7920 : p2777 ∨ p2784 ∨ (¬ p4833))
    (h7852 : (¬ p4798) ∨ p4799 ∨ p4803)
    (h7562 : (¬ p4682) ∨ p4683 ∨ p4686)
    (h9050 : (¬ p5303) ∨ p5304 ∨ p5306)
    (h7321 : (¬ p4593) ∨ p4594 ∨ p4597)
    (h7085 : (¬ p4504) ∨ p4505 ∨ p4508)
    (h3697 : p2774 ∨ (¬ p2784))
    (h7840 : p3659 ∨ (¬ p4799))
    (h7550 : p2509 ∨ (¬ p4683))
    (h9038 : p3548 ∨ (¬ p5304))
    (h7317 : p4384 ∨ (¬ p4597))
    (h7077 : p4441 ∨ (¬ p4508))
    (h7079 : p2187 ∨ (¬ p4508))
    (h55680 : (¬ p2509) ∨ (¬ p2563) ∨ (¬ p3083) ∨ (¬ p3952) ∨ (¬ p4700))
    (h53093 : (¬ p2187) ∨ (¬ p2563) ∨ (¬ p3923) ∨ (¬ p4512) ∨ (¬ p4629))
    (h8375 : p3083 ∨ (¬ p5010))
    (h8334 : p3923 ∨ (¬ p4992))
    (h8381 : (¬ p5006) ∨ p5007 ∨ p5010)
    (h8346 : (¬ p4991) ∨ p4992 ∨ p4996)
    (h8369 : p4256 ∨ (¬ p5007))
    (h8339 : p4317 ∨ (¬ p4996))
    (h8340 : p3063 ∨ (¬ p4996))
    (h26882 : (¬ p3093) ∨ p3449 ∨ (¬ p4317))
    (h63247 : (¬ p2254) ∨ (¬ p2563) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3952) ∨ (¬ p4193) ∨ (¬ p4358) ∨ (¬ p4882))
    (h46449 : (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3954))
    (h7983 : p4358 ∨ (¬ p4856))
    (h7332 : p2363 ∨ (¬ p4602))
    (h7995 : (¬ p4855) ∨ p4856 ∨ p4860)
    (h7338 : (¬ p4599) ∨ p4600 ∨ p4602)
    (h7989 : p2819 ∨ (¬ p4860))
    (h7324 : p3322 ∨ (¬ p4600))
    (h7326 : p4347 ∨ (¬ p4600))
    (h7328 : p4330 ∨ (¬ p4600))
    (h46832 : (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4347))
    (h8357 : p3073 ∨ (¬ p5003))
    (h8363 : (¬ p4999) ∨ p5000 ∨ p5003)
    (h8351 : p4261 ∨ (¬ p5000))
    (h66003 : (¬ p4244) ∨ (¬ p2819) ∨ (¬ p3548) ∨ (¬ p4133) ∨ (¬ p4024) ∨ (¬ p3054) ∨ (¬ p4533) ∨ (¬ p3646) ∨ (¬ p3093) ∨ (¬ p2952) ∨ (¬ p2750) ∨ (¬ p4173) ∨ (¬ p4629) ∨ (¬ p2252) ∨ (¬ p3952) ∨ (¬ p2427) ∨ (¬ p2563) ∨ (¬ p3954) ∨ (¬ p4882))
    (h8068 : p4244 ∨ (¬ p4893))
    (h6664 : p4244 ∨ (¬ p4316) ∨ (¬ p4320))
    (h8080 : (¬ p4892) ∨ p4893 ∨ p4896)
    (h8121 : p4320 ∨ (¬ p4916))
    (h8072 : p4344 ∨ (¬ p4896))
    (h8074 : p2870 ∨ (¬ p4896))
    (h8133 : (¬ p4915) ∨ p4916 ∨ p4918)
    (h19748 : (¬ p2881) ∨ (¬ p3659) ∨ (¬ p4344))
    (h6716 : (¬ p2143) ∨ (¬ p2870) ∨ p3051)
    (h8126 : p2995 ∨ (¬ p4918))
    (h8127 : p2901 ∨ (¬ p4918))
    (h8092 : p2881 ∨ (¬ p4903))
    (h63093 : (¬ p2563) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3952))
    (h54932 : (¬ p2396) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4140))
    (h8098 : (¬ p4899) ∨ p4900 ∨ p4903)
    (h8615 : p3246 ∨ (¬ p5103))
    (h7384 : p2396 ∨ (¬ p4622))
    (h8087 : (¬ p4900) ∨ p4901)
    (h8621 : (¬ p5100) ∨ p5101 ∨ p5103)
    (h7390 : (¬ p4618) ∨ p4619 ∨ p4622)
    (h8609 : p3690 ∨ (¬ p5101))
    (h7379 : (¬ p4619) ∨ p4620)
    (h51033 : (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3690) ∨ (¬ p3952) ∨ (¬ p4558))
    (h41348 : (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4140) ∨ (¬ p4620))
    (h7470 : p2449 ∨ (¬ p4659))
    (h8439 : p3744 ∨ (¬ p5042))
    (h7476 : (¬ p4654) ∨ p4655 ∨ p4659)
    (h8451 : (¬ p5041) ∨ p5042 ∨ p5044)
    (h7464 : p3947 ∨ (¬ p4655))
    (h8445 : p3125 ∨ (¬ p5044))
    (h49369 : (¬ p2901) ∨ (¬ p3125) ∨ (¬ p4037) ∨ (¬ p4153) ∨ (¬ p4558))
    (h41115 : (¬ p2563) ∨ (¬ p3125) ∨ (¬ p4026) ∨ (¬ p4512) ∨ (¬ p4629))
    (h8981 : p4037 ∨ (¬ p5273))
    (h8723 : p4026 ∨ (¬ p5147))
    (h8993 : (¬ p5272) ∨ p5273 ∨ p5277)
    (h8735 : (¬ p5146) ∨ p5147 ∨ p5151)
    (h8987 : p3323 ∨ (¬ p5277))
    (h8729 : p3319 ∨ (¬ p5151))
    (h59844 : (¬ p2870) ∨ (¬ p3323) ∨ (¬ p3745) ∨ (¬ p3917) ∨ (¬ p4193) ∨ (¬ p4558))
    (h52093 : (¬ p2252) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3954) ∨ (¬ p4256) ∨ (¬ p4330))
    (h8962 : p3917 ∨ (¬ p5263))
    (h7567 : p2534 ∨ (¬ p4692))
    (h8974 : (¬ p5262) ∨ p5263 ∨ p5268)
    (h7579 : (¬ p4691) ∨ p4692 ∨ p4694)
    (h8968 : p3483 ∨ (¬ p5268))
    (h7573 : p2528 ∨ (¬ p4694))
    (h66004 : (¬ p4348) ∨ (¬ p2528) ∨ (¬ p2299) ∨ (¬ p2657) ∨ (¬ p3742) ∨ (¬ p4712))
    (h7481 : p4348 ∨ (¬ p4665))
    (h7493 : (¬ p4664) ∨ p4665 ∨ p4667)
    (h7486 : p3945 ∨ (¬ p4667))
    (h7487 : p2459 ∨ (¬ p4667))
    (h49633 : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p4712))
    (h8144 : p2911 ∨ (¬ p4923))
    (h8150 : (¬ p4920) ∨ p4921 ∨ p4923)
    (h8138 : p3644 ∨ (¬ p4921))
    (h58899 : (¬ p2417) ∨ (¬ p3644) ∨ (¬ p3947) ∨ (¬ p4111) ∨ (¬ p4112))
    (h7418 : p2417 ∨ (¬ p4639))
    (h7424 : (¬ p4633) ∨ p4634 ∨ p4639)
    (h7412 : p4278 ∨ (¬ p4634))
    (h44820 : (¬ p2657) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4381))
    (h7902 : p4381 ∨ (¬ p4822))
    (h7914 : (¬ p4821) ∨ p4822 ∨ p4827)
    (h7908 : p2761 ∨ (¬ p4827))
    (h7910 : (¬ p4827) ∨ p4831)
    (h41811 : (¬ p2761) ∨ (¬ p3945) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4444))
    (h8646 : p4444 ∨ (¬ p5115))
    (h8658 : (¬ p5114) ∨ p5115 ∨ p5120)
    (h8651 : p4200 ∨ (¬ p5120))
    (h8652 : p3266 ∨ (¬ p5120))
    (h20091 : (¬ p2459) ∨ (¬ p4200) ∨ (¬ p5558))
    (h41469 : (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p4191) ∨ (¬ p4384))
    (h9721 : (¬ p5555) ∨ p5558)
    (h8928 : p4191 ∨ (¬ p5246))
    (h9733 : (¬ p5554) ∨ p5555 ∨ p5561)
    (h8940 : (¬ p5245) ∨ p5246 ∨ p5251)
    (h9725 : (¬ p5561) ∨ p5562)
    (h8934 : p3461 ∨ (¬ p5251))
    (h50996 : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3742) ∨ (¬ p4831) ∨ (¬ p5503))
    (h9583 : (¬ p5500) ∨ p5503)
    (h9595 : (¬ p5499) ∨ p5500 ∨ p5506)
    (h9589 : p3868 ∨ (¬ p5506))
    (h54078 : (¬ p3644) ∨ (¬ p3868) ∨ (¬ p4133) ∨ (¬ p4441) ∨ (¬ p5562) ∨ (¬ p5568))
    (h9791 : (¬ p5567) ∨ p5568)
    (h9803 : (¬ p5566) ∨ p5567 ∨ p5571)
    (h9797 : p3969 ∨ (¬ p5571))
    (h45725 : (¬ p2220) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3969))
    (h7130 : p2220 ∨ (¬ p4530))
    (h6704 : (¬ p2143) ∨ p2220 ∨ (¬ p2619))
    (h7136 : (¬ p4526) ∨ p4527 ∨ p4530)
    (h7704 : p2619 ∨ (¬ p4743))
    (h7122 : p3697 ∨ (¬ p4527))
    (h7123 : p3696 ∨ (¬ p4527))
    (h7710 : (¬ p4738) ∨ p4739 ∨ p4743)
    (h11852 : (¬ p2166) ∨ (¬ p3645) ∨ (¬ p3696) ∨ (¬ p3697))
    (h7698 : p3694 ∨ (¬ p4739))
    (h7045 : p2166 ∨ (¬ p4495))
    (h49801 : (¬ p2528) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4355) ∨ (¬ p4882))
    (h7051 : (¬ p4490) ∨ p4491 ∨ p4495)
    (h8473 : p3692 ∨ (¬ p5055))
    (h7037 : (¬ p4491) ∨ p4492)
    (h8485 : (¬ p5054) ∨ p5055 ∨ p5057)
    (h62130 : (¬ p2870) ∨ (¬ p3146) ∨ (¬ p4243) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4901))
    (h8479 : p3146 ∨ (¬ p5057))
    : p2284 ∨ (¬ p4809) ∨ (¬ p2563) ∨ (¬ p4557) ∨ (¬ p4732) ∨ (¬ p4882) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : p4809 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4557 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4732 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4642 := h65784;
    let u7 : p4713 := h65780;
    let u8 : p4706 := h65853;
    let u9 : p4561 := h65733;
    let u10 : p4698 := h65844;
    let u11 : p4955 := h65661;
    let u12 : p4540 := h65556;
    let u13 : p4648 := h65881;
    let u14 : p4626 := h65800;
    let u15 : p4510 := h65804;
    let u16 : p4815 := h65613;
    let u17 : p4519 := h65865;
    let u18 : p5188 := h65500;
    let u19 : p5139 := h65520;
    let u20 : p4747 := h65606;
    let u21 : p5047 := h65567;
    let u22 : p4839 := h65827;
    let u23 : p4775 := h65709;
    let u24 : p4762 := h65836;
    let u25 : p4931 := h65687;
    let u26 : p4872 := h65699;
    let u27 : p5013 := h65583;
    let u28 : p4534 := h65673;
    let u29 : p4879 := h65795;
    let u30 : p4886 := h65741;
    let u31 : p4864 := h65716;
    let u32 : p4791 := h65622;
    let u33 : p4605 := h65771;
    let u34 : p4499 := h65748;
    let u35 : p4833 := h65923;
    let u36 : p4798 := h65626;
    let u37 : p4682 := h65998;
    let u38 : p5303 := h65448;
    let u39 : p4593 := h65895;
    let u40 : p4504 := h65791;
    let u41 : p5006 := h65634;
    let u42 : p4991 := h65638;
    let u43 : p4855 := h65810;
    let u44 : p4599 := h65758;
    let u45 : p4999 := h65597;
    let u46 : p4892 := h65630;
    let u47 : p4915 := h65729;
    let u48 : p4899 := h65649;
    let u49 : p5100 := h65540;
    let u50 : p4618 := h65720;
    let u51 : p4654 := h65944;
    let u52 : p5041 := h65571;
    let u53 : p5272 := h65460;
    let u54 : p5146 := h65516;
    let u55 : p5262 := h65464;
    let u56 : p4691 := h65775;
    let u57 : p4664 := h65694;
    let u58 : p4920 := h65980;
    let u59 : p4633 := h65848;
    let u60 : p4821 := h65587;
    let u61 : p5114 := h65528;
    let u62 : p5554 := h65356;
    let u63 : p5245 := h65472;
    let u64 : p5499 := h65376;
    let u65 : p5566 := h65352;
    let u66 : p4526 := h65705;
    let u67 : p4738 := h65617;
    let u68 : p4490 := h65690;
    let u69 : p5054 := h65563;
    let u70 : p4111 := (Or.elim h7857 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u71 : p4116 := (Or.elim h7856 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u72 : p2274 := (Or.elim h7208 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u73 : (¬ p4110) := (Or.elim h9440 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u74 : (¬ p4714) := (Or.elim h7618 (fun q0 => (False.elim (u73 q0))) (fun r0 => r0));
    let u75 : p4716 := (Or.elim h7630 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u74 q1))) (fun r1 => r1))));
    let u76 : p4203 := (Or.elim h7622 (fun q0 => q0) (fun r0 => (False.elim (r0 u75))));
    let u77 : (¬ p2588) := (Or.elim h6680 (fun q0 => (False.elim (q0 u72))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u76))))));
    let u78 : (¬ p4707) := (Or.elim h7601 (fun q0 => (False.elim (u77 q0))) (fun r0 => r0));
    let u79 : p4709 := (Or.elim h7613 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u78 q1))) (fun r1 => r1))));
    let u80 : p4712 := (Or.elim h7609 (fun q0 => (False.elim (q0 u79))) (fun r0 => r0));
    let u81 : p3920 := (Or.elim h7606 (fun q0 => q0) (fun r0 => (False.elim (r0 u79))));
    let u82 : p3872 := (Or.elim h7207 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u83 : (¬ p4235) := (Or.elim h20312 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u82))) (fun r1 => r1))));
    let u84 : (¬ p4643) := (Or.elim h7429 (fun q0 => (False.elim (u83 q0))) (fun r0 => r0));
    let u85 : p4645 := (Or.elim h7441 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u84 q1))) (fun r1 => r1))));
    let u86 : p4646 := (Or.elim h7436 (fun q0 => (False.elim (q0 u85))) (fun r0 => r0));
    let u87 : p2427 := (Or.elim h5739 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u82))))));
    let u88 : p4558 := (Or.elim h7209 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    let u89 : p4140 := (Or.elim h7206 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u90 : p3954 := (Or.elim h7681 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u91 : p2753 := (Or.elim h7680 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u92 : p3873 := (Or.elim h7679 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u93 : (¬ p4565) := (Or.elim h7226 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u94 : (¬ p4241) := (Or.elim h6533 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    let u95 : p4562 := (Or.elim h7232 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u93 r1))))));
    let u96 : (¬ p4703) := (Or.elim h7588 (fun q0 => (False.elim (u94 q0))) (fun r0 => r0));
    let u97 : p4153 := (Or.elim h7218 (fun q0 => q0) (fun r0 => (False.elim (r0 u95))));
    let u98 : p3745 := (Or.elim h7219 (fun q0 => q0) (fun r0 => (False.elim (r0 u95))));
    let u99 : p3952 := (Or.elim h7220 (fun q0 => q0) (fun r0 => (False.elim (r0 u95))));
    let u100 : p4699 := (Or.elim h7596 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u96 r1))))));
    let u101 : p4700 := (Or.elim h7582 (fun q0 => (False.elim (q0 u100))) (fun r0 => r0));
    let u102 : p2440 := (Or.elim h7584 (fun q0 => q0) (fun r0 => (False.elim (r0 u100))));
    let u103 : p3662 := (Or.elim h27082 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u70))) (fun r1 => (False.elim (r1 u101))))));
    let u104 : (¬ p2992) := (Or.elim h20017 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u70))) (fun r1 => (False.elim (r1 u101))))));
    let u105 : (¬ p2247) := (Or.elim h46112 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u99))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u70))) (fun r3 => (False.elim (r3 u101))))))))));
    let u106 : (¬ p2437) := (Or.elim h52915 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u99))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u86))) (fun r3 => (False.elim (r3 u101))))))))));
    let u107 : (¬ p2406) := (Or.elim h20082 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u102))) (fun r1 => (False.elim (r1 u71))))));
    let u108 : p4154 := (Or.elim h6201 (fun q0 => (False.elim (q0 u103))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u97))) (fun r1 => r1))));
    let u109 : (¬ p4958) := (Or.elim h8246 (fun q0 => (False.elim (u104 q0))) (fun r0 => r0));
    let u110 : (¬ p2244) := (Or.elim h2625 (fun q0 => q0) (fun r0 => (False.elim (u105 r0))));
    let u111 : (¬ p4651) := (Or.elim h7453 (fun q0 => (False.elim (u106 q0))) (fun r0 => r0));
    let u112 : (¬ p4630) := (Or.elim h7401 (fun q0 => (False.elim (u107 q0))) (fun r0 => r0));
    let u113 : p4956 := (Or.elim h8252 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u109 r1))))));
    let u114 : p2251 := (Or.elim h7159 (fun q0 => (False.elim (u110 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u12))))));
    let u115 : p4649 := (Or.elim h7459 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u111 r1))))));
    let u116 : p4627 := (Or.elim h7407 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u112 r1))))));
    let u117 : p3412 := (Or.elim h8239 (fun q0 => q0) (fun r0 => (False.elim (r0 u113))));
    let u118 : p2252 := (Or.elim h2637 (fun q0 => (False.elim (q0 u114))) (fun r0 => r0));
    let u119 : p2253 := (Or.elim h2638 (fun q0 => (False.elim (q0 u114))) (fun r0 => r0));
    let u120 : p2241 := (Or.elim h2639 (fun q0 => q0) (fun r0 => (False.elim (r0 u114))));
    let u121 : p2254 := (Or.elim h2640 (fun q0 => (False.elim (q0 u114))) (fun r0 => r0));
    let u122 : p4112 := (Or.elim h7445 (fun q0 => q0) (fun r0 => (False.elim (r0 u115))));
    let u123 : p3742 := (Or.elim h7447 (fun q0 => q0) (fun r0 => (False.elim (r0 u115))));
    let u124 : p4202 := (Or.elim h7393 (fun q0 => q0) (fun r0 => (False.elim (r0 u116))));
    let u125 : p4629 := (Or.elim h7397 (fun q0 => (False.elim (q0 u116))) (fun r0 => r0));
    let u126 : p4173 := (Or.elim h6237 (fun q0 => (False.elim (q0 u117))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u99))) (fun r1 => r1))));
    let u127 : (¬ p2192) := (Or.elim h20007 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u117))) (fun r1 => (False.elim (r1 u99))))));
    let u128 : (¬ p2741) := (Or.elim h6267 (fun q0 => (False.elim (q0 u120))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u90))))));
    let u129 : p3574 := (Or.elim h6413 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u123))) (fun r1 => (False.elim (r1 u81))))));
    let u130 : (¬ p3555) := (Or.elim h42642 (fun q0 => (False.elim (q0 u120))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u126))))))));
    let u131 : (¬ p4515) := (Or.elim h7096 (fun q0 => (False.elim (u127 q0))) (fun r0 => r0));
    let u132 : (¬ p2740) := (Or.elim h3606 (fun q0 => q0) (fun r0 => (False.elim (u128 r0))));
    let u133 : (¬ p4520) := (Or.elim h7107 (fun q0 => (False.elim (u130 q0))) (fun r0 => r0));
    let u134 : (¬ p3452) := (Or.elim h6295 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u130 q1))) (fun r1 => (False.elim (r1 u124))))));
    let u135 : p4511 := (Or.elim h7102 (fun q0 => (False.elim (q0 u15))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u131 r1))))));
    let u136 : p2747 := (Or.elim h7875 (fun q0 => (False.elim (u132 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u16))))));
    let u137 : p4523 := (Or.elim h7119 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u133 q1))) (fun r1 => r1))));
    let u138 : (¬ p5189) := (Or.elim h8799 (fun q0 => (False.elim (u134 q0))) (fun r0 => r0));
    let u139 : p4512 := (Or.elim h7088 (fun q0 => (False.elim (q0 u135))) (fun r0 => r0));
    let u140 : p3957 := (Or.elim h7089 (fun q0 => q0) (fun r0 => (False.elim (r0 u135))));
    let u141 : p2748 := (Or.elim h3620 (fun q0 => (False.elim (q0 u136))) (fun r0 => r0));
    let u142 : p2750 := (Or.elim h3623 (fun q0 => (False.elim (q0 u136))) (fun r0 => r0));
    let u143 : p3645 := (Or.elim h7111 (fun q0 => q0) (fun r0 => (False.elim (r0 u137))));
    let u144 : p2210 := (Or.elim h7113 (fun q0 => q0) (fun r0 => (False.elim (r0 u137))));
    let u145 : p5192 := (Or.elim h8811 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u138 q1))) (fun r1 => r1))));
    let u146 : (¬ p3549) := (Or.elim h61082 (fun q0 => (False.elim (q0 u72))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u139))) (fun r3 => (False.elim (r3 u125))))))))));
    let u147 : (¬ p2630) := (Or.elim h35728 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u141))) (fun r1 => (False.elim (r1 u70))))));
    let u148 : (¬ p3136) := (Or.elim h19996 (fun q0 => (False.elim (q0 u141))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u70))) (fun r2 => (False.elim (r2 u101))))))));
    let u149 : (¬ p2797) := (Or.elim h33848 (fun q0 => (False.elim (q0 u141))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u108))))));
    let u150 : (¬ p2685) := (Or.elim h38656 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u141))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u70))) (fun r2 => (False.elim (r2 u122))))))));
    let u151 : (¬ p2651) := (Or.elim h51595 (fun q0 => (False.elim (q0 u119))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u142))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u90))) (fun r3 => (False.elim (r3 u70))))))))));
    let u152 : (¬ p2946) := (Or.elim h49229 (fun q0 => (False.elim (q0 u119))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u142))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u103))) (fun r3 => (False.elim (r3 u90))))))))));
    let u153 : (¬ p4874) := (Or.elim h29892 (fun q0 => (False.elim (q0 u144))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u90))) (fun r1 => r1))));
    let u154 : (¬ p3591) := (Or.elim h41941 (fun q0 => (False.elim (q0 u144))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u140))) (fun r3 => (False.elim (r3 u125))))))))));
    let u155 : p5194 := (Or.elim h8807 (fun q0 => (False.elim (q0 u145))) (fun r0 => r0));
    let u156 : (¬ p5140) := (Or.elim h8705 (fun q0 => (False.elim (u146 q0))) (fun r0 => r0));
    let u157 : (¬ p4751) := (Or.elim h7721 (fun q0 => (False.elim (u147 q0))) (fun r0 => r0));
    let u158 : (¬ p5050) := (Or.elim h8462 (fun q0 => (False.elim (u148 q0))) (fun r0 => r0));
    let u159 : (¬ p4844) := (Or.elim h7953 (fun q0 => (False.elim (u149 q0))) (fun r0 => r0));
    let u160 : (¬ p4780) := (Or.elim h7794 (fun q0 => (False.elim (u150 q0))) (fun r0 => r0));
    let u161 : (¬ p2661) := (Or.elim h3449 (fun q0 => (False.elim (u151 q0))) (fun r0 => r0));
    let u162 : (¬ p2956) := (Or.elim h4042 (fun q0 => (False.elim (u152 q0))) (fun r0 => r0));
    let u163 : (¬ p4873) := (Or.elim h8015 (fun q0 => q0) (fun r0 => (False.elim (u153 r0))));
    let u164 : (¬ p5014) := (Or.elim h8386 (fun q0 => (False.elim (u154 q0))) (fun r0 => r0));
    let u165 : (¬ p2230) := (Or.elim h59873 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u126))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u124))) (fun r3 => (False.elim (r3 u155))))))))));
    let u166 : p5143 := (Or.elim h8717 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u156 q1))) (fun r1 => r1))));
    let u167 : p4748 := (Or.elim h7727 (fun q0 => (False.elim (q0 u20))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u157 r1))))));
    let u168 : p5048 := (Or.elim h8468 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u158 r1))))));
    let u169 : p4840 := (Or.elim h7959 (fun q0 => (False.elim (q0 u22))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u159 r1))))));
    let u170 : p4776 := (Or.elim h7800 (fun q0 => (False.elim (q0 u23))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u160 r1))))));
    let u171 : p2654 := (Or.elim h7750 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u161 q1))) (fun r1 => (False.elim (r1 u24))))));
    let u172 : p2949 := (Or.elim h8182 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u162 q1))) (fun r1 => (False.elim (r1 u25))))));
    let u173 : p4876 := (Or.elim h8029 (fun q0 => (False.elim (q0 u26))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u163 q1))) (fun r1 => r1))));
    let u174 : p5019 := (Or.elim h8398 (fun q0 => (False.elim (q0 u27))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u164 q1))) (fun r1 => r1))));
    let u175 : (¬ p4537) := (Or.elim h7148 (fun q0 => (False.elim (u165 q0))) (fun r0 => r0));
    let u176 : p4452 := (Or.elim h8710 (fun q0 => q0) (fun r0 => (False.elim (r0 u166))));
    let u177 : p3309 := (Or.elim h8711 (fun q0 => q0) (fun r0 => (False.elim (r0 u166))));
    let u178 : p4343 := (Or.elim h7714 (fun q0 => q0) (fun r0 => (False.elim (r0 u167))));
    let u179 : p4316 := (Or.elim h8455 (fun q0 => q0) (fun r0 => (False.elim (r0 u168))));
    let u180 : p4842 := (Or.elim h7948 (fun q0 => (False.elim (q0 u169))) (fun r0 => r0));
    let u181 : p4778 := (Or.elim h7789 (fun q0 => (False.elim (q0 u170))) (fun r0 => r0));
    let u182 : p2657 := (Or.elim h3435 (fun q0 => (False.elim (q0 u171))) (fun r0 => r0));
    let u183 : p2951 := (Or.elim h4027 (fun q0 => (False.elim (q0 u172))) (fun r0 => r0));
    let u184 : p2952 := (Or.elim h4028 (fun q0 => (False.elim (q0 u172))) (fun r0 => r0));
    let u185 : p4243 := (Or.elim h8021 (fun q0 => q0) (fun r0 => (False.elim (r0 u173))));
    let u186 : p3093 := (Or.elim h8392 (fun q0 => q0) (fun r0 => (False.elim (r0 u174))));
    let u187 : p4535 := (Or.elim h7154 (fun q0 => (False.elim (q0 u28))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u175 r1))))));
    let u188 : (¬ p2850) := (Or.elim h19857 (fun q0 => (False.elim (q0 u102))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u178))))));
    let u189 : (¬ p2860) := (Or.elim h20521 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u99))) (fun r1 => (False.elim (r1 u179))))));
    let u190 : (¬ p3688) := (Or.elim h49201 (fun q0 => (False.elim (q0 u120))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u141))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u90))) (fun r3 => (False.elim (r3 u180))))))))));
    let u191 : (¬ p3588) := (Or.elim h41580 (fun q0 => (False.elim (q0 u120))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u141))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u90))) (fun r3 => (False.elim (r3 u181))))))))));
    let u192 : p3646 := (Or.elim h5865 (fun q0 => (False.elim (q0 u183))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u99))))));
    let u193 : (¬ p3880) := (Or.elim h44033 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u184))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u99))))))));
    let u194 : p2143 := (Or.elim h17146 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u143))) (fun r1 => (False.elim (r1 u185))))));
    let u195 : p3399 := (Or.elim h25108 (fun q0 => (False.elim (q0 u186))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u176))))));
    let u196 : (¬ p2177) := (Or.elim h52571 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u186))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u177))) (fun r2 => (False.elim (r2 u90))))))));
    let u197 : p4533 := (Or.elim h7144 (fun q0 => q0) (fun r0 => (False.elim (r0 u187))));
    let u198 : (¬ p4883) := (Or.elim h8040 (fun q0 => (False.elim (u188 q0))) (fun r0 => r0));
    let u199 : (¬ p4890) := (Or.elim h8057 (fun q0 => (False.elim (u189 q0))) (fun r0 => r0));
    let u200 : (¬ p4865) := (Or.elim h8000 (fun q0 => (False.elim (u190 q0))) (fun r0 => r0));
    let u201 : (¬ p4792) := (Or.elim h7823 (fun q0 => (False.elim (u191 q0))) (fun r0 => r0));
    let u202 : (¬ p4606) := (Or.elim h7343 (fun q0 => (False.elim (u193 q0))) (fun r0 => r0));
    let u203 : (¬ p4502) := (Or.elim h7062 (fun q0 => (False.elim (u196 q0))) (fun r0 => r0));
    let u204 : p4880 := (Or.elim h8046 (fun q0 => (False.elim (q0 u29))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u198 r1))))));
    let u205 : p4887 := (Or.elim h8063 (fun q0 => (False.elim (q0 u30))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u199 r1))))));
    let u206 : p4868 := (Or.elim h8012 (fun q0 => (False.elim (q0 u31))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u200 q1))) (fun r1 => r1))));
    let u207 : p4795 := (Or.elim h7835 (fun q0 => (False.elim (q0 u32))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u201 q1))) (fun r1 => r1))));
    let u208 : p4609 := (Or.elim h7355 (fun q0 => (False.elim (q0 u33))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u202 q1))) (fun r1 => r1))));
    let u209 : p4500 := (Or.elim h7068 (fun q0 => (False.elim (q0 u34))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u203 r1))))));
    let u210 : p3054 := (Or.elim h8032 (fun q0 => q0) (fun r0 => (False.elim (r0 u204))));
    let u211 : p4193 := (Or.elim h8049 (fun q0 => q0) (fun r0 => (False.elim (r0 u205))));
    let u212 : p4024 := (Or.elim h8004 (fun q0 => q0) (fun r0 => (False.elim (r0 u206))));
    let u213 : p2829 := (Or.elim h8006 (fun q0 => q0) (fun r0 => (False.elim (r0 u206))));
    let u214 : p3576 := (Or.elim h7827 (fun q0 => q0) (fun r0 => (False.elim (r0 u207))));
    let u215 : p4355 := (Or.elim h7348 (fun q0 => q0) (fun r0 => (False.elim (r0 u208))));
    let u216 : p4610 := (Or.elim h7350 (fun q0 => (False.elim (q0 u208))) (fun r0 => r0));
    let u217 : p3955 := (Or.elim h7054 (fun q0 => q0) (fun r0 => (False.elim (r0 u209))));
    let u218 : p2299 := (Or.elim h7056 (fun q0 => q0) (fun r0 => (False.elim (r0 u209))));
    let u219 : p4501 := (Or.elim h7057 (fun q0 => (False.elim (q0 u209))) (fun r0 => r0));
    let u220 : p4133 := (Or.elim h7058 (fun q0 => q0) (fun r0 => (False.elim (r0 u209))));
    let u221 : (¬ p2780) := (Or.elim h42276 (fun q0 => (False.elim (q0 u120))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u142))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u213))) (fun r3 => (False.elim (r3 u92))))))))));
    let u222 : (¬ p2717) := (Or.elim h42709 (fun q0 => (False.elim (q0 u218))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u195))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u214))) (fun r3 => (False.elim (r3 u90))))))))));
    let u223 : (¬ p2518) := (Or.elim h41927 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u126))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u124))) (fun r3 => (False.elim (r3 u216))))))))));
    let u224 : (¬ p3527) := (Or.elim h60034 (fun q0 => (False.elim (q0 u218))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u186))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u90))) (fun r3 => (False.elim (r3 u176))))))))));
    let u225 : (¬ p3956) := (Or.elim h50065 (fun q0 => (False.elim (q0 u118))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u182))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u142))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u186))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u177))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u129))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u90))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u219))))))))))))))))));
    let u226 : (¬ p3989) := (Or.elim h60774 (fun q0 => (False.elim (q0 u118))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u142))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u184))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u186))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u177))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u99))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u90))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u219))))))))))))))))));
    let u227 : (¬ p2777) := (Or.elim h3683 (fun q0 => q0) (fun r0 => (False.elim (u221 r0))));
    let u228 : (¬ p4803) := (Or.elim h7846 (fun q0 => (False.elim (u222 q0))) (fun r0 => r0));
    let u229 : (¬ p4686) := (Or.elim h7556 (fun q0 => (False.elim (u223 q0))) (fun r0 => r0));
    let u230 : (¬ p5306) := (Or.elim h9044 (fun q0 => (False.elim (u224 q0))) (fun r0 => r0));
    let u231 : (¬ p4594) := (Or.elim h7309 (fun q0 => (False.elim (u225 q0))) (fun r0 => r0));
    let u232 : (¬ p4505) := (Or.elim h7073 (fun q0 => (False.elim (u226 q0))) (fun r0 => r0));
    let u233 : p2784 := (Or.elim h7920 (fun q0 => (False.elim (u227 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u35))))));
    let u234 : p4799 := (Or.elim h7852 (fun q0 => (False.elim (q0 u36))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u228 r1))))));
    let u235 : p4683 := (Or.elim h7562 (fun q0 => (False.elim (q0 u37))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u229 r1))))));
    let u236 : p5304 := (Or.elim h9050 (fun q0 => (False.elim (q0 u38))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u230 r1))))));
    let u237 : p4597 := (Or.elim h7321 (fun q0 => (False.elim (q0 u39))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u231 q1))) (fun r1 => r1))));
    let u238 : p4508 := (Or.elim h7085 (fun q0 => (False.elim (q0 u40))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u232 q1))) (fun r1 => r1))));
    let u239 : p2774 := (Or.elim h3697 (fun q0 => q0) (fun r0 => (False.elim (r0 u233))));
    let u240 : p3659 := (Or.elim h7840 (fun q0 => q0) (fun r0 => (False.elim (r0 u234))));
    let u241 : p2509 := (Or.elim h7550 (fun q0 => q0) (fun r0 => (False.elim (r0 u235))));
    let u242 : p3548 := (Or.elim h9038 (fun q0 => q0) (fun r0 => (False.elim (r0 u236))));
    let u243 : p4384 := (Or.elim h7317 (fun q0 => q0) (fun r0 => (False.elim (r0 u237))));
    let u244 : p4441 := (Or.elim h7077 (fun q0 => q0) (fun r0 => (False.elim (r0 u238))));
    let u245 : p2187 := (Or.elim h7079 (fun q0 => q0) (fun r0 => (False.elim (r0 u238))));
    let u246 : (¬ p3083) := (Or.elim h55680 (fun q0 => (False.elim (q0 u241))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u99))) (fun r3 => (False.elim (r3 u101))))))))));
    let u247 : (¬ p3923) := (Or.elim h53093 (fun q0 => (False.elim (q0 u245))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u139))) (fun r3 => (False.elim (r3 u125))))))))));
    let u248 : (¬ p5010) := (Or.elim h8375 (fun q0 => (False.elim (u246 q0))) (fun r0 => r0));
    let u249 : (¬ p4992) := (Or.elim h8334 (fun q0 => (False.elim (u247 q0))) (fun r0 => r0));
    let u250 : p5007 := (Or.elim h8381 (fun q0 => (False.elim (q0 u41))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u248 r1))))));
    let u251 : p4996 := (Or.elim h8346 (fun q0 => (False.elim (q0 u42))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u249 q1))) (fun r1 => r1))));
    let u252 : p4256 := (Or.elim h8369 (fun q0 => q0) (fun r0 => (False.elim (r0 u250))));
    let u253 : p4317 := (Or.elim h8339 (fun q0 => q0) (fun r0 => (False.elim (r0 u251))));
    let u254 : p3063 := (Or.elim h8340 (fun q0 => q0) (fun r0 => (False.elim (r0 u251))));
    let u255 : p3449 := (Or.elim h26882 (fun q0 => (False.elim (q0 u186))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u253))))));
    let u256 : (¬ p4358) := (Or.elim h63247 (fun q0 => (False.elim (q0 u121))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u184))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u254))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u186))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u99))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u211))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u5))))))))))))))))));
    let u257 : (¬ p2363) := (Or.elim h46449 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u254))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u186))) (fun r2 => (False.elim (r2 u90))))))));
    let u258 : (¬ p4856) := (Or.elim h7983 (fun q0 => (False.elim (u256 q0))) (fun r0 => r0));
    let u259 : (¬ p4602) := (Or.elim h7332 (fun q0 => (False.elim (u257 q0))) (fun r0 => r0));
    let u260 : p4860 := (Or.elim h7995 (fun q0 => (False.elim (q0 u43))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u258 q1))) (fun r1 => r1))));
    let u261 : p4600 := (Or.elim h7338 (fun q0 => (False.elim (q0 u44))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u259 r1))))));
    let u262 : p2819 := (Or.elim h7989 (fun q0 => q0) (fun r0 => (False.elim (r0 u260))));
    let u263 : p3322 := (Or.elim h7324 (fun q0 => q0) (fun r0 => (False.elim (r0 u261))));
    let u264 : p4347 := (Or.elim h7326 (fun q0 => q0) (fun r0 => (False.elim (r0 u261))));
    let u265 : p4330 := (Or.elim h7328 (fun q0 => q0) (fun r0 => (False.elim (r0 u261))));
    let u266 : (¬ p3073) := (Or.elim h46832 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u255))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u90))) (fun r2 => (False.elim (r2 u264))))))));
    let u267 : (¬ p5003) := (Or.elim h8357 (fun q0 => (False.elim (u266 q0))) (fun r0 => r0));
    let u268 : p5000 := (Or.elim h8363 (fun q0 => (False.elim (q0 u45))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u267 r1))))));
    let u269 : p4261 := (Or.elim h8351 (fun q0 => q0) (fun r0 => (False.elim (r0 u268))));
    let u270 : (¬ p4244) := (Or.elim h66003 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u262))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u242))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u220))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u212))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u210))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u197))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u192))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u186))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u184))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u142))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u126))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u125))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u118))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u99))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u87))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u2))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u90))) (fun r17 => (False.elim (r17 u5))))))))))))))))))))))))))))))))))))));
    let u271 : (¬ p4893) := (Or.elim h8068 (fun q0 => (False.elim (u270 q0))) (fun r0 => r0));
    let u272 : (¬ p4320) := (Or.elim h6664 (fun q0 => (False.elim (u270 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u179))) (fun r1 => r1))));
    let u273 : p4896 := (Or.elim h8080 (fun q0 => (False.elim (q0 u46))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u271 q1))) (fun r1 => r1))));
    let u274 : (¬ p4916) := (Or.elim h8121 (fun q0 => (False.elim (u272 q0))) (fun r0 => r0));
    let u275 : p4344 := (Or.elim h8072 (fun q0 => q0) (fun r0 => (False.elim (r0 u273))));
    let u276 : p2870 := (Or.elim h8074 (fun q0 => q0) (fun r0 => (False.elim (r0 u273))));
    let u277 : p4918 := (Or.elim h8133 (fun q0 => (False.elim (q0 u47))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u274 q1))) (fun r1 => r1))));
    let u278 : (¬ p2881) := (Or.elim h19748 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u240))) (fun r1 => (False.elim (r1 u275))))));
    let u279 : p3051 := (Or.elim h6716 (fun q0 => (False.elim (q0 u194))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u276))) (fun r1 => r1))));
    let u280 : p2995 := (Or.elim h8126 (fun q0 => q0) (fun r0 => (False.elim (r0 u277))));
    let u281 : p2901 := (Or.elim h8127 (fun q0 => q0) (fun r0 => (False.elim (r0 u277))));
    let u282 : (¬ p4903) := (Or.elim h8092 (fun q0 => (False.elim (u278 q0))) (fun r0 => r0));
    let u283 : (¬ p3246) := (Or.elim h63093 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u183))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u279))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u99))))))))));
    let u284 : (¬ p2396) := (Or.elim h54932 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u279))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u192))) (fun r3 => (False.elim (r3 u89))))))))));
    let u285 : p4900 := (Or.elim h8098 (fun q0 => (False.elim (q0 u48))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u282 r1))))));
    let u286 : (¬ p5103) := (Or.elim h8615 (fun q0 => (False.elim (u283 q0))) (fun r0 => r0));
    let u287 : (¬ p4622) := (Or.elim h7384 (fun q0 => (False.elim (u284 q0))) (fun r0 => r0));
    let u288 : p4901 := (Or.elim h8087 (fun q0 => (False.elim (q0 u285))) (fun r0 => r0));
    let u289 : p5101 := (Or.elim h8621 (fun q0 => (False.elim (q0 u49))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u286 r1))))));
    let u290 : p4619 := (Or.elim h7390 (fun q0 => (False.elim (q0 u50))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u287 r1))))));
    let u291 : p3690 := (Or.elim h8609 (fun q0 => q0) (fun r0 => (False.elim (r0 u289))));
    let u292 : p4620 := (Or.elim h7379 (fun q0 => (False.elim (q0 u290))) (fun r0 => r0));
    let u293 : (¬ p2449) := (Or.elim h51033 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u280))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u291))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u99))) (fun r3 => (False.elim (r3 u88))))))))));
    let u294 : (¬ p3744) := (Or.elim h41348 (fun q0 => (False.elim (q0 u279))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u192))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u89))) (fun r3 => (False.elim (r3 u292))))))))));
    let u295 : (¬ p4659) := (Or.elim h7470 (fun q0 => (False.elim (u293 q0))) (fun r0 => r0));
    let u296 : (¬ p5042) := (Or.elim h8439 (fun q0 => (False.elim (u294 q0))) (fun r0 => r0));
    let u297 : p4655 := (Or.elim h7476 (fun q0 => (False.elim (q0 u51))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u295 r1))))));
    let u298 : p5044 := (Or.elim h8451 (fun q0 => (False.elim (q0 u52))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u296 q1))) (fun r1 => r1))));
    let u299 : p3947 := (Or.elim h7464 (fun q0 => q0) (fun r0 => (False.elim (r0 u297))));
    let u300 : p3125 := (Or.elim h8445 (fun q0 => q0) (fun r0 => (False.elim (r0 u298))));
    let u301 : (¬ p4037) := (Or.elim h49369 (fun q0 => (False.elim (q0 u281))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u300))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u97))) (fun r3 => (False.elim (r3 u88))))))))));
    let u302 : (¬ p4026) := (Or.elim h41115 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u300))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u139))) (fun r3 => (False.elim (r3 u125))))))))));
    let u303 : (¬ p5273) := (Or.elim h8981 (fun q0 => (False.elim (u301 q0))) (fun r0 => r0));
    let u304 : (¬ p5147) := (Or.elim h8723 (fun q0 => (False.elim (u302 q0))) (fun r0 => r0));
    let u305 : p5277 := (Or.elim h8993 (fun q0 => (False.elim (q0 u53))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u303 q1))) (fun r1 => r1))));
    let u306 : p5151 := (Or.elim h8735 (fun q0 => (False.elim (q0 u54))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u304 q1))) (fun r1 => r1))));
    let u307 : p3323 := (Or.elim h8987 (fun q0 => q0) (fun r0 => (False.elim (r0 u305))));
    let u308 : p3319 := (Or.elim h8729 (fun q0 => q0) (fun r0 => (False.elim (r0 u306))));
    let u309 : (¬ p3917) := (Or.elim h59844 (fun q0 => (False.elim (q0 u276))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u307))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u98))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u211))) (fun r4 => (False.elim (r4 u88))))))))))));
    let u310 : (¬ p2534) := (Or.elim h52093 (fun q0 => (False.elim (q0 u118))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u182))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u142))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u186))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u308))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u90))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u252))) (fun r7 => (False.elim (r7 u265))))))))))))))))));
    let u311 : (¬ p5263) := (Or.elim h8962 (fun q0 => (False.elim (u309 q0))) (fun r0 => r0));
    let u312 : (¬ p4692) := (Or.elim h7567 (fun q0 => (False.elim (u310 q0))) (fun r0 => r0));
    let u313 : p5268 := (Or.elim h8974 (fun q0 => (False.elim (q0 u55))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u311 q1))) (fun r1 => r1))));
    let u314 : p4694 := (Or.elim h7579 (fun q0 => (False.elim (q0 u56))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u312 q1))) (fun r1 => r1))));
    let u315 : p3483 := (Or.elim h8968 (fun q0 => q0) (fun r0 => (False.elim (r0 u313))));
    let u316 : p2528 := (Or.elim h7573 (fun q0 => q0) (fun r0 => (False.elim (r0 u314))));
    let u317 : (¬ p4348) := (Or.elim h66004 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u316))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u218))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u182))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u123))) (fun r4 => (False.elim (r4 u80))))))))))));
    let u318 : (¬ p4665) := (Or.elim h7481 (fun q0 => (False.elim (u317 q0))) (fun r0 => r0));
    let u319 : p4667 := (Or.elim h7493 (fun q0 => (False.elim (q0 u57))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u318 q1))) (fun r1 => r1))));
    let u320 : p3945 := (Or.elim h7486 (fun q0 => q0) (fun r0 => (False.elim (r0 u319))));
    let u321 : p2459 := (Or.elim h7487 (fun q0 => q0) (fun r0 => (False.elim (r0 u319))));
    let u322 : (¬ p2911) := (Or.elim h49633 (fun q0 => (False.elim (q0 u321))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u217))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u264))) (fun r3 => (False.elim (r3 u80))))))))));
    let u323 : (¬ p4923) := (Or.elim h8144 (fun q0 => (False.elim (u322 q0))) (fun r0 => r0));
    let u324 : p4921 := (Or.elim h8150 (fun q0 => (False.elim (q0 u58))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u323 r1))))));
    let u325 : p3644 := (Or.elim h8138 (fun q0 => q0) (fun r0 => (False.elim (r0 u324))));
    let u326 : (¬ p2417) := (Or.elim h58899 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u325))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u299))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u70))) (fun r3 => (False.elim (r3 u122))))))))));
    let u327 : (¬ p4639) := (Or.elim h7418 (fun q0 => (False.elim (u326 q0))) (fun r0 => r0));
    let u328 : p4634 := (Or.elim h7424 (fun q0 => (False.elim (q0 u59))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u327 r1))))));
    let u329 : p4278 := (Or.elim h7412 (fun q0 => q0) (fun r0 => (False.elim (r0 u328))));
    let u330 : (¬ p4381) := (Or.elim h44820 (fun q0 => (False.elim (q0 u182))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u123))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u329))) (fun r2 => r2))))));
    let u331 : (¬ p4822) := (Or.elim h7902 (fun q0 => (False.elim (u330 q0))) (fun r0 => r0));
    let u332 : p4827 := (Or.elim h7914 (fun q0 => (False.elim (q0 u60))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u331 q1))) (fun r1 => r1))));
    let u333 : p2761 := (Or.elim h7908 (fun q0 => q0) (fun r0 => (False.elim (r0 u332))));
    let u334 : p4831 := (Or.elim h7910 (fun q0 => (False.elim (q0 u332))) (fun r0 => r0));
    let u335 : (¬ p4444) := (Or.elim h41811 (fun q0 => (False.elim (q0 u333))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u320))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u220))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u264))) (fun r3 => r3))))))));
    let u336 : (¬ p5115) := (Or.elim h8646 (fun q0 => (False.elim (u335 q0))) (fun r0 => r0));
    let u337 : p5120 := (Or.elim h8658 (fun q0 => (False.elim (q0 u61))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u336 q1))) (fun r1 => r1))));
    let u338 : p4200 := (Or.elim h8651 (fun q0 => q0) (fun r0 => (False.elim (r0 u337))));
    let u339 : p3266 := (Or.elim h8652 (fun q0 => q0) (fun r0 => (False.elim (r0 u337))));
    let u340 : (¬ p5558) := (Or.elim h20091 (fun q0 => (False.elim (q0 u321))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u338))) (fun r1 => r1))));
    let u341 : (¬ p4191) := (Or.elim h41469 (fun q0 => (False.elim (q0 u316))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u339))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u263))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u243))))))))));
    let u342 : (¬ p5555) := (Or.elim h9721 (fun q0 => q0) (fun r0 => (False.elim (u340 r0))));
    let u343 : (¬ p5246) := (Or.elim h8928 (fun q0 => (False.elim (u341 q0))) (fun r0 => r0));
    let u344 : p5561 := (Or.elim h9733 (fun q0 => (False.elim (q0 u62))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u342 q1))) (fun r1 => r1))));
    let u345 : p5251 := (Or.elim h8940 (fun q0 => (False.elim (q0 u63))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u343 q1))) (fun r1 => r1))));
    let u346 : p5562 := (Or.elim h9725 (fun q0 => (False.elim (q0 u344))) (fun r0 => r0));
    let u347 : p3461 := (Or.elim h8934 (fun q0 => q0) (fun r0 => (False.elim (r0 u345))));
    let u348 : (¬ p5503) := (Or.elim h50996 (fun q0 => (False.elim (q0 u118))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u182))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u142))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u91))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u239))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u347))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u315))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u123))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u334))) (fun r8 => r8))))))))))))))))));
    let u349 : (¬ p5500) := (Or.elim h9583 (fun q0 => q0) (fun r0 => (False.elim (u348 r0))));
    let u350 : p5506 := (Or.elim h9595 (fun q0 => (False.elim (q0 u64))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u349 q1))) (fun r1 => r1))));
    let u351 : p3868 := (Or.elim h9589 (fun q0 => q0) (fun r0 => (False.elim (r0 u350))));
    let u352 : (¬ p5568) := (Or.elim h54078 (fun q0 => (False.elim (q0 u325))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u351))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u220))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u244))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u346))) (fun r4 => r4))))))))));
    let u353 : (¬ p5567) := (Or.elim h9791 (fun q0 => q0) (fun r0 => (False.elim (u352 r0))));
    let u354 : p5571 := (Or.elim h9803 (fun q0 => (False.elim (q0 u65))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u353 q1))) (fun r1 => r1))));
    let u355 : p3969 := (Or.elim h9797 (fun q0 => q0) (fun r0 => (False.elim (r0 u354))));
    let u356 : (¬ p2220) := (Or.elim h45725 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u192))) (fun r2 => (False.elim (r2 u355))))))));
    let u357 : (¬ p4530) := (Or.elim h7130 (fun q0 => (False.elim (u356 q0))) (fun r0 => r0));
    let u358 : (¬ p2619) := (Or.elim h6704 (fun q0 => (False.elim (q0 u194))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u356 q1))) (fun r1 => r1))));
    let u359 : p4527 := (Or.elim h7136 (fun q0 => (False.elim (q0 u66))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u357 r1))))));
    let u360 : (¬ p4743) := (Or.elim h7704 (fun q0 => (False.elim (u358 q0))) (fun r0 => r0));
    let u361 : p3697 := (Or.elim h7122 (fun q0 => q0) (fun r0 => (False.elim (r0 u359))));
    let u362 : p3696 := (Or.elim h7123 (fun q0 => q0) (fun r0 => (False.elim (r0 u359))));
    let u363 : p4739 := (Or.elim h7710 (fun q0 => (False.elim (q0 u67))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u360 r1))))));
    let u364 : (¬ p2166) := (Or.elim h11852 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u143))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u362))) (fun r2 => (False.elim (r2 u361))))))));
    let u365 : p3694 := (Or.elim h7698 (fun q0 => q0) (fun r0 => (False.elim (r0 u363))));
    let u366 : (¬ p4495) := (Or.elim h7045 (fun q0 => (False.elim (u364 q0))) (fun r0 => r0));
    let u367 : (¬ p3692) := (Or.elim h49801 (fun q0 => (False.elim (q0 u316))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u365))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u215))) (fun r3 => (False.elim (r3 u5))))))))));
    let u368 : p4491 := (Or.elim h7051 (fun q0 => (False.elim (q0 u68))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u366 r1))))));
    let u369 : (¬ p5055) := (Or.elim h8473 (fun q0 => (False.elim (u367 q0))) (fun r0 => r0));
    let u370 : p4492 := (Or.elim h7037 (fun q0 => (False.elim (q0 u368))) (fun r0 => r0));
    let u371 : p5057 := (Or.elim h8485 (fun q0 => (False.elim (q0 u69))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u369 q1))) (fun r1 => r1))));
    let u372 : (¬ p3146) := (Or.elim h62130 (fun q0 => (False.elim (q0 u276))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u185))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u269))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u370))) (fun r4 => (False.elim (r4 u288))))))))))));
    (Or.elim h8479 (fun q0 => (False.elim (u372 q0))) (fun r0 => (False.elim (r0 u371)))))

theorem step66007 (p2192 p2210 p2241 p2563 p3555 p3591 p3957 p4173 p4510 p4511 p4515 p4519 p4520 p4523 p4629 : Prop)
    (h65804 : p4510)
    (h65865 : p4519)
    (h9774 : (¬ p2192) ∨ (¬ p4173))
    (h42642 : (¬ p2241) ∨ (¬ p2563) ∨ (¬ p3555) ∨ (¬ p4173))
    (h7096 : p2192 ∨ (¬ p4515))
    (h7107 : p3555 ∨ (¬ p4520))
    (h7102 : (¬ p4510) ∨ p4511 ∨ p4515)
    (h7119 : (¬ p4519) ∨ p4520 ∨ p4523)
    (h7089 : p3957 ∨ (¬ p4511))
    (h7113 : p2210 ∨ (¬ p4523))
    (h41941 : (¬ p2210) ∨ (¬ p2563) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4629))
    : (¬ p4173) ∨ (¬ p3591) ∨ (¬ p4629) ∨ (¬ p2241) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4173 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4510 := h65804;
    let u6 : p4519 := h65865;
    let u7 : (¬ p2192) := (Or.elim h9774 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : (¬ p3555) := (Or.elim h42642 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u0))))))));
    let u9 : (¬ p4515) := (Or.elim h7096 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u10 : (¬ p4520) := (Or.elim h7107 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : p4511 := (Or.elim h7102 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u9 r1))))));
    let u12 : p4523 := (Or.elim h7119 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => r1))));
    let u13 : p3957 := (Or.elim h7089 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    let u14 : p2210 := (Or.elim h7113 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    (Or.elim h41941 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step66009 (p2122 p2315 p3483 p3821 p3822 p4025 p4618 p4619 p4622 p4623 : Prop)
    (h65720 : p4618)
    (h38128 : p2122 ∨ (¬ p3483) ∨ (¬ p4025))
    (h48783 : (¬ p2315) ∨ (¬ p3483) ∨ (¬ p3821) ∨ (¬ p3822) ∨ (¬ p4623))
    (h7376 : p4025 ∨ (¬ p4619))
    (h7382 : (¬ p4622) ∨ p4623)
    (h7390 : (¬ p4618) ∨ p4619 ∨ p4622)
    : (¬ p3483) ∨ (¬ p2315) ∨ (¬ p3821) ∨ (¬ p3822) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4618 := h65720;
    let u6 : (¬ p4025) := (Or.elim h38128 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => r1))));
    let u7 : (¬ p4623) := (Or.elim h48783 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    let u8 : (¬ p4619) := (Or.elim h7376 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    let u9 : (¬ p4622) := (Or.elim h7382 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h7390 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (False.elim (u9 r1)))))))

theorem step66321 (p2101 p2108 p4464 : Prop)
    (h65610 : p4464)
    (h6963 : p2101 ∨ p2108 ∨ (¬ p4464))
    : p2101 ∨ p2108 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2101) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2108) := (fun h => hn (Or.inr h));
    let u2 : p4464 := h65610;
    (Or.elim h6963 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66324 (p4469 p4470 p4474 : Prop)
    (h65926 : p4469)
    (h6996 : (¬ p4469) ∨ p4470 ∨ p4474)
    : p4474 ∨ p4470 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4474) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4470) := (fun h => hn (Or.inr h));
    let u2 : p4469 := h65926;
    (Or.elim h6996 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66325 (p2135 p2142 p4478 : Prop)
    (h65646 : p4478)
    (h7001 : p2135 ∨ p2142 ∨ (¬ p4478))
    : p2135 ∨ p2142 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2135) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2142) := (fun h => hn (Or.inr h));
    let u2 : p4478 := h65646;
    (Or.elim h7001 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66328 (p4483 p4484 p4487 : Prop)
    (h65737 : p4483)
    (h7034 : (¬ p4483) ∨ p4484 ∨ p4487)
    : p4487 ∨ p4484 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4487) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4484) := (fun h => hn (Or.inr h));
    let u2 : p4483 := h65737;
    (Or.elim h7034 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66329 (p4490 p4491 p4495 : Prop)
    (h65690 : p4490)
    (h7051 : (¬ p4490) ∨ p4491 ∨ p4495)
    : p4491 ∨ p4495 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4491) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4495) := (fun h => hn (Or.inr h));
    let u2 : p4490 := h65690;
    (Or.elim h7051 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66330 (p4499 p4500 p4502 : Prop)
    (h65748 : p4499)
    (h7068 : (¬ p4499) ∨ p4500 ∨ p4502)
    : p4502 ∨ p4500 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4502) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4500) := (fun h => hn (Or.inr h));
    let u2 : p4499 := h65748;
    (Or.elim h7068 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66331 (p4504 p4505 p4508 : Prop)
    (h65791 : p4504)
    (h7085 : (¬ p4504) ∨ p4505 ∨ p4508)
    : p4508 ∨ p4505 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4508) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4505) := (fun h => hn (Or.inr h));
    let u2 : p4504 := h65791;
    (Or.elim h7085 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66332 (p4510 p4511 p4515 : Prop)
    (h65804 : p4510)
    (h7102 : (¬ p4510) ∨ p4511 ∨ p4515)
    : p4511 ∨ p4515 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4511) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4515) := (fun h => hn (Or.inr h));
    let u2 : p4510 := h65804;
    (Or.elim h7102 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66333 (p4519 p4520 p4523 : Prop)
    (h65865 : p4519)
    (h7119 : (¬ p4519) ∨ p4520 ∨ p4523)
    : p4523 ∨ p4520 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4523) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4520) := (fun h => hn (Or.inr h));
    let u2 : p4519 := h65865;
    (Or.elim h7119 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66334 (p4526 p4527 p4530 : Prop)
    (h65705 : p4526)
    (h7136 : (¬ p4526) ∨ p4527 ∨ p4530)
    : p4527 ∨ p4530 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4527) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4530) := (fun h => hn (Or.inr h));
    let u2 : p4526 := h65705;
    (Or.elim h7136 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66335 (p4534 p4535 p4537 : Prop)
    (h65673 : p4534)
    (h7154 : (¬ p4534) ∨ p4535 ∨ p4537)
    : p4535 ∨ p4537 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4535) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4537) := (fun h => hn (Or.inr h));
    let u2 : p4534 := h65673;
    (Or.elim h7154 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66336 (p2244 p2251 p4540 : Prop)
    (h65556 : p4540)
    (h7159 : p2244 ∨ p2251 ∨ (¬ p4540))
    : p2244 ∨ p2251 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2244) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2251) := (fun h => hn (Or.inr h));
    let u2 : p4540 := h65556;
    (Or.elim h7159 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66339 (p4546 p4547 p4551 : Prop)
    (h65938 : p4546)
    (h7197 : (¬ p4546) ∨ p4547 ∨ p4551)
    : p4551 ∨ p4547 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4551) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4547) := (fun h => hn (Or.inr h));
    let u2 : p4546 := h65938;
    (Or.elim h7197 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66340 (p4553 p4554 p4557 : Prop)
    (h65724 : p4553)
    (h7214 : (¬ p4553) ∨ p4554 ∨ p4557)
    : p4554 ∨ p4557 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4554) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4557) := (fun h => hn (Or.inr h));
    let u2 : p4553 := h65724;
    (Or.elim h7214 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66341 (p4561 p4562 p4565 : Prop)
    (h65733 : p4561)
    (h7232 : (¬ p4561) ∨ p4562 ∨ p4565)
    : p4565 ∨ p4562 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4565) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4562) := (fun h => hn (Or.inr h));
    let u2 : p4561 := h65733;
    (Or.elim h7232 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66342 (p4567 p4568 p4571 : Prop)
    (h65887 : p4567)
    (h7249 : (¬ p4567) ∨ p4568 ∨ p4571)
    : p4571 ∨ p4568 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4571) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4568) := (fun h => hn (Or.inr h));
    let u2 : p4567 := h65887;
    (Or.elim h7249 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66343 (p2310 p2317 p4573 : Prop)
    (h65754 : p4573)
    (h7254 : p2310 ∨ p2317 ∨ (¬ p4573))
    : p2317 ∨ p2310 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2317) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2310) := (fun h => hn (Or.inr h));
    let u2 : p4573 := h65754;
    (Or.elim h7254 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66346 (p4578 p4579 p4582 : Prop)
    (h65823 : p4578)
    (h7287 : (¬ p4578) ∨ p4579 ∨ p4582)
    : p4579 ∨ p4582 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4579) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4582) := (fun h => hn (Or.inr h));
    let u2 : p4578 := h65823;
    (Or.elim h7287 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66347 (p4585 p4586 p4589 : Prop)
    (h65767 : p4585)
    (h7304 : (¬ p4585) ∨ p4586 ∨ p4589)
    : p4589 ∨ p4586 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4589) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4586) := (fun h => hn (Or.inr h));
    let u2 : p4585 := h65767;
    (Or.elim h7304 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66348 (p4593 p4594 p4597 : Prop)
    (h65895 : p4593)
    (h7321 : (¬ p4593) ∨ p4594 ∨ p4597)
    : p4597 ∨ p4594 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4597) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4594) := (fun h => hn (Or.inr h));
    let u2 : p4593 := h65895;
    (Or.elim h7321 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66349 (p4599 p4600 p4602 : Prop)
    (h65758 : p4599)
    (h7338 : (¬ p4599) ∨ p4600 ∨ p4602)
    : p4602 ∨ p4600 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4602) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4600) := (fun h => hn (Or.inr h));
    let u2 : p4599 := h65758;
    (Or.elim h7338 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66350 (p4605 p4606 p4609 : Prop)
    (h65771 : p4605)
    (h7355 : (¬ p4605) ∨ p4606 ∨ p4609)
    : p4609 ∨ p4606 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4606) := (fun h => hn (Or.inr h));
    let u2 : p4605 := h65771;
    (Or.elim h7355 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66351 (p4611 p4612 p4615 : Prop)
    (h65763 : p4611)
    (h7373 : (¬ p4611) ∨ p4612 ∨ p4615)
    : p4615 ∨ p4612 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4615) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4612) := (fun h => hn (Or.inr h));
    let u2 : p4611 := h65763;
    (Or.elim h7373 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66352 (p4618 p4619 p4622 : Prop)
    (h65720 : p4618)
    (h7390 : (¬ p4618) ∨ p4619 ∨ p4622)
    : p4619 ∨ p4622 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4622) := (fun h => hn (Or.inr h));
    let u2 : p4618 := h65720;
    (Or.elim h7390 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66353 (p4626 p4627 p4630 : Prop)
    (h65800 : p4626)
    (h7407 : (¬ p4626) ∨ p4627 ∨ p4630)
    : p4627 ∨ p4630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4627) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4630) := (fun h => hn (Or.inr h));
    let u2 : p4626 := h65800;
    (Or.elim h7407 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66354 (p4633 p4634 p4639 : Prop)
    (h65848 : p4633)
    (h7424 : (¬ p4633) ∨ p4634 ∨ p4639)
    : p4634 ∨ p4639 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4634) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4639) := (fun h => hn (Or.inr h));
    let u2 : p4633 := h65848;
    (Or.elim h7424 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66355 (p4642 p4643 p4645 : Prop)
    (h65784 : p4642)
    (h7441 : (¬ p4642) ∨ p4643 ∨ p4645)
    : p4643 ∨ p4645 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4643) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4645) := (fun h => hn (Or.inr h));
    let u2 : p4642 := h65784;
    (Or.elim h7441 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66356 (p4648 p4649 p4651 : Prop)
    (h65881 : p4648)
    (h7459 : (¬ p4648) ∨ p4649 ∨ p4651)
    : p4651 ∨ p4649 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4649) := (fun h => hn (Or.inr h));
    let u2 : p4648 := h65881;
    (Or.elim h7459 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66357 (p4654 p4655 p4659 : Prop)
    (h65944 : p4654)
    (h7476 : (¬ p4654) ∨ p4655 ∨ p4659)
    : p4655 ∨ p4659 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4655) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4659) := (fun h => hn (Or.inr h));
    let u2 : p4654 := h65944;
    (Or.elim h7476 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66358 (p4664 p4665 p4667 : Prop)
    (h65694 : p4664)
    (h7493 : (¬ p4664) ∨ p4665 ∨ p4667)
    : p4665 ∨ p4667 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4665) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4667) := (fun h => hn (Or.inr h));
    let u2 : p4664 := h65694;
    (Or.elim h7493 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66359 (p2473 p2480 p4670 : Prop)
    (h65891 : p4670)
    (h7498 : p2473 ∨ p2480 ∨ (¬ p4670))
    : p2480 ∨ p2473 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2480) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2473) := (fun h => hn (Or.inr h));
    let u2 : p4670 := h65891;
    (Or.elim h7498 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66362 (p2496 p2503 p4676 : Prop)
    (h65820 : p4676)
    (h7524 : p2496 ∨ p2503 ∨ (¬ p4676))
    : p2496 ∨ p2503 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2496) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2503) := (fun h => hn (Or.inr h));
    let u2 : p4676 := h65820;
    (Or.elim h7524 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66365 (p4682 p4683 p4686 : Prop)
    (h65998 : p4682)
    (h7562 : (¬ p4682) ∨ p4683 ∨ p4686)
    : p4683 ∨ p4686 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4683) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4686) := (fun h => hn (Or.inr h));
    let u2 : p4682 := h65998;
    (Or.elim h7562 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66366 (p4691 p4692 p4694 : Prop)
    (h65775 : p4691)
    (h7579 : (¬ p4691) ∨ p4692 ∨ p4694)
    : p4692 ∨ p4694 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4692) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4694) := (fun h => hn (Or.inr h));
    let u2 : p4691 := h65775;
    (Or.elim h7579 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66367 (p4698 p4699 p4703 : Prop)
    (h65844 : p4698)
    (h7596 : (¬ p4698) ∨ p4699 ∨ p4703)
    : p4703 ∨ p4699 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4703) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4699) := (fun h => hn (Or.inr h));
    let u2 : p4698 := h65844;
    (Or.elim h7596 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66368 (p4706 p4707 p4709 : Prop)
    (h65853 : p4706)
    (h7613 : (¬ p4706) ∨ p4707 ∨ p4709)
    : p4709 ∨ p4707 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4709) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4707) := (fun h => hn (Or.inr h));
    let u2 : p4706 := h65853;
    (Or.elim h7613 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66369 (p4713 p4714 p4716 : Prop)
    (h65780 : p4713)
    (h7630 : (¬ p4713) ∨ p4714 ∨ p4716)
    : p4714 ∨ p4716 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4714) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4716) := (fun h => hn (Or.inr h));
    let u2 : p4713 := h65780;
    (Or.elim h7630 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66370 (p2576 p2583 p4719 : Prop)
    (h65841 : p4719)
    (h7636 : p2576 ∨ p2583 ∨ (¬ p4719))
    : p2576 ∨ p2583 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2576) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2583) := (fun h => hn (Or.inr h));
    let u2 : p4719 := h65841;
    (Or.elim h7636 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66373 (p4725 p4726 p4728 : Prop)
    (h65591 : p4725)
    (h7676 : (¬ p4725) ∨ p4726 ∨ p4728)
    : p4728 ∨ p4726 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4728) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4726) := (fun h => hn (Or.inr h));
    let u2 : p4725 := h65591;
    (Or.elim h7676 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66374 (p4731 p4732 p4735 : Prop)
    (h65532 : p4731)
    (h7693 : (¬ p4731) ∨ p4732 ∨ p4735)
    : p4732 ∨ p4735 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4732) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4735) := (fun h => hn (Or.inr h));
    let u2 : p4731 := h65532;
    (Or.elim h7693 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66375 (p4738 p4739 p4743 : Prop)
    (h65617 : p4738)
    (h7710 : (¬ p4738) ∨ p4739 ∨ p4743)
    : p4739 ∨ p4743 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4739) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4743) := (fun h => hn (Or.inr h));
    let u2 : p4738 := h65617;
    (Or.elim h7710 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66376 (p4747 p4748 p4751 : Prop)
    (h65606 : p4747)
    (h7727 : (¬ p4747) ∨ p4748 ∨ p4751)
    : p4751 ∨ p4748 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4751) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4748) := (fun h => hn (Or.inr h));
    let u2 : p4747 := h65606;
    (Or.elim h7727 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66377 (p4754 p4755 p4758 : Prop)
    (h65665 : p4754)
    (h7745 : (¬ p4754) ∨ p4755 ∨ p4758)
    : p4758 ∨ p4755 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4758) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4755) := (fun h => hn (Or.inr h));
    let u2 : p4754 := h65665;
    (Or.elim h7745 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66378 (p2654 p2661 p4762 : Prop)
    (h65836 : p4762)
    (h7750 : p2654 ∨ p2661 ∨ (¬ p4762))
    : p2654 ∨ p2661 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2654) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2661) := (fun h => hn (Or.inr h));
    let u2 : p4762 := h65836;
    (Or.elim h7750 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66381 (p4767 p4768 p4772 : Prop)
    (h65859 : p4767)
    (h7783 : (¬ p4767) ∨ p4768 ∨ p4772)
    : p4772 ∨ p4768 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4772) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4768) := (fun h => hn (Or.inr h));
    let u2 : p4767 := h65859;
    (Or.elim h7783 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66382 (p4775 p4776 p4780 : Prop)
    (h65709 : p4775)
    (h7800 : (¬ p4775) ∨ p4776 ∨ p4780)
    : p4776 ∨ p4780 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4776) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4780) := (fun h => hn (Or.inr h));
    let u2 : p4775 := h65709;
    (Or.elim h7800 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66383 (p4784 p4785 p4788 : Prop)
    (h65602 : p4784)
    (h7817 : (¬ p4784) ∨ p4785 ∨ p4788)
    : p4785 ∨ p4788 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4785) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4788) := (fun h => hn (Or.inr h));
    let u2 : p4784 := h65602;
    (Or.elim h7817 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66384 (p4791 p4792 p4795 : Prop)
    (h65622 : p4791)
    (h7835 : (¬ p4791) ∨ p4792 ∨ p4795)
    : p4792 ∨ p4795 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4792) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4795) := (fun h => hn (Or.inr h));
    let u2 : p4791 := h65622;
    (Or.elim h7835 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66385 (p4798 p4799 p4803 : Prop)
    (h65626 : p4798)
    (h7852 : (¬ p4798) ∨ p4799 ∨ p4803)
    : p4803 ∨ p4799 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4803) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4799) := (fun h => hn (Or.inr h));
    let u2 : p4798 := h65626;
    (Or.elim h7852 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66386 (p4808 p4809 p4812 : Prop)
    (h65831 : p4808)
    (h7869 : (¬ p4808) ∨ p4809 ∨ p4812)
    : p4809 ∨ p4812 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4809) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4812) := (fun h => hn (Or.inr h));
    let u2 : p4808 := h65831;
    (Or.elim h7869 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66387 (p2740 p2747 p4815 : Prop)
    (h65613 : p4815)
    (h7875 : p2740 ∨ p2747 ∨ (¬ p4815))
    : p2740 ∨ p2747 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2740) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2747) := (fun h => hn (Or.inr h));
    let u2 : p4815 := h65613;
    (Or.elim h7875 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66390 (p4821 p4822 p4827 : Prop)
    (h65587 : p4821)
    (h7914 : (¬ p4821) ∨ p4822 ∨ p4827)
    : p4827 ∨ p4822 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4827) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4822) := (fun h => hn (Or.inr h));
    let u2 : p4821 := h65587;
    (Or.elim h7914 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66391 (p2777 p2784 p4833 : Prop)
    (h65923 : p4833)
    (h7920 : p2777 ∨ p2784 ∨ (¬ p4833))
    : p2784 ∨ p2777 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2784) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2777) := (fun h => hn (Or.inr h));
    let u2 : p4833 := h65923;
    (Or.elim h7920 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66394 (p4839 p4840 p4844 : Prop)
    (h65827 : p4839)
    (h7959 : (¬ p4839) ∨ p4840 ∨ p4844)
    : p4844 ∨ p4840 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4844) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4840) := (fun h => hn (Or.inr h));
    let u2 : p4839 := h65827;
    (Or.elim h7959 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66395 (p4855 p4856 p4860 : Prop)
    (h65810 : p4855)
    (h7995 : (¬ p4855) ∨ p4856 ∨ p4860)
    : p4856 ∨ p4860 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4856) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4860) := (fun h => hn (Or.inr h));
    let u2 : p4855 := h65810;
    (Or.elim h7995 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66396 (p4864 p4865 p4868 : Prop)
    (h65716 : p4864)
    (h8012 : (¬ p4864) ∨ p4865 ∨ p4868)
    : p4865 ∨ p4868 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4865) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4868) := (fun h => hn (Or.inr h));
    let u2 : p4864 := h65716;
    (Or.elim h8012 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66397 (p4872 p4873 p4876 : Prop)
    (h65699 : p4872)
    (h8029 : (¬ p4872) ∨ p4873 ∨ p4876)
    : p4873 ∨ p4876 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4873) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4876) := (fun h => hn (Or.inr h));
    let u2 : p4872 := h65699;
    (Or.elim h8029 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66398 (p4879 p4880 p4883 : Prop)
    (h65795 : p4879)
    (h8046 : (¬ p4879) ∨ p4880 ∨ p4883)
    : p4880 ∨ p4883 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4880) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4883) := (fun h => hn (Or.inr h));
    let u2 : p4879 := h65795;
    (Or.elim h8046 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66399 (p4886 p4887 p4890 : Prop)
    (h65741 : p4886)
    (h8063 : (¬ p4886) ∨ p4887 ∨ p4890)
    : p4887 ∨ p4890 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4887) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4890) := (fun h => hn (Or.inr h));
    let u2 : p4886 := h65741;
    (Or.elim h8063 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66400 (p4892 p4893 p4896 : Prop)
    (h65630 : p4892)
    (h8080 : (¬ p4892) ∨ p4893 ∨ p4896)
    : p4896 ∨ p4893 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4896) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4893) := (fun h => hn (Or.inr h));
    let u2 : p4892 := h65630;
    (Or.elim h8080 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66401 (p4899 p4900 p4903 : Prop)
    (h65649 : p4899)
    (h8098 : (¬ p4899) ∨ p4900 ∨ p4903)
    : p4903 ∨ p4900 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4903) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4900) := (fun h => hn (Or.inr h));
    let u2 : p4899 := h65649;
    (Or.elim h8098 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66402 (p4907 p4908 p4912 : Prop)
    (h65681 : p4907)
    (h8116 : (¬ p4907) ∨ p4908 ∨ p4912)
    : p4912 ∨ p4908 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4912) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4908) := (fun h => hn (Or.inr h));
    let u2 : p4907 := h65681;
    (Or.elim h8116 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66403 (p4915 p4916 p4918 : Prop)
    (h65729 : p4915)
    (h8133 : (¬ p4915) ∨ p4916 ∨ p4918)
    : p4916 ∨ p4918 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4916) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4918) := (fun h => hn (Or.inr h));
    let u2 : p4915 := h65729;
    (Or.elim h8133 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66404 (p4920 p4921 p4923 : Prop)
    (h65980 : p4920)
    (h8150 : (¬ p4920) ∨ p4921 ∨ p4923)
    : p4923 ∨ p4921 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4923) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4921) := (fun h => hn (Or.inr h));
    let u2 : p4920 := h65980;
    (Or.elim h8150 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66405 (p2925 p2932 p4925 : Prop)
    (h65902 : p4925)
    (h8155 : p2925 ∨ p2932 ∨ (¬ p4925))
    : p2932 ∨ p2925 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2932) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2925) := (fun h => hn (Or.inr h));
    let u2 : p4925 := h65902;
    (Or.elim h8155 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66408 (p2949 p2956 p4931 : Prop)
    (h65687 : p4931)
    (h8182 : p2949 ∨ p2956 ∨ (¬ p4931))
    : p2956 ∨ p2949 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2956) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2949) := (fun h => hn (Or.inr h));
    let u2 : p4931 := h65687;
    (Or.elim h8182 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66411 (p4936 p4937 p4941 : Prop)
    (h65677 : p4936)
    (h8218 : (¬ p4936) ∨ p4937 ∨ p4941)
    : p4937 ∨ p4941 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4937) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4941) := (fun h => hn (Or.inr h));
    let u2 : p4936 := h65677;
    (Or.elim h8218 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66412 (p4945 p4946 p4951 : Prop)
    (h65669 : p4945)
    (h8235 : (¬ p4945) ∨ p4946 ∨ p4951)
    : p4946 ∨ p4951 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4951) := (fun h => hn (Or.inr h));
    let u2 : p4945 := h65669;
    (Or.elim h8235 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66413 (p4955 p4956 p4958 : Prop)
    (h65661 : p4955)
    (h8252 : (¬ p4955) ∨ p4956 ∨ p4958)
    : p4956 ∨ p4958 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4956) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4958) := (fun h => hn (Or.inr h));
    let u2 : p4955 := h65661;
    (Or.elim h8252 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66414 (p4961 p4962 p4966 : Prop)
    (h65657 : p4961)
    (h8269 : (¬ p4961) ∨ p4962 ∨ p4966)
    : p4966 ∨ p4962 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4966) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4962) := (fun h => hn (Or.inr h));
    let u2 : p4961 := h65657;
    (Or.elim h8269 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66415 (p4970 p4971 p4974 : Prop)
    (h65653 : p4970)
    (h8286 : (¬ p4970) ∨ p4971 ∨ p4974)
    : p4974 ∨ p4971 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4974) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4971) := (fun h => hn (Or.inr h));
    let u2 : p4970 := h65653;
    (Or.elim h8286 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66416 (p3030 p3036 p4977 : Prop)
    (h65995 : p4977)
    (h8291 : p3030 ∨ p3036 ∨ (¬ p4977))
    : p3036 ∨ p3030 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3036) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3030) := (fun h => hn (Or.inr h));
    let u2 : p4977 := h65995;
    (Or.elim h8291 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66419 (p4982 p4983 p4987 : Prop)
    (h65642 : p4982)
    (h8327 : (¬ p4982) ∨ p4983 ∨ p4987)
    : p4983 ∨ p4987 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4983) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4987) := (fun h => hn (Or.inr h));
    let u2 : p4982 := h65642;
    (Or.elim h8327 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66420 (p4991 p4992 p4996 : Prop)
    (h65638 : p4991)
    (h8346 : (¬ p4991) ∨ p4992 ∨ p4996)
    : p4992 ∨ p4996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4996) := (fun h => hn (Or.inr h));
    let u2 : p4991 := h65638;
    (Or.elim h8346 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66421 (p4999 p5000 p5003 : Prop)
    (h65597 : p4999)
    (h8363 : (¬ p4999) ∨ p5000 ∨ p5003)
    : p5003 ∨ p5000 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5003) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5000) := (fun h => hn (Or.inr h));
    let u2 : p4999 := h65597;
    (Or.elim h8363 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66422 (p5006 p5007 p5010 : Prop)
    (h65634 : p5006)
    (h8381 : (¬ p5006) ∨ p5007 ∨ p5010)
    : p5007 ∨ p5010 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5007) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5010) := (fun h => hn (Or.inr h));
    let u2 : p5006 := h65634;
    (Or.elim h8381 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66423 (p5013 p5014 p5019 : Prop)
    (h65583 : p5013)
    (h8398 : (¬ p5013) ∨ p5014 ∨ p5019)
    : p5019 ∨ p5014 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5019) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5014) := (fun h => hn (Or.inr h));
    let u2 : p5013 := h65583;
    (Or.elim h8398 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66424 (p5023 p5024 p5029 : Prop)
    (h65579 : p5023)
    (h8417 : (¬ p5023) ∨ p5024 ∨ p5029)
    : p5024 ∨ p5029 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5024) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5029) := (fun h => hn (Or.inr h));
    let u2 : p5023 := h65579;
    (Or.elim h8417 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66425 (p5034 p5035 p5037 : Prop)
    (h65575 : p5034)
    (h8434 : (¬ p5034) ∨ p5035 ∨ p5037)
    : p5035 ∨ p5037 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5035) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5037) := (fun h => hn (Or.inr h));
    let u2 : p5034 := h65575;
    (Or.elim h8434 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66426 (p5041 p5042 p5044 : Prop)
    (h65571 : p5041)
    (h8451 : (¬ p5041) ∨ p5042 ∨ p5044)
    : p5042 ∨ p5044 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5042) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5044) := (fun h => hn (Or.inr h));
    let u2 : p5041 := h65571;
    (Or.elim h8451 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66427 (p5047 p5048 p5050 : Prop)
    (h65567 : p5047)
    (h8468 : (¬ p5047) ∨ p5048 ∨ p5050)
    : p5048 ∨ p5050 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5048) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5050) := (fun h => hn (Or.inr h));
    let u2 : p5047 := h65567;
    (Or.elim h8468 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66428 (p5054 p5055 p5057 : Prop)
    (h65563 : p5054)
    (h8485 : (¬ p5054) ∨ p5055 ∨ p5057)
    : p5055 ∨ p5057 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5055) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5057) := (fun h => hn (Or.inr h));
    let u2 : p5054 := h65563;
    (Or.elim h8485 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66429 (p5060 p5061 p5064 : Prop)
    (h65559 : p5060)
    (h8502 : (¬ p5060) ∨ p5061 ∨ p5064)
    : p5061 ∨ p5064 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5061) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5064) := (fun h => hn (Or.inr h));
    let u2 : p5060 := h65559;
    (Or.elim h8502 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66430 (p5072 p5073 p5077 : Prop)
    (h65552 : p5072)
    (h8546 : (¬ p5072) ∨ p5073 ∨ p5077)
    : p5073 ∨ p5077 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5077) := (fun h => hn (Or.inr h));
    let u2 : p5072 := h65552;
    (Or.elim h8546 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66431 (p5080 p5081 p5084 : Prop)
    (h65548 : p5080)
    (h8564 : (¬ p5080) ∨ p5081 ∨ p5084)
    : p5081 ∨ p5084 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5081) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5084) := (fun h => hn (Or.inr h));
    let u2 : p5080 := h65548;
    (Or.elim h8564 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66432 (p5088 p5089 p5092 : Prop)
    (h65544 : p5088)
    (h8583 : (¬ p5088) ∨ p5089 ∨ p5092)
    : p5089 ∨ p5092 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5089) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5092) := (fun h => hn (Or.inr h));
    let u2 : p5088 := h65544;
    (Or.elim h8583 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66433 (p3225 p3231 p5095 : Prop)
    (h65814 : p5095)
    (h8588 : p3225 ∨ p3231 ∨ (¬ p5095))
    : p3225 ∨ p3231 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3225) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3231) := (fun h => hn (Or.inr h));
    let u2 : p5095 := h65814;
    (Or.elim h8588 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66436 (p5100 p5101 p5103 : Prop)
    (h65540 : p5100)
    (h8621 : (¬ p5100) ∨ p5101 ∨ p5103)
    : p5101 ∨ p5103 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5101) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5103) := (fun h => hn (Or.inr h));
    let u2 : p5100 := h65540;
    (Or.elim h8621 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66437 (p5105 p5106 p5110 : Prop)
    (h65536 : p5105)
    (h8640 : (¬ p5105) ∨ p5106 ∨ p5110)
    : p5106 ∨ p5110 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5106) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5110) := (fun h => hn (Or.inr h));
    let u2 : p5105 := h65536;
    (Or.elim h8640 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66438 (p5114 p5115 p5120 : Prop)
    (h65528 : p5114)
    (h8658 : (¬ p5114) ∨ p5115 ∨ p5120)
    : p5115 ∨ p5120 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5115) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5120) := (fun h => hn (Or.inr h));
    let u2 : p5114 := h65528;
    (Or.elim h8658 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66439 (p5124 p5125 p5130 : Prop)
    (h65524 : p5124)
    (h8676 : (¬ p5124) ∨ p5125 ∨ p5130)
    : p5125 ∨ p5130 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5125) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5130) := (fun h => hn (Or.inr h));
    let u2 : p5124 := h65524;
    (Or.elim h8676 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66440 (p5139 p5140 p5143 : Prop)
    (h65520 : p5139)
    (h8717 : (¬ p5139) ∨ p5140 ∨ p5143)
    : p5140 ∨ p5143 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5140) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5143) := (fun h => hn (Or.inr h));
    let u2 : p5139 := h65520;
    (Or.elim h8717 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66441 (p5146 p5147 p5151 : Prop)
    (h65516 : p5146)
    (h8735 : (¬ p5146) ∨ p5147 ∨ p5151)
    : p5147 ∨ p5151 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5147) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5151) := (fun h => hn (Or.inr h));
    let u2 : p5146 := h65516;
    (Or.elim h8735 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66442 (p5156 p5157 p5163 : Prop)
    (h65512 : p5156)
    (h8753 : (¬ p5156) ∨ p5157 ∨ p5163)
    : p5157 ∨ p5163 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5157) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5163) := (fun h => hn (Or.inr h));
    let u2 : p5156 := h65512;
    (Or.elim h8753 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66443 (p5168 p5169 p5174 : Prop)
    (h65508 : p5168)
    (h8771 : (¬ p5168) ∨ p5169 ∨ p5174)
    : p5169 ∨ p5174 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5169) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5174) := (fun h => hn (Or.inr h));
    let u2 : p5168 := h65508;
    (Or.elim h8771 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66444 (p5179 p5180 p5185 : Prop)
    (h65504 : p5179)
    (h8788 : (¬ p5179) ∨ p5180 ∨ p5185)
    : p5180 ∨ p5185 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5180) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5185) := (fun h => hn (Or.inr h));
    let u2 : p5179 := h65504;
    (Or.elim h8788 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66445 (p5188 p5189 p5192 : Prop)
    (h65500 : p5188)
    (h8811 : (¬ p5188) ∨ p5189 ∨ p5192)
    : p5189 ∨ p5192 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5192) := (fun h => hn (Or.inr h));
    let u2 : p5188 := h65500;
    (Or.elim h8811 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66446 (p5195 p5196 p5200 : Prop)
    (h65496 : p5195)
    (h8828 : (¬ p5195) ∨ p5196 ∨ p5200)
    : p5196 ∨ p5200 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5196) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5200) := (fun h => hn (Or.inr h));
    let u2 : p5195 := h65496;
    (Or.elim h8828 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66447 (p5204 p5205 p5209 : Prop)
    (h65492 : p5204)
    (h8845 : (¬ p5204) ∨ p5205 ∨ p5209)
    : p5209 ∨ p5205 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5209) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5205) := (fun h => hn (Or.inr h));
    let u2 : p5204 := h65492;
    (Or.elim h8845 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66448 (p5212 p5213 p5215 : Prop)
    (h65488 : p5212)
    (h8865 : (¬ p5212) ∨ p5213 ∨ p5215)
    : p5215 ∨ p5213 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5215) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5213) := (fun h => hn (Or.inr h));
    let u2 : p5212 := h65488;
    (Or.elim h8865 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66449 (p5218 p5219 p5223 : Prop)
    (h65484 : p5218)
    (h8885 : (¬ p5218) ∨ p5219 ∨ p5223)
    : p5219 ∨ p5223 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5219) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5223) := (fun h => hn (Or.inr h));
    let u2 : p5218 := h65484;
    (Or.elim h8885 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66450 (p5226 p5227 p5232 : Prop)
    (h65480 : p5226)
    (h8905 : (¬ p5226) ∨ p5227 ∨ p5232)
    : p5227 ∨ p5232 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5227) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5232) := (fun h => hn (Or.inr h));
    let u2 : p5226 := h65480;
    (Or.elim h8905 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66451 (p5237 p5238 p5241 : Prop)
    (h65476 : p5237)
    (h8923 : (¬ p5237) ∨ p5238 ∨ p5241)
    : p5241 ∨ p5238 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5238) := (fun h => hn (Or.inr h));
    let u2 : p5237 := h65476;
    (Or.elim h8923 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66452 (p5245 p5246 p5251 : Prop)
    (h65472 : p5245)
    (h8940 : (¬ p5245) ∨ p5246 ∨ p5251)
    : p5246 ∨ p5251 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5251) := (fun h => hn (Or.inr h));
    let u2 : p5245 := h65472;
    (Or.elim h8940 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66453 (p5255 p5256 p5259 : Prop)
    (h65468 : p5255)
    (h8957 : (¬ p5255) ∨ p5256 ∨ p5259)
    : p5259 ∨ p5256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5259) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5256) := (fun h => hn (Or.inr h));
    let u2 : p5255 := h65468;
    (Or.elim h8957 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step66454 (p5262 p5263 p5268 : Prop)
    (h65464 : p5262)
    (h8974 : (¬ p5262) ∨ p5263 ∨ p5268)
    : p5263 ∨ p5268 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5263) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5268) := (fun h => hn (Or.inr h));
    let u2 : p5262 := h65464;
    (Or.elim h8974 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66455 (p5272 p5273 p5277 : Prop)
    (h65460 : p5272)
    (h8993 : (¬ p5272) ∨ p5273 ∨ p5277)
    : p5273 ∨ p5277 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5273) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5277) := (fun h => hn (Or.inr h));
    let u2 : p5272 := h65460;
    (Or.elim h8993 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66456 (p5280 p5281 p5287 : Prop)
    (h65456 : p5280)
    (h9014 : (¬ p5280) ∨ p5281 ∨ p5287)
    : p5281 ∨ p5287 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5281) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5287) := (fun h => hn (Or.inr h));
    let u2 : p5280 := h65456;
    (Or.elim h9014 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66457 (p5292 p5293 p5298 : Prop)
    (h65452 : p5292)
    (h9031 : (¬ p5292) ∨ p5293 ∨ p5298)
    : p5293 ∨ p5298 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5293) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5298) := (fun h => hn (Or.inr h));
    let u2 : p5292 := h65452;
    (Or.elim h9031 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66458 (p5303 p5304 p5306 : Prop)
    (h65448 : p5303)
    (h9050 : (¬ p5303) ∨ p5304 ∨ p5306)
    : p5304 ∨ p5306 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5304) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5306) := (fun h => hn (Or.inr h));
    let u2 : p5303 := h65448;
    (Or.elim h9050 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66459 (p5310 p5311 p5314 : Prop)
    (h65444 : p5310)
    (h9073 : (¬ p5310) ∨ p5311 ∨ p5314)
    : p5311 ∨ p5314 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5311) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5314) := (fun h => hn (Or.inr h));
    let u2 : p5310 := h65444;
    (Or.elim h9073 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66460 (p5319 p5320 p5323 : Prop)
    (h65440 : p5319)
    (h9114 : (¬ p5319) ∨ p5320 ∨ p5323)
    : p5320 ∨ p5323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5320) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5323) := (fun h => hn (Or.inr h));
    let u2 : p5319 := h65440;
    (Or.elim h9114 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66461 (p5326 p5327 p5331 : Prop)
    (h65436 : p5326)
    (h9170 : (¬ p5326) ∨ p5327 ∨ p5331)
    : p5327 ∨ p5331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5327) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5331) := (fun h => hn (Or.inr h));
    let u2 : p5326 := h65436;
    (Or.elim h9170 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66462 (p5336 p5337 p5342 : Prop)
    (h65432 : p5336)
    (h9187 : (¬ p5336) ∨ p5337 ∨ p5342)
    : p5337 ∨ p5342 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5337) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5342) := (fun h => hn (Or.inr h));
    let u2 : p5336 := h65432;
    (Or.elim h9187 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66463 (p5347 p5348 p5351 : Prop)
    (h65428 : p5347)
    (h9204 : (¬ p5347) ∨ p5348 ∨ p5351)
    : p5348 ∨ p5351 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5348) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5351) := (fun h => hn (Or.inr h));
    let u2 : p5347 := h65428;
    (Or.elim h9204 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66464 (p5355 p5356 p5361 : Prop)
    (h65424 : p5355)
    (h9223 : (¬ p5355) ∨ p5356 ∨ p5361)
    : p5356 ∨ p5361 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5356) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5361) := (fun h => hn (Or.inr h));
    let u2 : p5355 := h65424;
    (Or.elim h9223 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66465 (p5366 p5367 p5372 : Prop)
    (h65420 : p5366)
    (h9247 : (¬ p5366) ∨ p5367 ∨ p5372)
    : p5367 ∨ p5372 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5367) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5372) := (fun h => hn (Or.inr h));
    let u2 : p5366 := h65420;
    (Or.elim h9247 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66466 (p5376 p5377 p5382 : Prop)
    (h65416 : p5376)
    (h9267 : (¬ p5376) ∨ p5377 ∨ p5382)
    : p5377 ∨ p5382 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5377) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5382) := (fun h => hn (Or.inr h));
    let u2 : p5376 := h65416;
    (Or.elim h9267 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66467 (p5385 p5386 p5390 : Prop)
    (h65412 : p5385)
    (h9303 : (¬ p5385) ∨ p5386 ∨ p5390)
    : p5386 ∨ p5390 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5386) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5390) := (fun h => hn (Or.inr h));
    let u2 : p5385 := h65412;
    (Or.elim h9303 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66468 (p5395 p5396 p5401 : Prop)
    (h65408 : p5395)
    (h9320 : (¬ p5395) ∨ p5396 ∨ p5401)
    : p5396 ∨ p5401 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5396) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5401) := (fun h => hn (Or.inr h));
    let u2 : p5395 := h65408;
    (Or.elim h9320 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66469 (p5406 p5407 p5412 : Prop)
    (h65404 : p5406)
    (h9351 : (¬ p5406) ∨ p5407 ∨ p5412)
    : p5407 ∨ p5412 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5407) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5412) := (fun h => hn (Or.inr h));
    let u2 : p5406 := h65404;
    (Or.elim h9351 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66470 (p5417 p5418 p5424 : Prop)
    (h65400 : p5417)
    (h9368 : (¬ p5417) ∨ p5418 ∨ p5424)
    : p5418 ∨ p5424 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5418) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5424) := (fun h => hn (Or.inr h));
    let u2 : p5417 := h65400;
    (Or.elim h9368 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66471 (p5429 p5430 p5436 : Prop)
    (h65396 : p5429)
    (h9386 : (¬ p5429) ∨ p5430 ∨ p5436)
    : p5430 ∨ p5436 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5430) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5436) := (fun h => hn (Or.inr h));
    let u2 : p5429 := h65396;
    (Or.elim h9386 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66472 (p5441 p5442 p5446 : Prop)
    (h65392 : p5441)
    (h9404 : (¬ p5441) ∨ p5442 ∨ p5446)
    : p5442 ∨ p5446 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5442) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5446) := (fun h => hn (Or.inr h));
    let u2 : p5441 := h65392;
    (Or.elim h9404 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66473 (p5451 p5452 p5457 : Prop)
    (h65388 : p5451)
    (h9436 : (¬ p5451) ∨ p5452 ∨ p5457)
    : p5452 ∨ p5457 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5452) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5457) := (fun h => hn (Or.inr h));
    let u2 : p5451 := h65388;
    (Or.elim h9436 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66474 (p3770 p3777 p5462 : Prop)
    (h65713 : p5462)
    (h9454 : p3770 ∨ p3777 ∨ (¬ p5462))
    : p3777 ∨ p3770 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3777) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3770) := (fun h => hn (Or.inr h));
    let u2 : p5462 := h65713;
    (Or.elim h9454 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step66477 (p5468 p5469 p5474 : Prop)
    (h65384 : p5468)
    (h9493 : (¬ p5468) ∨ p5469 ∨ p5474)
    : p5469 ∨ p5474 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5469) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5474) := (fun h => hn (Or.inr h));
    let u2 : p5468 := h65384;
    (Or.elim h9493 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66478 (p5484 p5485 p5490 : Prop)
    (h65380 : p5484)
    (h9545 : (¬ p5484) ∨ p5485 ∨ p5490)
    : p5485 ∨ p5490 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5485) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5490) := (fun h => hn (Or.inr h));
    let u2 : p5484 := h65380;
    (Or.elim h9545 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66479 (p5499 p5500 p5506 : Prop)
    (h65376 : p5499)
    (h9595 : (¬ p5499) ∨ p5500 ∨ p5506)
    : p5500 ∨ p5506 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5500) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5506) := (fun h => hn (Or.inr h));
    let u2 : p5499 := h65376;
    (Or.elim h9595 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66480 (p5511 p5512 p5517 : Prop)
    (h65372 : p5511)
    (h9634 : (¬ p5511) ∨ p5512 ∨ p5517)
    : p5512 ∨ p5517 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5512) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5517) := (fun h => hn (Or.inr h));
    let u2 : p5511 := h65372;
    (Or.elim h9634 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66482 (p5532 p5533 p5538 : Prop)
    (h65364 : p5532)
    (h9673 : (¬ p5532) ∨ p5533 ∨ p5538)
    : p5533 ∨ p5538 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5533) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5538) := (fun h => hn (Or.inr h));
    let u2 : p5532 := h65364;
    (Or.elim h9673 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66483 (p5543 p5544 p5549 : Prop)
    (h65360 : p5543)
    (h9715 : (¬ p5543) ∨ p5544 ∨ p5549)
    : p5544 ∨ p5549 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5544) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5549) := (fun h => hn (Or.inr h));
    let u2 : p5543 := h65360;
    (Or.elim h9715 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66484 (p5554 p5555 p5561 : Prop)
    (h65356 : p5554)
    (h9733 : (¬ p5554) ∨ p5555 ∨ p5561)
    : p5555 ∨ p5561 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5555) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5561) := (fun h => hn (Or.inr h));
    let u2 : p5554 := h65356;
    (Or.elim h9733 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66485 (p5566 p5567 p5571 : Prop)
    (h65352 : p5566)
    (h9803 : (¬ p5566) ∨ p5567 ∨ p5571)
    : p5567 ∨ p5571 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5567) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5571) := (fun h => hn (Or.inr h));
    let u2 : p5566 := h65352;
    (Or.elim h9803 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66486 (p5576 p5577 p5583 : Prop)
    (h65348 : p5576)
    (h9820 : (¬ p5576) ∨ p5577 ∨ p5583)
    : p5577 ∨ p5583 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5577) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5583) := (fun h => hn (Or.inr h));
    let u2 : p5576 := h65348;
    (Or.elim h9820 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66487 (p5588 p5589 p5593 : Prop)
    (h65344 : p5588)
    (h9850 : (¬ p5588) ∨ p5589 ∨ p5593)
    : p5589 ∨ p5593 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5589) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5593) := (fun h => hn (Or.inr h));
    let u2 : p5588 := h65344;
    (Or.elim h9850 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66488 (p5596 p5597 p5603 : Prop)
    (h65340 : p5596)
    (h9876 : (¬ p5596) ∨ p5597 ∨ p5603)
    : p5597 ∨ p5603 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5597) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5603) := (fun h => hn (Or.inr h));
    let u2 : p5596 := h65340;
    (Or.elim h9876 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66489 (p5608 p5609 p5615 : Prop)
    (h65336 : p5608)
    (h9893 : (¬ p5608) ∨ p5609 ∨ p5615)
    : p5609 ∨ p5615 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5615) := (fun h => hn (Or.inr h));
    let u2 : p5608 := h65336;
    (Or.elim h9893 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66490 (p5620 p5621 p5626 : Prop)
    (h65332 : p5620)
    (h9969 : (¬ p5620) ∨ p5621 ∨ p5626)
    : p5621 ∨ p5626 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5621) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5626) := (fun h => hn (Or.inr h));
    let u2 : p5620 := h65332;
    (Or.elim h9969 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66491 (p5631 p5632 p5637 : Prop)
    (h65328 : p5631)
    (h9986 : (¬ p5631) ∨ p5632 ∨ p5637)
    : p5632 ∨ p5637 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5632) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5637) := (fun h => hn (Or.inr h));
    let u2 : p5631 := h65328;
    (Or.elim h9986 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66492 (p5642 p5643 p5648 : Prop)
    (h65324 : p5642)
    (h10013 : (¬ p5642) ∨ p5643 ∨ p5648)
    : p5643 ∨ p5648 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5643) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5648) := (fun h => hn (Or.inr h));
    let u2 : p5642 := h65324;
    (Or.elim h10013 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66493 (p5658 p5659 p5663 : Prop)
    (h65320 : p5658)
    (h10131 : (¬ p5658) ∨ p5659 ∨ p5663)
    : p5659 ∨ p5663 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5659) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5663) := (fun h => hn (Or.inr h));
    let u2 : p5658 := h65320;
    (Or.elim h10131 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66494 (p5668 p5669 p5673 : Prop)
    (h65316 : p5668)
    (h10167 : (¬ p5668) ∨ p5669 ∨ p5673)
    : p5669 ∨ p5673 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5669) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5673) := (fun h => hn (Or.inr h));
    let u2 : p5668 := h65316;
    (Or.elim h10167 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66495 (p5677 p5678 p5684 : Prop)
    (h65312 : p5677)
    (h10200 : (¬ p5677) ∨ p5678 ∨ p5684)
    : p5678 ∨ p5684 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5678) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5684) := (fun h => hn (Or.inr h));
    let u2 : p5677 := h65312;
    (Or.elim h10200 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66496 (p5689 p5690 p5696 : Prop)
    (h65308 : p5689)
    (h10236 : (¬ p5689) ∨ p5690 ∨ p5696)
    : p5690 ∨ p5696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5690) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5696) := (fun h => hn (Or.inr h));
    let u2 : p5689 := h65308;
    (Or.elim h10236 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66498 (p5713 p5714 p5720 : Prop)
    (h65300 : p5713)
    (h10443 : (¬ p5713) ∨ p5714 ∨ p5720)
    : p5714 ∨ p5720 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5714) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5720) := (fun h => hn (Or.inr h));
    let u2 : p5713 := h65300;
    (Or.elim h10443 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66499 (p5725 p5726 p5731 : Prop)
    (h65296 : p5725)
    (h10539 : (¬ p5725) ∨ p5726 ∨ p5731)
    : p5726 ∨ p5731 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5726) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5731) := (fun h => hn (Or.inr h));
    let u2 : p5725 := h65296;
    (Or.elim h10539 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66500 (p5736 p5737 p5743 : Prop)
    (h65292 : p5736)
    (h10664 : (¬ p5736) ∨ p5737 ∨ p5743)
    : p5737 ∨ p5743 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5743) := (fun h => hn (Or.inr h));
    let u2 : p5736 := h65292;
    (Or.elim h10664 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step66504 (p5787 p5788 p5789 : Prop)
    (h65927 : p5787)
    (h11745 : (¬ p5787) ∨ (¬ p5788) ∨ (¬ p5789))
    : (¬ p5789) ∨ (¬ p5788) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5789 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5788 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5787 := h65927;
    (Or.elim h11745 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66505 (p5790 p5791 p5792 : Prop)
    (h65738 : p5790)
    (h11763 : (¬ p5790) ∨ (¬ p5791) ∨ (¬ p5792))
    : (¬ p5792) ∨ (¬ p5791) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5792 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5791 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5790 := h65738;
    (Or.elim h11763 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66506 (p5793 p5794 p5795 : Prop)
    (h65691 : p5793)
    (h11780 : (¬ p5793) ∨ (¬ p5794) ∨ (¬ p5795))
    : (¬ p5794) ∨ (¬ p5795) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5794 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5795 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5793 := h65691;
    (Or.elim h11780 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66507 (p5796 p5797 p5798 : Prop)
    (h65749 : p5796)
    (h11797 : (¬ p5796) ∨ (¬ p5797) ∨ (¬ p5798))
    : (¬ p5798) ∨ (¬ p5797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5798 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5797 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5796 := h65749;
    (Or.elim h11797 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66508 (p5799 p5800 p5801 : Prop)
    (h65792 : p5799)
    (h11814 : (¬ p5799) ∨ (¬ p5800) ∨ (¬ p5801))
    : (¬ p5801) ∨ (¬ p5800) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5801 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5800 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5799 := h65792;
    (Or.elim h11814 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66509 (p5802 p5803 p5804 : Prop)
    (h65805 : p5802)
    (h11831 : (¬ p5802) ∨ (¬ p5803) ∨ (¬ p5804))
    : (¬ p5803) ∨ (¬ p5804) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5803 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5804 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5802 := h65805;
    (Or.elim h11831 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66510 (p5805 p5806 p5807 : Prop)
    (h65866 : p5805)
    (h11849 : (¬ p5805) ∨ (¬ p5806) ∨ (¬ p5807))
    : (¬ p5807) ∨ (¬ p5806) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5806 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5805 := h65866;
    (Or.elim h11849 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66511 (p5808 p5809 p5810 : Prop)
    (h65706 : p5808)
    (h11867 : (¬ p5808) ∨ (¬ p5809) ∨ (¬ p5810))
    : (¬ p5809) ∨ (¬ p5810) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5809 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5810 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5808 := h65706;
    (Or.elim h11867 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66512 (p5811 p5812 p5813 : Prop)
    (h65674 : p5811)
    (h11884 : (¬ p5811) ∨ (¬ p5812) ∨ (¬ p5813))
    : (¬ p5812) ∨ (¬ p5813) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5812 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5813 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5811 := h65674;
    (Or.elim h11884 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66513 (p5814 p5815 p5816 : Prop)
    (h65939 : p5814)
    (h11902 : (¬ p5814) ∨ (¬ p5815) ∨ (¬ p5816))
    : (¬ p5816) ∨ (¬ p5815) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5816 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5815 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5814 := h65939;
    (Or.elim h11902 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66514 (p5817 p5818 p5819 : Prop)
    (h65725 : p5817)
    (h11919 : (¬ p5817) ∨ (¬ p5818) ∨ (¬ p5819))
    : (¬ p5818) ∨ (¬ p5819) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5818 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5819 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5817 := h65725;
    (Or.elim h11919 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66515 (p5820 p5821 p5822 : Prop)
    (h65734 : p5820)
    (h11936 : (¬ p5820) ∨ (¬ p5821) ∨ (¬ p5822))
    : (¬ p5822) ∨ (¬ p5821) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5822 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5821 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5820 := h65734;
    (Or.elim h11936 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66516 (p5823 p5824 p5825 : Prop)
    (h65888 : p5823)
    (h11954 : (¬ p5823) ∨ (¬ p5824) ∨ (¬ p5825))
    : (¬ p5825) ∨ (¬ p5824) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5825 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5824 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5823 := h65888;
    (Or.elim h11954 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66517 (p5826 p5827 p5828 : Prop)
    (h65824 : p5826)
    (h11971 : (¬ p5826) ∨ (¬ p5827) ∨ (¬ p5828))
    : (¬ p5827) ∨ (¬ p5828) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5827 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5828 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5826 := h65824;
    (Or.elim h11971 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66518 (p5829 p5830 p5831 : Prop)
    (h65768 : p5829)
    (h11988 : (¬ p5829) ∨ (¬ p5830) ∨ (¬ p5831))
    : (¬ p5831) ∨ (¬ p5830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5831 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5830 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5829 := h65768;
    (Or.elim h11988 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66519 (p5832 p5833 p5834 : Prop)
    (h65896 : p5832)
    (h12005 : (¬ p5832) ∨ (¬ p5833) ∨ (¬ p5834))
    : (¬ p5834) ∨ (¬ p5833) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5834 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5833 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5832 := h65896;
    (Or.elim h12005 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66520 (p5835 p5836 p5837 : Prop)
    (h65759 : p5835)
    (h12024 : (¬ p5835) ∨ (¬ p5836) ∨ (¬ p5837))
    : (¬ p5837) ∨ (¬ p5836) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5837 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5836 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5835 := h65759;
    (Or.elim h12024 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66521 (p5838 p5839 p5840 : Prop)
    (h65772 : p5838)
    (h12043 : (¬ p5838) ∨ (¬ p5839) ∨ (¬ p5840))
    : (¬ p5840) ∨ (¬ p5839) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5840 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5839 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5838 := h65772;
    (Or.elim h12043 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66522 (p5841 p5842 p5843 : Prop)
    (h65764 : p5841)
    (h12060 : (¬ p5841) ∨ (¬ p5842) ∨ (¬ p5843))
    : (¬ p5843) ∨ (¬ p5842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5843 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5842 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5841 := h65764;
    (Or.elim h12060 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66523 (p5844 p5845 p5846 : Prop)
    (h65721 : p5844)
    (h12078 : (¬ p5844) ∨ (¬ p5845) ∨ (¬ p5846))
    : (¬ p5845) ∨ (¬ p5846) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5845 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5846 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5844 := h65721;
    (Or.elim h12078 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66524 (p5847 p5848 p5849 : Prop)
    (h65801 : p5847)
    (h12096 : (¬ p5847) ∨ (¬ p5848) ∨ (¬ p5849))
    : (¬ p5848) ∨ (¬ p5849) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5848 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5849 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5847 := h65801;
    (Or.elim h12096 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66525 (p5850 p5851 p5852 : Prop)
    (h65849 : p5850)
    (h12114 : (¬ p5850) ∨ (¬ p5851) ∨ (¬ p5852))
    : (¬ p5851) ∨ (¬ p5852) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5851 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5852 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5850 := h65849;
    (Or.elim h12114 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66526 (p5853 p5854 p5855 : Prop)
    (h65785 : p5853)
    (h12131 : (¬ p5853) ∨ (¬ p5854) ∨ (¬ p5855))
    : (¬ p5854) ∨ (¬ p5855) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5854 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5855 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5853 := h65785;
    (Or.elim h12131 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66527 (p5856 p5857 p5858 : Prop)
    (h65882 : p5856)
    (h12148 : (¬ p5856) ∨ (¬ p5857) ∨ (¬ p5858))
    : (¬ p5858) ∨ (¬ p5857) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5858 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5857 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5856 := h65882;
    (Or.elim h12148 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66528 (p5859 p5860 p5861 : Prop)
    (h65945 : p5859)
    (h12165 : (¬ p5859) ∨ (¬ p5860) ∨ (¬ p5861))
    : (¬ p5860) ∨ (¬ p5861) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5861 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5859 := h65945;
    (Or.elim h12165 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66529 (p5862 p5863 p5864 : Prop)
    (h65695 : p5862)
    (h12182 : (¬ p5862) ∨ (¬ p5863) ∨ (¬ p5864))
    : (¬ p5863) ∨ (¬ p5864) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5863 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5864 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5862 := h65695;
    (Or.elim h12182 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66530 (p5865 p5866 p5867 : Prop)
    (h65999 : p5865)
    (h12201 : (¬ p5865) ∨ (¬ p5866) ∨ (¬ p5867))
    : (¬ p5866) ∨ (¬ p5867) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5866 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5867 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5865 := h65999;
    (Or.elim h12201 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66531 (p5868 p5869 p5870 : Prop)
    (h65776 : p5868)
    (h12219 : (¬ p5868) ∨ (¬ p5869) ∨ (¬ p5870))
    : (¬ p5869) ∨ (¬ p5870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5869 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5870 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5868 := h65776;
    (Or.elim h12219 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66532 (p5871 p5872 p5873 : Prop)
    (h65845 : p5871)
    (h12236 : (¬ p5871) ∨ (¬ p5872) ∨ (¬ p5873))
    : (¬ p5873) ∨ (¬ p5872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5873 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5872 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5871 := h65845;
    (Or.elim h12236 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66533 (p5874 p5875 p5876 : Prop)
    (h65854 : p5874)
    (h12254 : (¬ p5874) ∨ (¬ p5875) ∨ (¬ p5876))
    : (¬ p5876) ∨ (¬ p5875) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5876 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5875 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5874 := h65854;
    (Or.elim h12254 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66534 (p5877 p5878 p5879 : Prop)
    (h65781 : p5877)
    (h12271 : (¬ p5877) ∨ (¬ p5878) ∨ (¬ p5879))
    : (¬ p5878) ∨ (¬ p5879) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5878 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5879 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5877 := h65781;
    (Or.elim h12271 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66535 (p5880 p5881 p5882 : Prop)
    (h65592 : p5880)
    (h12288 : (¬ p5880) ∨ (¬ p5881) ∨ (¬ p5882))
    : (¬ p5882) ∨ (¬ p5881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5882 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5881 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5880 := h65592;
    (Or.elim h12288 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66536 (p5883 p5884 p5885 : Prop)
    (h65533 : p5883)
    (h12305 : (¬ p5883) ∨ (¬ p5884) ∨ (¬ p5885))
    : (¬ p5884) ∨ (¬ p5885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5884 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5885 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5883 := h65533;
    (Or.elim h12305 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66537 (p5886 p5887 p5888 : Prop)
    (h65618 : p5886)
    (h12322 : (¬ p5886) ∨ (¬ p5887) ∨ (¬ p5888))
    : (¬ p5887) ∨ (¬ p5888) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5887 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5888 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5886 := h65618;
    (Or.elim h12322 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66538 (p5889 p5890 p5891 : Prop)
    (h65607 : p5889)
    (h12339 : (¬ p5889) ∨ (¬ p5890) ∨ (¬ p5891))
    : (¬ p5891) ∨ (¬ p5890) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5890 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5889 := h65607;
    (Or.elim h12339 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66539 (p5892 p5893 p5894 : Prop)
    (h65666 : p5892)
    (h12357 : (¬ p5892) ∨ (¬ p5893) ∨ (¬ p5894))
    : (¬ p5894) ∨ (¬ p5893) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5894 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5893 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5892 := h65666;
    (Or.elim h12357 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66540 (p5895 p5896 p5897 : Prop)
    (h65860 : p5895)
    (h12374 : (¬ p5895) ∨ (¬ p5896) ∨ (¬ p5897))
    : (¬ p5897) ∨ (¬ p5896) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5897 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5896 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5895 := h65860;
    (Or.elim h12374 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66541 (p5898 p5899 p5900 : Prop)
    (h65710 : p5898)
    (h12391 : (¬ p5898) ∨ (¬ p5899) ∨ (¬ p5900))
    : (¬ p5899) ∨ (¬ p5900) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5899 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5900 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5898 := h65710;
    (Or.elim h12391 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66542 (p5901 p5902 p5903 : Prop)
    (h65603 : p5901)
    (h12408 : (¬ p5901) ∨ (¬ p5902) ∨ (¬ p5903))
    : (¬ p5902) ∨ (¬ p5903) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5902 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5903 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5901 := h65603;
    (Or.elim h12408 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66543 (p5904 p5905 p5906 : Prop)
    (h65623 : p5904)
    (h12426 : (¬ p5904) ∨ (¬ p5905) ∨ (¬ p5906))
    : (¬ p5905) ∨ (¬ p5906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5905 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5906 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5904 := h65623;
    (Or.elim h12426 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66544 (p5907 p5908 p5909 : Prop)
    (h65627 : p5907)
    (h12444 : (¬ p5907) ∨ (¬ p5908) ∨ (¬ p5909))
    : (¬ p5909) ∨ (¬ p5908) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5909 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5908 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5907 := h65627;
    (Or.elim h12444 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66545 (p5910 p5911 p5912 : Prop)
    (h65832 : p5910)
    (h12461 : (¬ p5910) ∨ (¬ p5911) ∨ (¬ p5912))
    : (¬ p5911) ∨ (¬ p5912) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5912 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5910 := h65832;
    (Or.elim h12461 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66546 (p5913 p5914 p5915 : Prop)
    (h65588 : p5913)
    (h12479 : (¬ p5913) ∨ (¬ p5914) ∨ (¬ p5915))
    : (¬ p5915) ∨ (¬ p5914) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5915 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5914 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5913 := h65588;
    (Or.elim h12479 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66547 (p5916 p5917 p5918 : Prop)
    (h65828 : p5916)
    (h12499 : (¬ p5916) ∨ (¬ p5917) ∨ (¬ p5918))
    : (¬ p5918) ∨ (¬ p5917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5918 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5917 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5916 := h65828;
    (Or.elim h12499 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66548 (p5922 p5923 p5924 : Prop)
    (h65811 : p5922)
    (h12538 : (¬ p5922) ∨ (¬ p5923) ∨ (¬ p5924))
    : (¬ p5923) ∨ (¬ p5924) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5923 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5924 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5922 := h65811;
    (Or.elim h12538 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66549 (p5925 p5926 p5927 : Prop)
    (h65717 : p5925)
    (h12556 : (¬ p5925) ∨ (¬ p5926) ∨ (¬ p5927))
    : (¬ p5926) ∨ (¬ p5927) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5926 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5927 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5925 := h65717;
    (Or.elim h12556 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66550 (p5928 p5929 p5930 : Prop)
    (h65700 : p5928)
    (h12573 : (¬ p5928) ∨ (¬ p5929) ∨ (¬ p5930))
    : (¬ p5929) ∨ (¬ p5930) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5929 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5930 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5928 := h65700;
    (Or.elim h12573 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66551 (p5931 p5932 p5933 : Prop)
    (h65796 : p5931)
    (h12590 : (¬ p5931) ∨ (¬ p5932) ∨ (¬ p5933))
    : (¬ p5932) ∨ (¬ p5933) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5932 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5933 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5931 := h65796;
    (Or.elim h12590 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66552 (p5934 p5935 p5936 : Prop)
    (h65742 : p5934)
    (h12607 : (¬ p5934) ∨ (¬ p5935) ∨ (¬ p5936))
    : (¬ p5935) ∨ (¬ p5936) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5935 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5936 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5934 := h65742;
    (Or.elim h12607 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66553 (p5937 p5938 p5939 : Prop)
    (h65631 : p5937)
    (h12625 : (¬ p5937) ∨ (¬ p5938) ∨ (¬ p5939))
    : (¬ p5939) ∨ (¬ p5938) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5939 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5938 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5937 := h65631;
    (Or.elim h12625 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66554 (p5940 p5941 p5942 : Prop)
    (h65650 : p5940)
    (h12644 : (¬ p5940) ∨ (¬ p5941) ∨ (¬ p5942))
    : (¬ p5942) ∨ (¬ p5941) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5942 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5941 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5940 := h65650;
    (Or.elim h12644 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66555 (p5943 p5944 p5945 : Prop)
    (h65682 : p5943)
    (h12661 : (¬ p5943) ∨ (¬ p5944) ∨ (¬ p5945))
    : (¬ p5945) ∨ (¬ p5944) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5945 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5944 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5943 := h65682;
    (Or.elim h12661 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66556 (p5946 p5947 p5948 : Prop)
    (h65730 : p5946)
    (h12678 : (¬ p5946) ∨ (¬ p5947) ∨ (¬ p5948))
    : (¬ p5947) ∨ (¬ p5948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5947 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5948 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5946 := h65730;
    (Or.elim h12678 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66557 (p5949 p5950 p5951 : Prop)
    (h65981 : p5949)
    (h12695 : (¬ p5949) ∨ (¬ p5950) ∨ (¬ p5951))
    : (¬ p5951) ∨ (¬ p5950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5951 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5950 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5949 := h65981;
    (Or.elim h12695 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66558 (p5952 p5953 p5954 : Prop)
    (h65678 : p5952)
    (h12715 : (¬ p5952) ∨ (¬ p5953) ∨ (¬ p5954))
    : (¬ p5953) ∨ (¬ p5954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5953 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5954 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5952 := h65678;
    (Or.elim h12715 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66559 (p5955 p5956 p5957 : Prop)
    (h65670 : p5955)
    (h12733 : (¬ p5955) ∨ (¬ p5956) ∨ (¬ p5957))
    : (¬ p5956) ∨ (¬ p5957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5956 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5957 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5955 := h65670;
    (Or.elim h12733 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66560 (p5958 p5959 p5960 : Prop)
    (h65662 : p5958)
    (h12751 : (¬ p5958) ∨ (¬ p5959) ∨ (¬ p5960))
    : (¬ p5959) ∨ (¬ p5960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5959 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5960 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5958 := h65662;
    (Or.elim h12751 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66561 (p5961 p5962 p5963 : Prop)
    (h65658 : p5961)
    (h12773 : (¬ p5961) ∨ (¬ p5962) ∨ (¬ p5963))
    : (¬ p5963) ∨ (¬ p5962) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5962 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5961 := h65658;
    (Or.elim h12773 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66562 (p5964 p5965 p5966 : Prop)
    (h65654 : p5964)
    (h12793 : (¬ p5964) ∨ (¬ p5965) ∨ (¬ p5966))
    : (¬ p5966) ∨ (¬ p5965) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5966 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5965 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5964 := h65654;
    (Or.elim h12793 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66563 (p5967 p5968 p5969 : Prop)
    (h65643 : p5967)
    (h12814 : (¬ p5967) ∨ (¬ p5968) ∨ (¬ p5969))
    : (¬ p5968) ∨ (¬ p5969) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5968 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5969 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5967 := h65643;
    (Or.elim h12814 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66564 (p5970 p5971 p5972 : Prop)
    (h65639 : p5970)
    (h12831 : (¬ p5970) ∨ (¬ p5971) ∨ (¬ p5972))
    : (¬ p5971) ∨ (¬ p5972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5971 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5972 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5970 := h65639;
    (Or.elim h12831 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66565 (p5973 p5974 p5975 : Prop)
    (h65598 : p5973)
    (h12848 : (¬ p5973) ∨ (¬ p5974) ∨ (¬ p5975))
    : (¬ p5975) ∨ (¬ p5974) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5975 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5974 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5973 := h65598;
    (Or.elim h12848 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66566 (p5976 p5977 p5978 : Prop)
    (h65635 : p5976)
    (h12866 : (¬ p5976) ∨ (¬ p5977) ∨ (¬ p5978))
    : (¬ p5977) ∨ (¬ p5978) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5977 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5978 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5976 := h65635;
    (Or.elim h12866 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66567 (p5979 p5980 p5981 : Prop)
    (h65584 : p5979)
    (h12883 : (¬ p5979) ∨ (¬ p5980) ∨ (¬ p5981))
    : (¬ p5981) ∨ (¬ p5980) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5981 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5980 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5979 := h65584;
    (Or.elim h12883 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66568 (p5982 p5983 p5984 : Prop)
    (h65580 : p5982)
    (h12901 : (¬ p5982) ∨ (¬ p5983) ∨ (¬ p5984))
    : (¬ p5983) ∨ (¬ p5984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5983 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5984 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5982 := h65580;
    (Or.elim h12901 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66569 (p5985 p5986 p5987 : Prop)
    (h65576 : p5985)
    (h12919 : (¬ p5985) ∨ (¬ p5986) ∨ (¬ p5987))
    : (¬ p5986) ∨ (¬ p5987) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5986 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5987 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5985 := h65576;
    (Or.elim h12919 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66570 (p5988 p5989 p5990 : Prop)
    (h65572 : p5988)
    (h12936 : (¬ p5988) ∨ (¬ p5989) ∨ (¬ p5990))
    : (¬ p5989) ∨ (¬ p5990) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5989 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5990 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5988 := h65572;
    (Or.elim h12936 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66571 (p5991 p5992 p5993 : Prop)
    (h65568 : p5991)
    (h12954 : (¬ p5991) ∨ (¬ p5992) ∨ (¬ p5993))
    : (¬ p5992) ∨ (¬ p5993) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5993 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5991 := h65568;
    (Or.elim h12954 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66572 (p5994 p5995 p5996 : Prop)
    (h65564 : p5994)
    (h12971 : (¬ p5994) ∨ (¬ p5995) ∨ (¬ p5996))
    : (¬ p5995) ∨ (¬ p5996) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5995 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5996 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5994 := h65564;
    (Or.elim h12971 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66573 (p5997 p5998 p5999 : Prop)
    (h65560 : p5997)
    (h12988 : (¬ p5997) ∨ (¬ p5998) ∨ (¬ p5999))
    : (¬ p5998) ∨ (¬ p5999) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5998 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5999 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5997 := h65560;
    (Or.elim h12988 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66574 (p6000 p6001 p6002 : Prop)
    (h65553 : p6000)
    (h13008 : (¬ p6000) ∨ (¬ p6001) ∨ (¬ p6002))
    : (¬ p6001) ∨ (¬ p6002) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6001 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6002 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6000 := h65553;
    (Or.elim h13008 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66575 (p6003 p6004 p6005 : Prop)
    (h65549 : p6003)
    (h13028 : (¬ p6003) ∨ (¬ p6004) ∨ (¬ p6005))
    : (¬ p6004) ∨ (¬ p6005) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6004 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6005 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6003 := h65549;
    (Or.elim h13028 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66577 (p6009 p6010 p6011 : Prop)
    (h65541 : p6009)
    (h13067 : (¬ p6009) ∨ (¬ p6010) ∨ (¬ p6011))
    : (¬ p6010) ∨ (¬ p6011) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6010 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6011 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6009 := h65541;
    (Or.elim h13067 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66578 (p6012 p6013 p6014 : Prop)
    (h65537 : p6012)
    (h13087 : (¬ p6012) ∨ (¬ p6013) ∨ (¬ p6014))
    : (¬ p6013) ∨ (¬ p6014) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6013 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6014 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6012 := h65537;
    (Or.elim h13087 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66579 (p6015 p6016 p6017 : Prop)
    (h65529 : p6015)
    (h13105 : (¬ p6015) ∨ (¬ p6016) ∨ (¬ p6017))
    : (¬ p6016) ∨ (¬ p6017) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6017 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6015 := h65529;
    (Or.elim h13105 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66580 (p6018 p6019 p6020 : Prop)
    (h65525 : p6018)
    (h13122 : (¬ p6018) ∨ (¬ p6019) ∨ (¬ p6020))
    : (¬ p6019) ∨ (¬ p6020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6020 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6018 := h65525;
    (Or.elim h13122 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66581 (p6021 p6022 p6023 : Prop)
    (h65521 : p6021)
    (h13141 : (¬ p6021) ∨ (¬ p6022) ∨ (¬ p6023))
    : (¬ p6022) ∨ (¬ p6023) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6022 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6023 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6021 := h65521;
    (Or.elim h13141 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66582 (p6024 p6025 p6026 : Prop)
    (h65517 : p6024)
    (h13158 : (¬ p6024) ∨ (¬ p6025) ∨ (¬ p6026))
    : (¬ p6025) ∨ (¬ p6026) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6025 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6026 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6024 := h65517;
    (Or.elim h13158 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66583 (p6027 p6028 p6029 : Prop)
    (h65513 : p6027)
    (h13176 : (¬ p6027) ∨ (¬ p6028) ∨ (¬ p6029))
    : (¬ p6028) ∨ (¬ p6029) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6028 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6029 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6027 := h65513;
    (Or.elim h13176 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66584 (p6030 p6031 p6032 : Prop)
    (h65509 : p6030)
    (h13193 : (¬ p6030) ∨ (¬ p6031) ∨ (¬ p6032))
    : (¬ p6031) ∨ (¬ p6032) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6031 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6032 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6030 := h65509;
    (Or.elim h13193 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66585 (p6033 p6034 p6035 : Prop)
    (h65505 : p6033)
    (h13210 : (¬ p6033) ∨ (¬ p6034) ∨ (¬ p6035))
    : (¬ p6034) ∨ (¬ p6035) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6034 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6035 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6033 := h65505;
    (Or.elim h13210 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66586 (p6036 p6037 p6038 : Prop)
    (h65501 : p6036)
    (h13232 : (¬ p6036) ∨ (¬ p6037) ∨ (¬ p6038))
    : (¬ p6037) ∨ (¬ p6038) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6037 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6038 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6036 := h65501;
    (Or.elim h13232 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66587 (p6039 p6040 p6041 : Prop)
    (h65497 : p6039)
    (h13250 : (¬ p6039) ∨ (¬ p6040) ∨ (¬ p6041))
    : (¬ p6040) ∨ (¬ p6041) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6040 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6041 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6039 := h65497;
    (Or.elim h13250 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66588 (p6042 p6043 p6044 : Prop)
    (h65493 : p6042)
    (h13267 : (¬ p6042) ∨ (¬ p6043) ∨ (¬ p6044))
    : (¬ p6043) ∨ (¬ p6044) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6043 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6044 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6042 := h65493;
    (Or.elim h13267 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66589 (p6045 p6046 p6047 : Prop)
    (h65489 : p6045)
    (h13286 : (¬ p6045) ∨ (¬ p6046) ∨ (¬ p6047))
    : (¬ p6047) ∨ (¬ p6046) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6047 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6046 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6045 := h65489;
    (Or.elim h13286 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step66590 (p6048 p6049 p6050 : Prop)
    (h65485 : p6048)
    (h13304 : (¬ p6048) ∨ (¬ p6049) ∨ (¬ p6050))
    : (¬ p6049) ∨ (¬ p6050) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6049 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6050 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6048 := h65485;
    (Or.elim h13304 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66591 (p6051 p6052 p6053 : Prop)
    (h65481 : p6051)
    (h13324 : (¬ p6051) ∨ (¬ p6052) ∨ (¬ p6053))
    : (¬ p6052) ∨ (¬ p6053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6052 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6053 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6051 := h65481;
    (Or.elim h13324 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66592 (p6054 p6055 p6056 : Prop)
    (h65477 : p6054)
    (h13346 : (¬ p6054) ∨ (¬ p6055) ∨ (¬ p6056))
    : (¬ p6055) ∨ (¬ p6056) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6056 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6054 := h65477;
    (Or.elim h13346 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66593 (p6057 p6058 p6059 : Prop)
    (h65473 : p6057)
    (h13367 : (¬ p6057) ∨ (¬ p6058) ∨ (¬ p6059))
    : (¬ p6058) ∨ (¬ p6059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6058 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6059 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6057 := h65473;
    (Or.elim h13367 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66594 (p6060 p6061 p6062 : Prop)
    (h65469 : p6060)
    (h13387 : (¬ p6060) ∨ (¬ p6061) ∨ (¬ p6062))
    : (¬ p6061) ∨ (¬ p6062) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6061 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6062 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6060 := h65469;
    (Or.elim h13387 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66595 (p6063 p6064 p6065 : Prop)
    (h65465 : p6063)
    (h13407 : (¬ p6063) ∨ (¬ p6064) ∨ (¬ p6065))
    : (¬ p6064) ∨ (¬ p6065) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6064 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6065 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6063 := h65465;
    (Or.elim h13407 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66596 (p6066 p6067 p6068 : Prop)
    (h65461 : p6066)
    (h13437 : (¬ p6066) ∨ (¬ p6067) ∨ (¬ p6068))
    : (¬ p6067) ∨ (¬ p6068) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6067 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6068 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6066 := h65461;
    (Or.elim h13437 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66597 (p6069 p6070 p6071 : Prop)
    (h65457 : p6069)
    (h13462 : (¬ p6069) ∨ (¬ p6070) ∨ (¬ p6071))
    : (¬ p6070) ∨ (¬ p6071) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6070 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6071 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6069 := h65457;
    (Or.elim h13462 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66598 (p6072 p6073 p6074 : Prop)
    (h65453 : p6072)
    (h13480 : (¬ p6072) ∨ (¬ p6073) ∨ (¬ p6074))
    : (¬ p6073) ∨ (¬ p6074) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6074 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6072 := h65453;
    (Or.elim h13480 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66599 (p6075 p6076 p6077 : Prop)
    (h65449 : p6075)
    (h13498 : (¬ p6075) ∨ (¬ p6076) ∨ (¬ p6077))
    : (¬ p6076) ∨ (¬ p6077) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6076 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6077 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6075 := h65449;
    (Or.elim h13498 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66600 (p6078 p6079 p6080 : Prop)
    (h65445 : p6078)
    (h13517 : (¬ p6078) ∨ (¬ p6079) ∨ (¬ p6080))
    : (¬ p6079) ∨ (¬ p6080) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6079 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6080 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6078 := h65445;
    (Or.elim h13517 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66601 (p6081 p6082 p6083 : Prop)
    (h65441 : p6081)
    (h13557 : (¬ p6081) ∨ (¬ p6082) ∨ (¬ p6083))
    : (¬ p6082) ∨ (¬ p6083) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6082 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6083 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6081 := h65441;
    (Or.elim h13557 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66602 (p6084 p6085 p6086 : Prop)
    (h65437 : p6084)
    (h13629 : (¬ p6084) ∨ (¬ p6085) ∨ (¬ p6086))
    : (¬ p6085) ∨ (¬ p6086) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6085 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6086 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6084 := h65437;
    (Or.elim h13629 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66603 (p6087 p6088 p6089 : Prop)
    (h65433 : p6087)
    (h13646 : (¬ p6087) ∨ (¬ p6088) ∨ (¬ p6089))
    : (¬ p6088) ∨ (¬ p6089) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6089 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6087 := h65433;
    (Or.elim h13646 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66605 (p6093 p6094 p6095 : Prop)
    (h65425 : p6093)
    (h13681 : (¬ p6093) ∨ (¬ p6094) ∨ (¬ p6095))
    : (¬ p6094) ∨ (¬ p6095) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6094 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6095 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6093 := h65425;
    (Or.elim h13681 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66606 (p6096 p6097 p6098 : Prop)
    (h65421 : p6096)
    (h13711 : (¬ p6096) ∨ (¬ p6097) ∨ (¬ p6098))
    : (¬ p6097) ∨ (¬ p6098) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6097 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6098 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6096 := h65421;
    (Or.elim h13711 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66607 (p6099 p6100 p6101 : Prop)
    (h65417 : p6099)
    (h13742 : (¬ p6099) ∨ (¬ p6100) ∨ (¬ p6101))
    : (¬ p6100) ∨ (¬ p6101) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6100 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6101 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6099 := h65417;
    (Or.elim h13742 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66608 (p6102 p6103 p6104 : Prop)
    (h65413 : p6102)
    (h13778 : (¬ p6102) ∨ (¬ p6103) ∨ (¬ p6104))
    : (¬ p6103) ∨ (¬ p6104) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6103 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6104 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6102 := h65413;
    (Or.elim h13778 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66609 (p6105 p6106 p6107 : Prop)
    (h65409 : p6105)
    (h13796 : (¬ p6105) ∨ (¬ p6106) ∨ (¬ p6107))
    : (¬ p6106) ∨ (¬ p6107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6106 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6107 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6105 := h65409;
    (Or.elim h13796 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66610 (p6108 p6109 p6110 : Prop)
    (h65405 : p6108)
    (h13840 : (¬ p6108) ∨ (¬ p6109) ∨ (¬ p6110))
    : (¬ p6109) ∨ (¬ p6110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6109 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6110 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6108 := h65405;
    (Or.elim h13840 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66611 (p6111 p6112 p6113 : Prop)
    (h65401 : p6111)
    (h13861 : (¬ p6111) ∨ (¬ p6112) ∨ (¬ p6113))
    : (¬ p6112) ∨ (¬ p6113) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6112 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6113 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6111 := h65401;
    (Or.elim h13861 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66613 (p6117 p6118 p6119 : Prop)
    (h65393 : p6117)
    (h13895 : (¬ p6117) ∨ (¬ p6118) ∨ (¬ p6119))
    : (¬ p6118) ∨ (¬ p6119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6118 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6119 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6117 := h65393;
    (Or.elim h13895 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66614 (p6120 p6121 p6122 : Prop)
    (h65389 : p6120)
    (h13927 : (¬ p6120) ∨ (¬ p6121) ∨ (¬ p6122))
    : (¬ p6121) ∨ (¬ p6122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6121 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6122 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6120 := h65389;
    (Or.elim h13927 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66615 (p6123 p6124 p6125 : Prop)
    (h65385 : p6123)
    (h13970 : (¬ p6123) ∨ (¬ p6124) ∨ (¬ p6125))
    : (¬ p6124) ∨ (¬ p6125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6124 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6125 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6123 := h65385;
    (Or.elim h13970 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66616 (p6126 p6127 p6128 : Prop)
    (h65381 : p6126)
    (h14019 : (¬ p6126) ∨ (¬ p6127) ∨ (¬ p6128))
    : (¬ p6127) ∨ (¬ p6128) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6127 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6128 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6126 := h65381;
    (Or.elim h14019 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66617 (p6129 p6130 p6131 : Prop)
    (h65377 : p6129)
    (h14046 : (¬ p6129) ∨ (¬ p6130) ∨ (¬ p6131))
    : (¬ p6130) ∨ (¬ p6131) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6130 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6131 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6129 := h65377;
    (Or.elim h14046 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66619 (p6135 p6136 p6137 : Prop)
    (h65369 : p6135)
    (h14144 : (¬ p6135) ∨ (¬ p6136) ∨ (¬ p6137))
    : (¬ p6136) ∨ (¬ p6137) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6137 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6135 := h65369;
    (Or.elim h14144 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66620 (p6138 p6139 p6140 : Prop)
    (h65365 : p6138)
    (h14179 : (¬ p6138) ∨ (¬ p6139) ∨ (¬ p6140))
    : (¬ p6139) ∨ (¬ p6140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6139 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6140 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6138 := h65365;
    (Or.elim h14179 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66622 (p6144 p6145 p6146 : Prop)
    (h65357 : p6144)
    (h14278 : (¬ p6144) ∨ (¬ p6145) ∨ (¬ p6146))
    : (¬ p6145) ∨ (¬ p6146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6146 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6144 := h65357;
    (Or.elim h14278 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66623 (p6147 p6148 p6149 : Prop)
    (h65353 : p6147)
    (h14404 : (¬ p6147) ∨ (¬ p6148) ∨ (¬ p6149))
    : (¬ p6148) ∨ (¬ p6149) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6148 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6149 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6147 := h65353;
    (Or.elim h14404 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66624 (p6150 p6151 p6152 : Prop)
    (h65349 : p6150)
    (h14422 : (¬ p6150) ∨ (¬ p6151) ∨ (¬ p6152))
    : (¬ p6151) ∨ (¬ p6152) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6151 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6152 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6150 := h65349;
    (Or.elim h14422 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66625 (p6153 p6154 p6155 : Prop)
    (h65345 : p6153)
    (h14486 : (¬ p6153) ∨ (¬ p6154) ∨ (¬ p6155))
    : (¬ p6154) ∨ (¬ p6155) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6154 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6155 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6153 := h65345;
    (Or.elim h14486 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66628 (p6162 p6163 p6164 : Prop)
    (h65333 : p6162)
    (h14712 : (¬ p6162) ∨ (¬ p6163) ∨ (¬ p6164))
    : (¬ p6163) ∨ (¬ p6164) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6163 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6164 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6162 := h65333;
    (Or.elim h14712 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66629 (p6165 p6166 p6167 : Prop)
    (h65329 : p6165)
    (h14731 : (¬ p6165) ∨ (¬ p6166) ∨ (¬ p6167))
    : (¬ p6166) ∨ (¬ p6167) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6167 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6165 := h65329;
    (Or.elim h14731 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66630 (p6168 p6169 p6170 : Prop)
    (h65325 : p6168)
    (h14763 : (¬ p6168) ∨ (¬ p6169) ∨ (¬ p6170))
    : (¬ p6169) ∨ (¬ p6170) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6169 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6170 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6168 := h65325;
    (Or.elim h14763 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66631 (p6171 p6172 p6173 : Prop)
    (h65321 : p6171)
    (h15014 : (¬ p6171) ∨ (¬ p6172) ∨ (¬ p6173))
    : (¬ p6172) ∨ (¬ p6173) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6173 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6171 := h65321;
    (Or.elim h15014 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66632 (p6174 p6175 p6176 : Prop)
    (h65317 : p6174)
    (h15094 : (¬ p6174) ∨ (¬ p6175) ∨ (¬ p6176))
    : (¬ p6175) ∨ (¬ p6176) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6175 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6176 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6174 := h65317;
    (Or.elim h15094 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66633 (p6177 p6178 p6179 : Prop)
    (h65313 : p6177)
    (h15165 : (¬ p6177) ∨ (¬ p6178) ∨ (¬ p6179))
    : (¬ p6178) ∨ (¬ p6179) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6178 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6179 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6177 := h65313;
    (Or.elim h15165 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66634 (p6180 p6181 p6182 : Prop)
    (h65309 : p6180)
    (h15274 : (¬ p6180) ∨ (¬ p6181) ∨ (¬ p6182))
    : (¬ p6181) ∨ (¬ p6182) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6182 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6180 := h65309;
    (Or.elim h15274 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66636 (p6186 p6187 p6188 : Prop)
    (h65301 : p6186)
    (h15779 : (¬ p6186) ∨ (¬ p6187) ∨ (¬ p6188))
    : (¬ p6187) ∨ (¬ p6188) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6188 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6186 := h65301;
    (Or.elim h15779 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66637 (p6189 p6190 p6191 : Prop)
    (h65297 : p6189)
    (h16044 : (¬ p6189) ∨ (¬ p6190) ∨ (¬ p6191))
    : (¬ p6190) ∨ (¬ p6191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6191 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6189 := h65297;
    (Or.elim h16044 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66638 (p6192 p6193 p6194 : Prop)
    (h65293 : p6192)
    (h16419 : (¬ p6192) ∨ (¬ p6193) ∨ (¬ p6194))
    : (¬ p6193) ∨ (¬ p6194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6194 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p6192 := h65293;
    (Or.elim h16419 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step66644 (p2156 p2553 p3097 p3556 p3646 p3660 p4275 p4484 p4487 p4533 p4554 p4718 : Prop)
    (h7201 : p4275 ∨ (¬ p4554))
    (h7202 : p3097 ∨ (¬ p4554))
    (h57162 : (¬ p2156) ∨ (¬ p2553) ∨ (¬ p3556) ∨ (¬ p4275) ∨ (¬ p4718))
    (h53114 : (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3660) ∨ (¬ p4533))
    (h7028 : p2156 ∨ (¬ p4487))
    (h7022 : p3646 ∨ (¬ p4484))
    (h66328 : p4487 ∨ p4484)
    : (¬ p4554) ∨ (¬ p3556) ∨ (¬ p4533) ∨ (¬ p4718) ∨ (¬ p3660) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4554 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4275 := (Or.elim h7201 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p3097 := (Or.elim h7202 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : (¬ p2156) := (Or.elim h57162 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3))))))))));
    let u9 : (¬ p3646) := (Or.elim h53114 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    let u10 : (¬ p4487) := (Or.elim h7028 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : (¬ p4484) := (Or.elim h7022 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    (Or.elim h66328 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u11 r0)))))

theorem step66646 (p2191 p2459 p2528 p2589 p3692 p3880 p4355 p4606 p4609 p4629 : Prop)
    (h44763 : (¬ p2459) ∨ (¬ p2589) ∨ (¬ p3692) ∨ (¬ p3880))
    (h54486 : (¬ p2191) ∨ (¬ p2528) ∨ (¬ p3692) ∨ (¬ p4355) ∨ (¬ p4629))
    (h7343 : p3880 ∨ (¬ p4606))
    (h7348 : p4355 ∨ (¬ p4609))
    (h66350 : p4609 ∨ p4606)
    : (¬ p3692) ∨ (¬ p2528) ∨ (¬ p2459) ∨ (¬ p2191) ∨ (¬ p4629) ∨ (¬ p2589) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3692 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3880) := (Or.elim h44763 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => r2))))));
    let u7 : (¬ p4355) := (Or.elim h54486 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    let u8 : (¬ p4606) := (Or.elim h7343 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    let u9 : (¬ p4609) := (Or.elim h7348 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    (Or.elim h66350 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step66647 (p2373 p3146 p3256 p3661 p4118 p4311 p4702 p5061 p5064 p5106 p5110 : Prop)
    (h8634 : p3256 ∨ (¬ p5110))
    (h34559 : (¬ p3146) ∨ p3256 ∨ (¬ p4311))
    (h66437 : p5106 ∨ p5110)
    (h8494 : p4311 ∨ (¬ p5064))
    (h8628 : p4118 ∨ (¬ p5106))
    (h66429 : p5061 ∨ p5064)
    (h41848 : (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4702))
    (h8488 : p3661 ∨ (¬ p5061))
    : p3256 ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5110) := (Or.elim h8634 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u5 : (¬ p4311) := (Or.elim h34559 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => r1))));
    let u6 : p5106 := (Or.elim h66437 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : (¬ p5064) := (Or.elim h8494 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    let u8 : p4118 := (Or.elim h8628 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u9 : p5061 := (Or.elim h66429 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u10 : (¬ p3661) := (Or.elim h41848 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h8488 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u9)))))

theorem step66648 (p2244 p2247 p2251 p2252 p2657 p2751 p2810 p3379 p3487 p4281 p4812 : Prop)
    (h7861 : p3487 ∨ (¬ p4812))
    (h7862 : p4281 ∨ (¬ p4812))
    (h49266 : (¬ p2247) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p3379) ∨ (¬ p3487))
    (h15387 : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p3487) ∨ (¬ p4281))
    (h2625 : (¬ p2244) ∨ p2247)
    (h2637 : (¬ p2251) ∨ p2252)
    (h66336 : p2244 ∨ p2251)
    : (¬ p4812) ∨ (¬ p2810) ∨ (¬ p2751) ∨ (¬ p2657) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4812 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3487 := (Or.elim h7861 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p4281 := (Or.elim h7862 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : (¬ p2247) := (Or.elim h49266 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5))))))))));
    let u8 : (¬ p2252) := (Or.elim h15387 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6))))))));
    let u9 : (¬ p2244) := (Or.elim h2625 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u10 : (¬ p2251) := (Or.elim h2637 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h66336 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step66649 (p2156 p2177 p2192 p2210 p2274 p2284 p2307 p2310 p2313 p2317 p2427 p2542 p2563 p2630 p2651 p2654 p2657 p2659 p2661 p2737 p2747 p2751 p2810 p2839 p3054 p3093 p3309 p3361 p3365 p3379 p3549 p3556 p3583 p3585 p3591 p3644 p3645 p3646 p3695 p3872 p3873 p3904 p3954 p3957 p4031 p4198 p4202 p4210 p4243 p4244 p4256 p4484 p4487 p4500 p4501 p4502 p4511 p4512 p4515 p4523 p4533 p4535 p4537 p4557 p4627 p4629 p4630 p4699 p4703 p4732 p4748 p4751 p4785 p4788 p4809 p4812 p4873 p4874 p4876 p4880 p4882 p4883 p5014 p5019 p5140 p5143 p5213 p5215 p5216 : Prop)
    (h7113 : p2210 ∨ (¬ p4523))
    (h7681 : p3954 ∨ (¬ p4732))
    (h29892 : (¬ p2210) ∨ (¬ p3954) ∨ (¬ p4874))
    (h8015 : (¬ p4873) ∨ p4874)
    (h66397 : p4873 ∨ p4876)
    (h8023 : p2839 ∨ (¬ p4876))
    (h9144 : (¬ p2839) ∨ (¬ p3583))
    (h7207 : p3872 ∨ (¬ p4557))
    (h7111 : p3645 ∨ (¬ p4523))
    (h8021 : p4243 ∨ (¬ p4876))
    (h26822 : (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4243) ∨ p4244)
    (h20311 : (¬ p2563) ∨ (¬ p3695) ∨ (¬ p3872) ∨ (¬ p4244))
    (h8038 : p3695 ∨ (¬ p4883))
    (h66398 : p4880 ∨ p4883)
    (h8032 : p3054 ∨ (¬ p4880))
    (h37227 : (¬ p3054) ∨ p3583 ∨ (¬ p3585))
    (h8853 : p3585 ∨ (¬ p5213))
    (h66448 : p5215 ∨ p5213)
    (h8860 : (¬ p5215) ∨ p5216)
    (h8036 : (¬ p4880) ∨ p4882)
    (h5739 : p2427 ∨ (¬ p2563) ∨ (¬ p3872))
    (h22664 : (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4210))
    (h7399 : p4210 ∨ (¬ p4630))
    (h66353 : p4627 ∨ p4630)
    (h7397 : (¬ p4627) ∨ p4629)
    (h7208 : p2274 ∨ (¬ p4557))
    (h6734 : (¬ p3556) ∨ p3646 ∨ (¬ p3872))
    (h5323 : (¬ p2192) ∨ (¬ p3645) ∨ (¬ p3646))
    (h7096 : p2192 ∨ (¬ p4515))
    (h66332 : p4511 ∨ p4515)
    (h7088 : (¬ p4511) ∨ p4512)
    (h61082 : (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p4629))
    (h8705 : p3549 ∨ (¬ p5140))
    (h66440 : p5140 ∨ p5143)
    (h8711 : p3309 ∨ (¬ p5143))
    (h7089 : p3957 ∨ (¬ p4511))
    (h41941 : (¬ p2210) ∨ (¬ p2563) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4629))
    (h8386 : p3591 ∨ (¬ p5014))
    (h66423 : p5019 ∨ p5014)
    (h8392 : p3093 ∨ (¬ p5019))
    (h52571 : (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3954))
    (h7062 : p2177 ∨ (¬ p4502))
    (h66330 : p4502 ∨ p4500)
    (h7057 : (¬ p4500) ∨ p4501)
    (h7679 : p3873 ∨ (¬ p4732))
    (h20298 : (¬ p2427) ∨ (¬ p3556) ∨ (¬ p4031))
    (h7146 : p4031 ∨ (¬ p4537))
    (h66335 : p4535 ∨ p4537)
    (h7140 : p3904 ∨ (¬ p4535))
    (h8330 : (¬ p2651) ∨ (¬ p2657))
    (h3449 : p2651 ∨ (¬ p2661))
    (h66378 : p2654 ∨ p2661)
    (h3437 : (¬ p2654) ∨ p2659)
    (h41572 : (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2659) ∨ (¬ p3646) ∨ (¬ p3904))
    (h7590 : p2542 ∨ (¬ p4703))
    (h66367 : p4703 ∨ p4699)
    (h7393 : p4202 ∨ (¬ p4627))
    (h6790 : (¬ p2210) ∨ p3379 ∨ (¬ p4202))
    (h7144 : p4533 ∨ (¬ p4535))
    (h20348 : (¬ p2156) ∨ (¬ p3556) ∨ (¬ p3872))
    (h7028 : p2156 ∨ (¬ p4487))
    (h66328 : p4487 ∨ p4484)
    (h7020 : p4198 ∨ (¬ p4484))
    (h60888 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2563) ∨ (¬ p4198) ∨ (¬ p4533))
    (h2756 : (¬ p2310) ∨ p2313)
    (h66343 : p2317 ∨ p2310)
    (h2770 : p2307 ∨ (¬ p2317))
    (h3622 : p2737 ∨ (¬ p2747))
    (h3624 : (¬ p2747) ∨ p2751)
    (h49742 : (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p3873) ∨ (¬ p5216))
    (h7805 : p3365 ∨ (¬ p4785))
    (h66383 : p4785 ∨ p4788)
    (h7809 : p3361 ∨ (¬ p4788))
    (h4833 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3361))
    (h7721 : p2630 ∨ (¬ p4751))
    (h66376 : p4751 ∨ p4748)
    (h7715 : p2810 ∨ (¬ p4748))
    (h66648 : (¬ p4812) ∨ (¬ p2810) ∨ (¬ p2751) ∨ (¬ p2657) ∨ (¬ p3379))
    (h66386 : p4809 ∨ p4812)
    (h66005 : p2284 ∨ (¬ p4809) ∨ (¬ p2563) ∨ (¬ p4557) ∨ (¬ p4732) ∨ (¬ p4882))
    (h65988 : (¬ p4511) ∨ (¬ p4256) ∨ (¬ p4809) ∨ (¬ p4699) ∨ (¬ p4501) ∨ (¬ p3644) ∨ (¬ p2307) ∨ (¬ p2563) ∨ (¬ p2747) ∨ (¬ p3954) ∨ (¬ p2284) ∨ (¬ p3872) ∨ (¬ p3556))
    : (¬ p2747) ∨ (¬ p4256) ∨ (¬ p3644) ∨ (¬ p4732) ∨ (¬ p2657) ∨ (¬ p4523) ∨ (¬ p3556) ∨ (¬ p4557) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2747 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4732 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4523 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4557 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2210 := (Or.elim h7113 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u10 : p3954 := (Or.elim h7681 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u11 : (¬ p4874) := (Or.elim h29892 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => r1))));
    let u12 : (¬ p4873) := (Or.elim h8015 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u13 : p4876 := (Or.elim h66397 (fun q0 => (False.elim (u12 q0))) (fun r0 => r0));
    let u14 : p2839 := (Or.elim h8023 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u15 : (¬ p3583) := (Or.elim h9144 (fun q0 => (False.elim (q0 u14))) (fun r0 => r0));
    let u16 : p3872 := (Or.elim h7207 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u17 : p3645 := (Or.elim h7111 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u18 : p4243 := (Or.elim h8021 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u19 : p4244 := (Or.elim h26822 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u17))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u18))) (fun r2 => r2))))));
    let u20 : (¬ p3695) := (Or.elim h20311 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u16))) (fun r2 => (False.elim (r2 u19))))))));
    let u21 : (¬ p4883) := (Or.elim h8038 (fun q0 => (False.elim (u20 q0))) (fun r0 => r0));
    let u22 : p4880 := (Or.elim h66398 (fun q0 => q0) (fun r0 => (False.elim (u21 r0))));
    let u23 : p3054 := (Or.elim h8032 (fun q0 => q0) (fun r0 => (False.elim (r0 u22))));
    let u24 : (¬ p3585) := (Or.elim h37227 (fun q0 => (False.elim (q0 u23))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u15 q1))) (fun r1 => r1))));
    let u25 : (¬ p5213) := (Or.elim h8853 (fun q0 => (False.elim (u24 q0))) (fun r0 => r0));
    let u26 : p5215 := (Or.elim h66448 (fun q0 => q0) (fun r0 => (False.elim (u25 r0))));
    let u27 : p5216 := (Or.elim h8860 (fun q0 => (False.elim (q0 u26))) (fun r0 => r0));
    let u28 : p4882 := (Or.elim h8036 (fun q0 => (False.elim (q0 u22))) (fun r0 => r0));
    let u29 : p2427 := (Or.elim h5739 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (False.elim (r1 u16))))));
    let u30 : (¬ p4210) := (Or.elim h22664 (fun q0 => (False.elim (q0 u29))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u17))) (fun r2 => r2))))));
    let u31 : (¬ p4630) := (Or.elim h7399 (fun q0 => (False.elim (u30 q0))) (fun r0 => r0));
    let u32 : p4627 := (Or.elim h66353 (fun q0 => q0) (fun r0 => (False.elim (u31 r0))));
    let u33 : p4629 := (Or.elim h7397 (fun q0 => (False.elim (q0 u32))) (fun r0 => r0));
    let u34 : p2274 := (Or.elim h7208 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u35 : p3646 := (Or.elim h6734 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u16))))));
    let u36 : (¬ p2192) := (Or.elim h5323 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u17))) (fun r1 => (False.elim (r1 u35))))));
    let u37 : (¬ p4515) := (Or.elim h7096 (fun q0 => (False.elim (u36 q0))) (fun r0 => r0));
    let u38 : p4511 := (Or.elim h66332 (fun q0 => q0) (fun r0 => (False.elim (u37 r0))));
    let u39 : p4512 := (Or.elim h7088 (fun q0 => (False.elim (q0 u38))) (fun r0 => r0));
    let u40 : (¬ p3549) := (Or.elim h61082 (fun q0 => (False.elim (q0 u34))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u39))) (fun r3 => (False.elim (r3 u33))))))))));
    let u41 : (¬ p5140) := (Or.elim h8705 (fun q0 => (False.elim (u40 q0))) (fun r0 => r0));
    let u42 : p5143 := (Or.elim h66440 (fun q0 => (False.elim (u41 q0))) (fun r0 => r0));
    let u43 : p3309 := (Or.elim h8711 (fun q0 => q0) (fun r0 => (False.elim (r0 u42))));
    let u44 : p3957 := (Or.elim h7089 (fun q0 => q0) (fun r0 => (False.elim (r0 u38))));
    let u45 : (¬ p3591) := (Or.elim h41941 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u44))) (fun r3 => (False.elim (r3 u33))))))))));
    let u46 : (¬ p5014) := (Or.elim h8386 (fun q0 => (False.elim (u45 q0))) (fun r0 => r0));
    let u47 : p5019 := (Or.elim h66423 (fun q0 => q0) (fun r0 => (False.elim (u46 r0))));
    let u48 : p3093 := (Or.elim h8392 (fun q0 => q0) (fun r0 => (False.elim (r0 u47))));
    let u49 : (¬ p2177) := (Or.elim h52571 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u48))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u43))) (fun r2 => (False.elim (r2 u10))))))));
    let u50 : (¬ p4502) := (Or.elim h7062 (fun q0 => (False.elim (u49 q0))) (fun r0 => r0));
    let u51 : p4500 := (Or.elim h66330 (fun q0 => (False.elim (u50 q0))) (fun r0 => r0));
    let u52 : p4501 := (Or.elim h7057 (fun q0 => (False.elim (q0 u51))) (fun r0 => r0));
    let u53 : p3873 := (Or.elim h7679 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u54 : (¬ p4031) := (Or.elim h20298 (fun q0 => (False.elim (q0 u29))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => r1))));
    let u55 : (¬ p4537) := (Or.elim h7146 (fun q0 => (False.elim (u54 q0))) (fun r0 => r0));
    let u56 : p4535 := (Or.elim h66335 (fun q0 => q0) (fun r0 => (False.elim (u55 r0))));
    let u57 : p3904 := (Or.elim h7140 (fun q0 => q0) (fun r0 => (False.elim (r0 u56))));
    let u58 : (¬ p2651) := (Or.elim h8330 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u59 : (¬ p2661) := (Or.elim h3449 (fun q0 => (False.elim (u58 q0))) (fun r0 => r0));
    let u60 : p2654 := (Or.elim h66378 (fun q0 => q0) (fun r0 => (False.elim (u59 r0))));
    let u61 : p2659 := (Or.elim h3437 (fun q0 => (False.elim (q0 u60))) (fun r0 => r0));
    let u62 : (¬ p2542) := (Or.elim h41572 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u61))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u35))) (fun r3 => (False.elim (r3 u57))))))))));
    let u63 : (¬ p4703) := (Or.elim h7590 (fun q0 => (False.elim (u62 q0))) (fun r0 => r0));
    let u64 : p4699 := (Or.elim h66367 (fun q0 => (False.elim (u63 q0))) (fun r0 => r0));
    let u65 : p4202 := (Or.elim h7393 (fun q0 => q0) (fun r0 => (False.elim (r0 u32))));
    let u66 : p3379 := (Or.elim h6790 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u65))))));
    let u67 : p4533 := (Or.elim h7144 (fun q0 => q0) (fun r0 => (False.elim (r0 u56))));
    let u68 : (¬ p2156) := (Or.elim h20348 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (False.elim (r1 u16))))));
    let u69 : (¬ p4487) := (Or.elim h7028 (fun q0 => (False.elim (u68 q0))) (fun r0 => r0));
    let u70 : p4484 := (Or.elim h66328 (fun q0 => (False.elim (u69 q0))) (fun r0 => r0));
    let u71 : p4198 := (Or.elim h7020 (fun q0 => q0) (fun r0 => (False.elim (r0 u70))));
    let u72 : (¬ p2313) := (Or.elim h60888 (fun q0 => (False.elim (q0 u34))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u71))) (fun r3 => (False.elim (r3 u67))))))))));
    let u73 : (¬ p2310) := (Or.elim h2756 (fun q0 => q0) (fun r0 => (False.elim (u72 r0))));
    let u74 : p2317 := (Or.elim h66343 (fun q0 => q0) (fun r0 => (False.elim (u73 r0))));
    let u75 : p2307 := (Or.elim h2770 (fun q0 => q0) (fun r0 => (False.elim (r0 u74))));
    let u76 : p2737 := (Or.elim h3622 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u77 : p2751 := (Or.elim h3624 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u78 : (¬ p3365) := (Or.elim h49742 (fun q0 => (False.elim (q0 u76))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u66))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u53))) (fun r3 => (False.elim (r3 u27))))))))));
    let u79 : (¬ p4785) := (Or.elim h7805 (fun q0 => (False.elim (u78 q0))) (fun r0 => r0));
    let u80 : p4788 := (Or.elim h66383 (fun q0 => (False.elim (u79 q0))) (fun r0 => r0));
    let u81 : p3361 := (Or.elim h7809 (fun q0 => q0) (fun r0 => (False.elim (r0 u80))));
    let u82 : (¬ p2630) := (Or.elim h4833 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u81))))));
    let u83 : (¬ p4751) := (Or.elim h7721 (fun q0 => (False.elim (u82 q0))) (fun r0 => r0));
    let u84 : p4748 := (Or.elim h66376 (fun q0 => (False.elim (u83 q0))) (fun r0 => r0));
    let u85 : p2810 := (Or.elim h7715 (fun q0 => q0) (fun r0 => (False.elim (r0 u84))));
    let u86 : (¬ p4812) := (Or.elim h66648 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u85))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u77))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u66))))))))));
    let u87 : p4809 := (Or.elim h66386 (fun q0 => q0) (fun r0 => (False.elim (u86 r0))));
    let u88 : p2284 := (Or.elim h66005 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u87))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u28))))))))))));
    (Or.elim h65988 (fun q0 => (False.elim (q0 u38))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u87))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u64))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u52))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u75))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u88))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u16))) (fun r11 => (False.elim (r11 u6)))))))))))))))))))))))))))

theorem step66650 (p2177 p2192 p2210 p2274 p2299 p2427 p2437 p2440 p2542 p2563 p2651 p2654 p2657 p2659 p2661 p2740 p2743 p2747 p2839 p2881 p2891 p2911 p3093 p3309 p3486 p3527 p3548 p3549 p3554 p3556 p3569 p3570 p3591 p3644 p3645 p3646 p3741 p3742 p3872 p3904 p3954 p3957 p4031 p4173 p4186 p4210 p4235 p4243 p4256 p4392 p4452 p4500 p4502 p4511 p4512 p4515 p4523 p4533 p4535 p4537 p4557 p4627 p4629 p4630 p4643 p4645 p4649 p4651 p4699 p4703 p4732 p4873 p4874 p4876 p4900 p4903 p4908 p4912 p4921 p4923 p5014 p5019 p5048 p5050 p5052 p5140 p5143 p5304 p5306 : Prop)
    (h7207 : p3872 ∨ (¬ p4557))
    (h20312 : (¬ p2563) ∨ (¬ p3872) ∨ (¬ p4235))
    (h7429 : p4235 ∨ (¬ p4643))
    (h66355 : p4643 ∨ p4645)
    (h7433 : p3569 ∨ (¬ p4645))
    (h5739 : p2427 ∨ (¬ p2563) ∨ (¬ p3872))
    (h7111 : p3645 ∨ (¬ p4523))
    (h22664 : (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4210))
    (h7399 : p4210 ∨ (¬ p4630))
    (h66353 : p4627 ∨ p4630)
    (h7397 : (¬ p4627) ∨ p4629)
    (h20298 : (¬ p2427) ∨ (¬ p3556) ∨ (¬ p4031))
    (h7146 : p4031 ∨ (¬ p4537))
    (h66335 : p4535 ∨ p4537)
    (h7144 : p4533 ∨ (¬ p4535))
    (h6734 : (¬ p3556) ∨ p3646 ∨ (¬ p3872))
    (h5323 : (¬ p2192) ∨ (¬ p3645) ∨ (¬ p3646))
    (h7096 : p2192 ∨ (¬ p4515))
    (h66332 : p4511 ∨ p4515)
    (h7090 : p4173 ∨ (¬ p4511))
    (h41459 : (¬ p2563) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p4173) ∨ (¬ p4533))
    (h8110 : p2891 ∨ (¬ p4912))
    (h66402 : p4912 ∨ p4908)
    (h8104 : p3486 ∨ (¬ p4908))
    (h7140 : p3904 ∨ (¬ p4535))
    (h8330 : (¬ p2651) ∨ (¬ p2657))
    (h3449 : p2651 ∨ (¬ p2661))
    (h66378 : p2654 ∨ p2661)
    (h3437 : (¬ p2654) ∨ p2659)
    (h41572 : (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2659) ∨ (¬ p3646) ∨ (¬ p3904))
    (h7590 : p2542 ∨ (¬ p4703))
    (h66367 : p4703 ∨ p4699)
    (h7584 : p2440 ∨ (¬ p4699))
    (h63238 : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p3486) ∨ (¬ p3569) ∨ (¬ p4629))
    (h7453 : p2437 ∨ (¬ p4651))
    (h66356 : p4651 ∨ p4649)
    (h7447 : p3742 ∨ (¬ p4649))
    (h8102 : p3554 ∨ (¬ p4908))
    (h7113 : p2210 ∨ (¬ p4523))
    (h7089 : p3957 ∨ (¬ p4511))
    (h41941 : (¬ p2210) ∨ (¬ p2563) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4629))
    (h8386 : p3591 ∨ (¬ p5014))
    (h66423 : p5019 ∨ p5014)
    (h8392 : p3093 ∨ (¬ p5019))
    (h7208 : p2274 ∨ (¬ p4557))
    (h7088 : (¬ p4511) ∨ p4512)
    (h61082 : (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p4629))
    (h8705 : p3549 ∨ (¬ p5140))
    (h66440 : p5140 ∨ p5143)
    (h8711 : p3309 ∨ (¬ p5143))
    (h8710 : p4452 ∨ (¬ p5143))
    (h7681 : p3954 ∨ (¬ p4732))
    (h29892 : (¬ p2210) ∨ (¬ p3954) ∨ (¬ p4874))
    (h52571 : (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3954))
    (h8015 : (¬ p4873) ∨ p4874)
    (h7062 : p2177 ∨ (¬ p4502))
    (h66397 : p4873 ∨ p4876)
    (h66330 : p4502 ∨ p4500)
    (h8021 : p4243 ∨ (¬ p4876))
    (h8023 : p2839 ∨ (¬ p4876))
    (h7056 : p2299 ∨ (¬ p4500))
    (h60034 : (¬ p2299) ∨ (¬ p3093) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4452))
    (h9044 : p3527 ∨ (¬ p5306))
    (h66458 : p5304 ∨ p5306)
    (h9038 : p3548 ∨ (¬ p5304))
    (h40975 : (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4629))
    (h8092 : p2881 ∨ (¬ p4903))
    (h66401 : p4903 ∨ p4900)
    (h8086 : p3570 ∨ (¬ p4900))
    (h41489 : (¬ p2911) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p4533))
    (h8144 : p2911 ∨ (¬ p4923))
    (h66404 : p4923 ∨ p4921)
    (h8136 : p4186 ∨ (¬ p4921))
    (h8138 : p3644 ∨ (¬ p4921))
    (h6402 : (¬ p3742) ∨ (¬ p4186) ∨ p4256)
    (h66649 : (¬ p2747) ∨ (¬ p4256) ∨ (¬ p3644) ∨ (¬ p4732) ∨ (¬ p2657) ∨ (¬ p4523) ∨ (¬ p3556) ∨ (¬ p4557) ∨ (¬ p2563))
    (h66387 : p2740 ∨ p2747)
    (h3608 : (¬ p2740) ∨ p2743)
    (h18646 : (¬ p2743) ∨ (¬ p2839) ∨ (¬ p4392))
    (h50872 : (¬ p2210) ∨ (¬ p2743) ∨ (¬ p3954) ∨ (¬ p4243) ∨ (¬ p5052))
    (h8454 : p4392 ∨ (¬ p5048))
    (h8463 : (¬ p5050) ∨ p5052)
    (h66427 : p5048 ∨ p5050)
    : (¬ p4732) ∨ (¬ p2657) ∨ (¬ p4523) ∨ (¬ p3556) ∨ (¬ p4557) ∨ (¬ p3741) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4732 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4523 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4557 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3872 := (Or.elim h7207 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u8 : (¬ p4235) := (Or.elim h20312 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => r1))));
    let u9 : (¬ p4643) := (Or.elim h7429 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u10 : p4645 := (Or.elim h66355 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u11 : p3569 := (Or.elim h7433 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    let u12 : p2427 := (Or.elim h5739 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (False.elim (r1 u7))))));
    let u13 : p3645 := (Or.elim h7111 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u14 : (¬ p4210) := (Or.elim h22664 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => r2))))));
    let u15 : (¬ p4630) := (Or.elim h7399 (fun q0 => (False.elim (u14 q0))) (fun r0 => r0));
    let u16 : p4627 := (Or.elim h66353 (fun q0 => q0) (fun r0 => (False.elim (u15 r0))));
    let u17 : p4629 := (Or.elim h7397 (fun q0 => (False.elim (q0 u16))) (fun r0 => r0));
    let u18 : (¬ p4031) := (Or.elim h20298 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => r1))));
    let u19 : (¬ p4537) := (Or.elim h7146 (fun q0 => (False.elim (u18 q0))) (fun r0 => r0));
    let u20 : p4535 := (Or.elim h66335 (fun q0 => q0) (fun r0 => (False.elim (u19 r0))));
    let u21 : p4533 := (Or.elim h7144 (fun q0 => q0) (fun r0 => (False.elim (r0 u20))));
    let u22 : p3646 := (Or.elim h6734 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u7))))));
    let u23 : (¬ p2192) := (Or.elim h5323 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (False.elim (r1 u22))))));
    let u24 : (¬ p4515) := (Or.elim h7096 (fun q0 => (False.elim (u23 q0))) (fun r0 => r0));
    let u25 : p4511 := (Or.elim h66332 (fun q0 => q0) (fun r0 => (False.elim (u24 r0))));
    let u26 : p4173 := (Or.elim h7090 (fun q0 => q0) (fun r0 => (False.elim (r0 u25))));
    let u27 : (¬ p2891) := (Or.elim h41459 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u26))) (fun r3 => (False.elim (r3 u21))))))))));
    let u28 : (¬ p4912) := (Or.elim h8110 (fun q0 => (False.elim (u27 q0))) (fun r0 => r0));
    let u29 : p4908 := (Or.elim h66402 (fun q0 => (False.elim (u28 q0))) (fun r0 => r0));
    let u30 : p3486 := (Or.elim h8104 (fun q0 => q0) (fun r0 => (False.elim (r0 u29))));
    let u31 : p3904 := (Or.elim h7140 (fun q0 => q0) (fun r0 => (False.elim (r0 u20))));
    let u32 : (¬ p2651) := (Or.elim h8330 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u33 : (¬ p2661) := (Or.elim h3449 (fun q0 => (False.elim (u32 q0))) (fun r0 => r0));
    let u34 : p2654 := (Or.elim h66378 (fun q0 => q0) (fun r0 => (False.elim (u33 r0))));
    let u35 : p2659 := (Or.elim h3437 (fun q0 => (False.elim (q0 u34))) (fun r0 => r0));
    let u36 : (¬ p2542) := (Or.elim h41572 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u35))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u22))) (fun r3 => (False.elim (r3 u31))))))))));
    let u37 : (¬ p4703) := (Or.elim h7590 (fun q0 => (False.elim (u36 q0))) (fun r0 => r0));
    let u38 : p4699 := (Or.elim h66367 (fun q0 => (False.elim (u37 q0))) (fun r0 => r0));
    let u39 : p2440 := (Or.elim h7584 (fun q0 => q0) (fun r0 => (False.elim (r0 u38))));
    let u40 : (¬ p2437) := (Or.elim h63238 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u39))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u30))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (False.elim (r3 u17))))))))));
    let u41 : (¬ p4651) := (Or.elim h7453 (fun q0 => (False.elim (u40 q0))) (fun r0 => r0));
    let u42 : p4649 := (Or.elim h66356 (fun q0 => (False.elim (u41 q0))) (fun r0 => r0));
    let u43 : p3742 := (Or.elim h7447 (fun q0 => q0) (fun r0 => (False.elim (r0 u42))));
    let u44 : p3554 := (Or.elim h8102 (fun q0 => q0) (fun r0 => (False.elim (r0 u29))));
    let u45 : p2210 := (Or.elim h7113 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u46 : p3957 := (Or.elim h7089 (fun q0 => q0) (fun r0 => (False.elim (r0 u25))));
    let u47 : (¬ p3591) := (Or.elim h41941 (fun q0 => (False.elim (q0 u45))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u46))) (fun r3 => (False.elim (r3 u17))))))))));
    let u48 : (¬ p5014) := (Or.elim h8386 (fun q0 => (False.elim (u47 q0))) (fun r0 => r0));
    let u49 : p5019 := (Or.elim h66423 (fun q0 => q0) (fun r0 => (False.elim (u48 r0))));
    let u50 : p3093 := (Or.elim h8392 (fun q0 => q0) (fun r0 => (False.elim (r0 u49))));
    let u51 : p2274 := (Or.elim h7208 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u52 : p4512 := (Or.elim h7088 (fun q0 => (False.elim (q0 u25))) (fun r0 => r0));
    let u53 : (¬ p3549) := (Or.elim h61082 (fun q0 => (False.elim (q0 u51))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u52))) (fun r3 => (False.elim (r3 u17))))))))));
    let u54 : (¬ p5140) := (Or.elim h8705 (fun q0 => (False.elim (u53 q0))) (fun r0 => r0));
    let u55 : p5143 := (Or.elim h66440 (fun q0 => (False.elim (u54 q0))) (fun r0 => r0));
    let u56 : p3309 := (Or.elim h8711 (fun q0 => q0) (fun r0 => (False.elim (r0 u55))));
    let u57 : p4452 := (Or.elim h8710 (fun q0 => q0) (fun r0 => (False.elim (r0 u55))));
    let u58 : p3954 := (Or.elim h7681 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u59 : (¬ p4874) := (Or.elim h29892 (fun q0 => (False.elim (q0 u45))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u58))) (fun r1 => r1))));
    let u60 : (¬ p2177) := (Or.elim h52571 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u50))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u56))) (fun r2 => (False.elim (r2 u58))))))));
    let u61 : (¬ p4873) := (Or.elim h8015 (fun q0 => q0) (fun r0 => (False.elim (u59 r0))));
    let u62 : (¬ p4502) := (Or.elim h7062 (fun q0 => (False.elim (u60 q0))) (fun r0 => r0));
    let u63 : p4876 := (Or.elim h66397 (fun q0 => (False.elim (u61 q0))) (fun r0 => r0));
    let u64 : p4500 := (Or.elim h66330 (fun q0 => (False.elim (u62 q0))) (fun r0 => r0));
    let u65 : p4243 := (Or.elim h8021 (fun q0 => q0) (fun r0 => (False.elim (r0 u63))));
    let u66 : p2839 := (Or.elim h8023 (fun q0 => q0) (fun r0 => (False.elim (r0 u63))));
    let u67 : p2299 := (Or.elim h7056 (fun q0 => q0) (fun r0 => (False.elim (r0 u64))));
    let u68 : (¬ p3527) := (Or.elim h60034 (fun q0 => (False.elim (q0 u67))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u50))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u58))) (fun r3 => (False.elim (r3 u57))))))))));
    let u69 : (¬ p5306) := (Or.elim h9044 (fun q0 => (False.elim (u68 q0))) (fun r0 => r0));
    let u70 : p5304 := (Or.elim h66458 (fun q0 => q0) (fun r0 => (False.elim (u69 r0))));
    let u71 : p3548 := (Or.elim h9038 (fun q0 => q0) (fun r0 => (False.elim (r0 u70))));
    let u72 : (¬ p2881) := (Or.elim h40975 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u71))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u44))) (fun r3 => (False.elim (r3 u17))))))))));
    let u73 : (¬ p4903) := (Or.elim h8092 (fun q0 => (False.elim (u72 q0))) (fun r0 => r0));
    let u74 : p4900 := (Or.elim h66401 (fun q0 => (False.elim (u73 q0))) (fun r0 => r0));
    let u75 : p3570 := (Or.elim h8086 (fun q0 => q0) (fun r0 => (False.elim (r0 u74))));
    let u76 : (¬ p2911) := (Or.elim h41489 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u75))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u21))))))))));
    let u77 : (¬ p4923) := (Or.elim h8144 (fun q0 => (False.elim (u76 q0))) (fun r0 => r0));
    let u78 : p4921 := (Or.elim h66404 (fun q0 => (False.elim (u77 q0))) (fun r0 => r0));
    let u79 : p4186 := (Or.elim h8136 (fun q0 => q0) (fun r0 => (False.elim (r0 u78))));
    let u80 : p3644 := (Or.elim h8138 (fun q0 => q0) (fun r0 => (False.elim (r0 u78))));
    let u81 : p4256 := (Or.elim h6402 (fun q0 => (False.elim (q0 u43))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u79))) (fun r1 => r1))));
    let u82 : (¬ p2747) := (Or.elim h66649 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u81))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u80))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u6))))))))))))))))));
    let u83 : p2740 := (Or.elim h66387 (fun q0 => q0) (fun r0 => (False.elim (u82 r0))));
    let u84 : p2743 := (Or.elim h3608 (fun q0 => (False.elim (q0 u83))) (fun r0 => r0));
    let u85 : (¬ p4392) := (Or.elim h18646 (fun q0 => (False.elim (q0 u84))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u66))) (fun r1 => r1))));
    let u86 : (¬ p5052) := (Or.elim h50872 (fun q0 => (False.elim (q0 u45))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u84))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u58))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u65))) (fun r3 => r3))))))));
    let u87 : (¬ p5048) := (Or.elim h8454 (fun q0 => (False.elim (u85 q0))) (fun r0 => r0));
    let u88 : (¬ p5050) := (Or.elim h8463 (fun q0 => q0) (fun r0 => (False.elim (u86 r0))));
    (Or.elim h66427 (fun q0 => (False.elim (u87 q0))) (fun r0 => (False.elim (u88 r0)))))

theorem step66651 (p1 p7 p2081 : Prop)
    (h2296 : (¬ p1) ∨ p2081)
    (h2297 : (¬ p7) ∨ p2081)
    (h13 : p1 ∨ p7)
    : p2081 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2081) := (fun h => hn h);
    let u1 : (¬ p1) := (Or.elim h2296 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p7) := (Or.elim h2297 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h13 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step66652 (p2081 p2082 : Prop)
    (h66651 : p2081)
    (h2314 : (¬ p2081) ∨ p2082)
    : p2082 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2082) := (fun h => hn h);
    let u1 : p2081 := h66651;
    (Or.elim h2314 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step66653 (p2082 p4453 : Prop)
    (h66652 : p2082)
    (h6959 : (¬ p2082) ∨ p4453)
    : p4453 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4453) := (fun h => hn h);
    let u1 : p2082 := h66652;
    (Or.elim h6959 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step66654 (p4453 p5784 : Prop)
    (h66653 : p4453)
    (h11728 : (¬ p4453) ∨ p5784)
    : p5784 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5784) := (fun h => hn h);
    let u1 : p4453 := h66653;
    (Or.elim h11728 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step66658 (p2299 p2588 p2630 p2657 p2810 p3361 p3367 p3422 p3475 p3574 p3584 p3585 p4236 p4748 p4751 p4785 p4787 p4788 p5213 p5215 p5219 p5223 : Prop)
    (h43874 : (¬ p2299) ∨ (¬ p2588) ∨ (¬ p2810) ∨ (¬ p3574))
    (h7715 : p2810 ∨ (¬ p4748))
    (h66376 : p4751 ∨ p4748)
    (h7720 : p3475 ∨ (¬ p4751))
    (h7721 : p2630 ∨ (¬ p4751))
    (h4833 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3361))
    (h7809 : p3361 ∨ (¬ p4788))
    (h66383 : p4785 ∨ p4788)
    (h7803 : p4236 ∨ (¬ p4785))
    (h7807 : (¬ p4785) ∨ p4787)
    (h65870 : (¬ p3367) ∨ (¬ p4787) ∨ (¬ p4236) ∨ (¬ p2657) ∨ (¬ p4751))
    (h51047 : (¬ p2657) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p3574) ∨ (¬ p4787))
    (h8859 : p3367 ∨ (¬ p5215))
    (h8879 : p3422 ∨ (¬ p5223))
    (h66448 : p5215 ∨ p5213)
    (h66449 : p5219 ∨ p5223)
    (h8853 : p3585 ∨ (¬ p5213))
    (h8873 : p3584 ∨ (¬ p5219))
    (h43890 : (¬ p2299) ∨ (¬ p2588) ∨ (¬ p3584) ∨ (¬ p3585))
    : (¬ p3574) ∨ (¬ p2588) ∨ (¬ p2299) ∨ (¬ p2657) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3574 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2810) := (Or.elim h43874 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u0))))))));
    let u5 : (¬ p4748) := (Or.elim h7715 (fun q0 => (False.elim (u4 q0))) (fun r0 => r0));
    let u6 : p4751 := (Or.elim h66376 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u7 : p3475 := (Or.elim h7720 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u8 : p2630 := (Or.elim h7721 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u9 : (¬ p3361) := (Or.elim h4833 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => r1))));
    let u10 : (¬ p4788) := (Or.elim h7809 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u11 : p4785 := (Or.elim h66383 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u12 : p4236 := (Or.elim h7803 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    let u13 : p4787 := (Or.elim h7807 (fun q0 => (False.elim (q0 u11))) (fun r0 => r0));
    let u14 : (¬ p3367) := (Or.elim h65870 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6))))))))));
    let u15 : (¬ p3422) := (Or.elim h51047 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u13))))))))));
    let u16 : (¬ p5215) := (Or.elim h8859 (fun q0 => (False.elim (u14 q0))) (fun r0 => r0));
    let u17 : (¬ p5223) := (Or.elim h8879 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u18 : p5213 := (Or.elim h66448 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    let u19 : p5219 := (Or.elim h66449 (fun q0 => q0) (fun r0 => (False.elim (u17 r0))));
    let u20 : p3585 := (Or.elim h8853 (fun q0 => q0) (fun r0 => (False.elim (r0 u18))));
    let u21 : p3584 := (Or.elim h8873 (fun q0 => q0) (fun r0 => (False.elim (r0 u19))));
    (Or.elim h43890 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u21))) (fun r2 => (False.elim (r2 u20)))))))))

theorem step66659 (p2406 p2493 p2509 p2563 p3238 p3693 p3880 p4203 p4507 p4606 p4627 p4630 p4716 : Prop)
    (h7624 : p2563 ∨ (¬ p4716))
    (h7622 : p4203 ∨ (¬ p4716))
    (h7342 : p3693 ∨ (¬ p4606))
    (h7343 : p3880 ∨ (¬ p4606))
    (h53958 : (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2563) ∨ (¬ p3693) ∨ (¬ p4507))
    (h63184 : (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3880) ∨ (¬ p4203) ∨ (¬ p4507))
    (h7401 : p2406 ∨ (¬ p4630))
    (h7395 : p3238 ∨ (¬ p4627))
    (h66353 : p4627 ∨ p4630)
    : (¬ p4606) ∨ (¬ p2493) ∨ (¬ p4507) ∨ (¬ p2509) ∨ (¬ p4716) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4606 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4716 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2563 := (Or.elim h7624 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u6 : p4203 := (Or.elim h7622 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u7 : p3693 := (Or.elim h7342 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : p3880 := (Or.elim h7343 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u9 : (¬ p2406) := (Or.elim h53958 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u2))))))))));
    let u10 : (¬ p3238) := (Or.elim h63184 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2))))))))));
    let u11 : (¬ p4630) := (Or.elim h7401 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u12 : (¬ p4627) := (Or.elim h7395 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    (Or.elim h66353 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u11 r0)))))

theorem step66660 (p2373 p2542 p3016 p3497 p3742 p4186 p4355 p4609 p4699 p4700 p4703 p4717 : Prop)
    (h7348 : p4355 ∨ (¬ p4609))
    (h7349 : p2373 ∨ (¬ p4609))
    (h20162 : (¬ p2542) ∨ (¬ p3742) ∨ (¬ p4186) ∨ (¬ p4355))
    (h41712 : (¬ p2373) ∨ (¬ p3016) ∨ (¬ p3497) ∨ (¬ p4700) ∨ (¬ p4717))
    (h7590 : p2542 ∨ (¬ p4703))
    (h7582 : (¬ p4699) ∨ p4700)
    (h66367 : p4703 ∨ p4699)
    : (¬ p4609) ∨ (¬ p3742) ∨ (¬ p3016) ∨ (¬ p3497) ∨ (¬ p4186) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4355 := (Or.elim h7348 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p2373 := (Or.elim h7349 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : (¬ p2542) := (Or.elim h20162 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6))))))));
    let u9 : (¬ p4700) := (Or.elim h41712 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u5))))))))));
    let u10 : (¬ p4703) := (Or.elim h7590 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : (¬ p4699) := (Or.elim h7582 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h66367 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u11 r0)))))

theorem step66663 (p2737 p2850 p3054 p3238 p3367 p3583 p3585 p4257 p4749 p4880 p4883 p5213 p5215 : Prop)
    (h8999 : (¬ p3367) ∨ (¬ p3585))
    (h37227 : (¬ p3054) ∨ p3583 ∨ (¬ p3585))
    (h8859 : p3367 ∨ (¬ p5215))
    (h8032 : p3054 ∨ (¬ p4880))
    (h66448 : p5215 ∨ p5213)
    (h66398 : p4880 ∨ p4883)
    (h8851 : p4257 ∨ (¬ p5213))
    (h8040 : p2850 ∨ (¬ p4883))
    (h41294 : (¬ p2737) ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p4257) ∨ (¬ p4749))
    : (¬ p3585) ∨ p3583 ∨ (¬ p4749) ∨ (¬ p2737) ∨ (¬ p3238) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3585 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3583) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3367) := (Or.elim h8999 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : (¬ p3054) := (Or.elim h37227 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u0))))));
    let u7 : (¬ p5215) := (Or.elim h8859 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    let u8 : (¬ p4880) := (Or.elim h8032 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    let u9 : p5213 := (Or.elim h66448 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u10 : p4883 := (Or.elim h66398 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : p4257 := (Or.elim h8851 (fun q0 => q0) (fun r0 => (False.elim (r0 u9))));
    let u12 : p2850 := (Or.elim h8040 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    (Or.elim h41294 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step66669 (p2363 p2406 p2496 p2497 p2499 p2509 p2528 p2534 p3453 p3573 p4261 p4371 p4608 p4692 p4694 : Prop)
    (h3125 : (¬ p2496) ∨ p2497)
    (h3127 : (¬ p2496) ∨ p2499)
    (h37493 : (¬ p2497) ∨ p3453 ∨ (¬ p4371))
    (h22593 : (¬ p2499) ∨ p2509 ∨ (¬ p3573))
    (h49121 : (¬ p2406) ∨ (¬ p2528) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4608))
    (h57873 : (¬ p2363) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2534))
    (h7573 : p2528 ∨ (¬ p4694))
    (h7567 : p2534 ∨ (¬ p4692))
    (h66366 : p4692 ∨ p4694)
    : (¬ p2496) ∨ (¬ p2406) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p3573) ∨ (¬ p2363) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2496 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2497 := (Or.elim h3125 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u8 : p2499 := (Or.elim h3127 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u9 : p3453 := (Or.elim h37493 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u3))))));
    let u10 : p2509 := (Or.elim h22593 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u4))))));
    let u11 : (¬ p2528) := (Or.elim h49121 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6))))))))));
    let u12 : (¬ p2534) := (Or.elim h57873 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => r2))))));
    let u13 : (¬ p4694) := (Or.elim h7573 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    let u14 : (¬ p4692) := (Or.elim h7567 (fun q0 => (False.elim (u12 q0))) (fun r0 => r0));
    (Or.elim h66366 (fun q0 => (False.elim (u14 q0))) (fun r0 => (False.elim (u13 r0)))))

theorem step66674 (p2299 p3570 p3872 p3989 p4138 p4275 p4500 p4554 p4557 : Prop)
    (h7056 : p2299 ∨ (¬ p4500))
    (h7055 : p4138 ∨ (¬ p4500))
    (h27210 : p3570 ∨ (¬ p3872) ∨ (¬ p3989) ∨ (¬ p4138))
    (h6943 : (¬ p2299) ∨ p3570 ∨ (¬ p4275))
    (h7207 : p3872 ∨ (¬ p4557))
    (h7201 : p4275 ∨ (¬ p4554))
    (h66340 : p4554 ∨ p4557)
    : p3570 ∨ (¬ p3989) ∨ (¬ p4500) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3570) := (fun h => hn (Or.inl h));
    let u1 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4500 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2299 := (Or.elim h7056 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u4 : p4138 := (Or.elim h7055 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u5 : (¬ p3872) := (Or.elim h27210 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4))))))));
    let u6 : (¬ p4275) := (Or.elim h6943 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => r1))));
    let u7 : (¬ p4557) := (Or.elim h7207 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    let u8 : (¬ p4554) := (Or.elim h7201 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    (Or.elim h66340 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u7 r0)))))

theorem step66677 (p2187 p2383 p3063 p3093 p3204 p3860 p4514 p4992 p4993 p4996 p5019 : Prop)
    (h8390 : p3204 ∨ (¬ p5019))
    (h8392 : p3093 ∨ (¬ p5019))
    (h6329 : p2383 ∨ (¬ p3063) ∨ (¬ p3204))
    (h54781 : (¬ p2187) ∨ (¬ p3093) ∨ (¬ p3860) ∨ (¬ p4514) ∨ (¬ p4993))
    (h8340 : p3063 ∨ (¬ p4996))
    (h8333 : (¬ p4992) ∨ p4993)
    (h66420 : p4992 ∨ p4996)
    : (¬ p5019) ∨ p2383 ∨ (¬ p3860) ∨ (¬ p4514) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3204 := (Or.elim h8390 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p3093 := (Or.elim h8392 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : (¬ p3063) := (Or.elim h6329 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u5))))));
    let u8 : (¬ p4993) := (Or.elim h54781 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    let u9 : (¬ p4996) := (Or.elim h8340 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u10 : (¬ p4992) := (Or.elim h8333 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h66420 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u9 r0)))))

theorem step66678 (p2187 p2241 p2352 p2383 p2387 p3063 p3379 p3591 p3860 p3923 p4514 p4756 p4992 p4996 p5014 p5015 p5019 : Prop)
    (h9785 : (¬ p2383) ∨ (¬ p2387))
    (h66677 : (¬ p5019) ∨ p2383 ∨ (¬ p3860) ∨ (¬ p4514) ∨ (¬ p2187))
    (h66423 : p5019 ∨ p5014)
    (h8384 : (¬ p5014) ∨ p5015)
    (h8386 : p3591 ∨ (¬ p5014))
    (h55404 : (¬ p2241) ∨ (¬ p2387) ∨ (¬ p3063) ∨ (¬ p4756) ∨ (¬ p5015))
    (h43981 : (¬ p2352) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3923))
    (h8340 : p3063 ∨ (¬ p4996))
    (h8334 : p3923 ∨ (¬ p4992))
    (h66420 : p4992 ∨ p4996)
    : (¬ p2387) ∨ (¬ p2352) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p2241) ∨ (¬ p4514) ∨ (¬ p4756) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4756 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2383) := (Or.elim h9785 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u9 : (¬ p5019) := (Or.elim h66677 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7))))))))));
    let u10 : p5014 := (Or.elim h66423 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u11 : p5015 := (Or.elim h8384 (fun q0 => (False.elim (q0 u10))) (fun r0 => r0));
    let u12 : p3591 := (Or.elim h8386 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    let u13 : (¬ p3063) := (Or.elim h55404 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u11))))))))));
    let u14 : (¬ p3923) := (Or.elim h43981 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => r2))))));
    let u15 : (¬ p4996) := (Or.elim h8340 (fun q0 => (False.elim (u13 q0))) (fun r0 => r0));
    let u16 : (¬ p4992) := (Or.elim h8334 (fun q0 => (False.elim (u14 q0))) (fun r0 => r0));
    (Or.elim h66420 (fun q0 => (False.elim (u16 q0))) (fun r0 => (False.elim (u15 r0)))))

theorem step66679 (p2122 p2542 p2589 p2655 p2786 p3063 p3227 p3343 p3359 p3379 p3399 p3461 p3547 p3549 p3591 p3654 p3680 p3822 p3830 p3834 p3860 p3917 p3955 p3990 p4026 p4191 p4317 p4444 p4470 p4474 p4697 p4789 p4811 p4871 p4996 p5140 p5143 p5147 p5151 p5152 p5169 p5174 p5246 p5251 p5485 p5490 : Prop)
    (h8339 : p4317 ∨ (¬ p4996))
    (h8340 : p3063 ∨ (¬ p4996))
    (h29238 : p3591 ∨ (¬ p3860) ∨ (¬ p4317))
    (h19944 : (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3955))
    (h19762 : (¬ p3063) ∨ (¬ p3990) ∨ (¬ p4026))
    (h8705 : p3549 ∨ (¬ p5140))
    (h8723 : p4026 ∨ (¬ p5147))
    (h66440 : p5140 ∨ p5143)
    (h66441 : p5147 ∨ p5151)
    (h8709 : p3547 ∨ (¬ p5143))
    (h8727 : (¬ p5151) ∨ p5152)
    (h62951 : (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591) ∨ (¬ p3822) ∨ (¬ p4871))
    (h42269 : (¬ p3591) ∨ (¬ p3830) ∨ (¬ p3917) ∨ (¬ p4871) ∨ (¬ p5152))
    (h6984 : p3822 ∨ (¬ p4470))
    (h9539 : p3830 ∨ (¬ p5490))
    (h66324 : p4474 ∨ p4470)
    (h66478 : p5485 ∨ p5490)
    (h6990 : p2122 ∨ (¬ p4474))
    (h9533 : p3834 ∨ (¬ p5485))
    (h46854 : (¬ p2122) ∨ (¬ p3680) ∨ (¬ p3917) ∨ (¬ p4191))
    (h42260 : (¬ p3227) ∨ (¬ p3343) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p4811))
    (h8928 : p4191 ∨ (¬ p5246))
    (h8765 : p3343 ∨ (¬ p5174))
    (h66452 : p5246 ∨ p5251)
    (h66443 : p5169 ∨ p5174)
    (h8934 : p3461 ∨ (¬ p5251))
    (h8759 : p3359 ∨ (¬ p5169))
    (h49052 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2786) ∨ (¬ p3359) ∨ (¬ p3461) ∨ (¬ p3654) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p4789))
    : (¬ p4996) ∨ (¬ p3917) ∨ (¬ p3654) ∨ (¬ p4444) ∨ (¬ p3399) ∨ (¬ p3680) ∨ (¬ p2589) ∨ (¬ p3227) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4697) ∨ (¬ p2786) ∨ (¬ p4789) ∨ (¬ p4811) ∨ (¬ p4871) ∨ (¬ p3990) ∨ (¬ p3955) ∨ (¬ p2655) ∨ (¬ p2542) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3227 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p4871 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))));
    let u19 : p4317 := (Or.elim h8339 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u20 : p3063 := (Or.elim h8340 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u21 : p3591 := (Or.elim h29238 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (False.elim (r1 u19))))));
    let u22 : (¬ p3549) := (Or.elim h19944 (fun q0 => (False.elim (q0 u20))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u16))))));
    let u23 : (¬ p4026) := (Or.elim h19762 (fun q0 => (False.elim (q0 u20))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u15))) (fun r1 => r1))));
    let u24 : (¬ p5140) := (Or.elim h8705 (fun q0 => (False.elim (u22 q0))) (fun r0 => r0));
    let u25 : (¬ p5147) := (Or.elim h8723 (fun q0 => (False.elim (u23 q0))) (fun r0 => r0));
    let u26 : p5143 := (Or.elim h66440 (fun q0 => (False.elim (u24 q0))) (fun r0 => r0));
    let u27 : p5151 := (Or.elim h66441 (fun q0 => (False.elim (u25 q0))) (fun r0 => r0));
    let u28 : p3547 := (Or.elim h8709 (fun q0 => q0) (fun r0 => (False.elim (r0 u26))));
    let u29 : p5152 := (Or.elim h8727 (fun q0 => (False.elim (q0 u27))) (fun r0 => r0));
    let u30 : (¬ p3822) := (Or.elim h62951 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u28))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u21))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u14))))))))));
    let u31 : (¬ p3830) := (Or.elim h42269 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (False.elim (r3 u29))))))))));
    let u32 : (¬ p4470) := (Or.elim h6984 (fun q0 => (False.elim (u30 q0))) (fun r0 => r0));
    let u33 : (¬ p5490) := (Or.elim h9539 (fun q0 => (False.elim (u31 q0))) (fun r0 => r0));
    let u34 : p4474 := (Or.elim h66324 (fun q0 => q0) (fun r0 => (False.elim (u32 r0))));
    let u35 : p5485 := (Or.elim h66478 (fun q0 => q0) (fun r0 => (False.elim (u33 r0))));
    let u36 : p2122 := (Or.elim h6990 (fun q0 => q0) (fun r0 => (False.elim (r0 u34))));
    let u37 : p3834 := (Or.elim h9533 (fun q0 => q0) (fun r0 => (False.elim (r0 u35))));
    let u38 : (¬ p4191) := (Or.elim h46854 (fun q0 => (False.elim (q0 u36))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    let u39 : (¬ p3343) := (Or.elim h42260 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u37))) (fun r3 => (False.elim (r3 u13))))))))));
    let u40 : (¬ p5246) := (Or.elim h8928 (fun q0 => (False.elim (u38 q0))) (fun r0 => r0));
    let u41 : (¬ p5174) := (Or.elim h8765 (fun q0 => (False.elim (u39 q0))) (fun r0 => r0));
    let u42 : p5251 := (Or.elim h66452 (fun q0 => (False.elim (u40 q0))) (fun r0 => r0));
    let u43 : p5169 := (Or.elim h66443 (fun q0 => q0) (fun r0 => (False.elim (u41 r0))));
    let u44 : p3461 := (Or.elim h8934 (fun q0 => q0) (fun r0 => (False.elim (r0 u42))));
    let u45 : p3359 := (Or.elim h8759 (fun q0 => q0) (fun r0 => (False.elim (r0 u43))));
    (Or.elim h49052 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u17))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u45))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u44))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u12)))))))))))))))))))))

theorem step66680 (p2098 p2187 p2230 p2241 p2252 p2352 p2383 p2387 p2406 p2427 p2437 p2440 p2441 p2542 p2589 p2651 p2654 p2655 p2661 p2740 p2741 p2747 p2748 p2750 p2753 p2761 p2786 p2911 p2922 p2925 p2927 p2932 p2952 p3083 p3093 p3222 p3225 p3227 p3231 p3237 p3238 p3266 p3365 p3379 p3399 p3413 p3483 p3570 p3609 p3644 p3654 p3680 p3690 p3742 p3860 p3868 p3873 p3917 p3923 p3954 p3955 p3990 p4001 p4079 p4129 p4235 p4241 p4256 p4320 p4322 p4358 p4366 p4370 p4381 p4383 p4402 p4432 p4444 p4514 p4535 p4537 p4594 p4597 p4608 p4612 p4615 p4621 p4627 p4630 p4643 p4645 p4649 p4651 p4683 p4686 p4688 p4697 p4699 p4703 p4729 p4732 p4756 p4785 p4788 p4789 p4811 p4822 p4827 p4831 p4871 p4921 p4923 p4992 p4993 p4996 p5007 p5010 p5014 p5016 p5019 p5115 p5120 p5192 p5205 p5209 p5216 p5263 p5268 p5396 p5401 p5500 p5503 p5506 p5555 p5558 p5561 p5564 p5659 p5660 p5663 : Prop)
    (h63296 : (¬ p2952) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4381))
    (h7902 : p4381 ∨ (¬ p4822))
    (h66390 : p4827 ∨ p4822)
    (h7910 : (¬ p4827) ∨ p4831)
    (h7908 : p2761 ∨ (¬ p4827))
    (h7679 : p3873 ∨ (¬ p4732))
    (h7681 : p3954 ∨ (¬ p4732))
    (h6267 : (¬ p2241) ∨ (¬ p2741) ∨ (¬ p3954))
    (h3606 : (¬ p2740) ∨ p2741)
    (h66387 : p2740 ∨ p2747)
    (h3620 : (¬ p2747) ∨ p2748)
    (h27638 : (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3873))
    (h7805 : p3365 ∨ (¬ p4785))
    (h66383 : p4785 ∨ p4788)
    (h7812 : (¬ p4788) ∨ p4789)
    (h3623 : (¬ p2747) ∨ p2750)
    (h9451 : (¬ p2440) ∨ (¬ p2542))
    (h7584 : p2440 ∨ (¬ p4699))
    (h66367 : p4703 ∨ p4699)
    (h7588 : p4241 ∨ (¬ p4703))
    (h24547 : (¬ p2427) ∨ (¬ p4241) ∨ (¬ p4320))
    (h7435 : p2427 ∨ (¬ p4645))
    (h66355 : p4643 ∨ p4645)
    (h7428 : p4001 ∨ (¬ p4643))
    (h20262 : (¬ p2911) ∨ (¬ p3570) ∨ (¬ p4001))
    (h8144 : p2911 ∨ (¬ p4923))
    (h66404 : p4923 ∨ p4921)
    (h8137 : p4383 ∨ (¬ p4921))
    (h63098 : (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p5558))
    (h9721 : (¬ p5555) ∨ p5558)
    (h66484 : p5555 ∨ p5561)
    (h9728 : (¬ p5561) ∨ p5564)
    (h5947 : (¬ p3570) ∨ p3644 ∨ (¬ p4001))
    (h7680 : p2753 ∨ (¬ p4732))
    (h7589 : p3413 ∨ (¬ p4703))
    (h14339 : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3413))
    (h3449 : p2651 ∨ (¬ p2661))
    (h66378 : p2654 ∨ p2661)
    (h3433 : (¬ p2654) ∨ p2655)
    (h7427 : p2441 ∨ (¬ p4643))
    (h26527 : p4235 ∨ (¬ p4241) ∨ (¬ p4320))
    (h8804 : p4079 ∨ (¬ p5192))
    (h8805 : p3379 ∨ (¬ p5192))
    (h20283 : (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4688))
    (h7555 : (¬ p4686) ∨ p4688)
    (h66365 : p4683 ∨ p4686)
    (h7549 : p4370 ∨ (¬ p4683))
    (h42186 : (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4370) ∨ (¬ p4608))
    (h42261 : (¬ p3083) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4370) ∨ (¬ p4811))
    (h7401 : p2406 ∨ (¬ p4630))
    (h8375 : p3083 ∨ (¬ p5010))
    (h66353 : p4627 ∨ p4630)
    (h66422 : p5007 ∨ p5010)
    (h7395 : p3238 ∨ (¬ p4627))
    (h8369 : p4256 ∨ (¬ p5007))
    (h4598 : (¬ p2441) ∨ (¬ p2922) ∨ (¬ p3238))
    (h4597 : (¬ p3222) ∨ (¬ p3237) ∨ (¬ p3238))
    (h49291 : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3954) ∨ (¬ p4079) ∨ (¬ p5216))
    (h3992 : p2922 ∨ (¬ p2932))
    (h4585 : p3222 ∨ (¬ p3231))
    (h7148 : p2230 ∨ (¬ p4537))
    (h66405 : p2932 ∨ p2925)
    (h66433 : p3225 ∨ p3231)
    (h66335 : p4535 ∨ p4537)
    (h3977 : (¬ p2925) ∨ p2927)
    (h4570 : (¬ p3225) ∨ p3227)
    (h7142 : p2589 ∨ (¬ p4535))
    (h53117 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3644) ∨ (¬ p3742))
    (h44001 : (¬ p2589) ∨ (¬ p2761) ∨ (¬ p4235) ∨ (¬ p4322) ∨ (¬ p4402))
    (h57164 : (¬ p2187) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p4256) ∨ (¬ p4432))
    (h7447 : p3742 ∨ (¬ p4649))
    (h9308 : p4322 ∨ (¬ p5396))
    (h7308 : p4432 ∨ (¬ p4594))
    (h66356 : p4651 ∨ p4649)
    (h66468 : p5396 ∨ p5401)
    (h66348 : p4597 ∨ p4594)
    (h7453 : p2437 ∨ (¬ p4651))
    (h9314 : p3680 ∨ (¬ p5401))
    (h7315 : p2352 ∨ (¬ p4597))
    (h41590 : (¬ p2437) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p4811))
    (h42265 : (¬ p2437) ∨ (¬ p3868) ∨ (¬ p4256) ∨ (¬ p4383) ∨ (¬ p5564))
    (h8833 : p4366 ∨ (¬ p5205))
    (h9589 : p3868 ∨ (¬ p5506))
    (h66447 : p5209 ∨ p5205)
    (h66479 : p5500 ∨ p5506)
    (h8839 : p3399 ∨ (¬ p5209))
    (h9583 : (¬ p5500) ∨ p5503)
    (h43991 : (¬ p2441) ∨ (¬ p2589) ∨ (¬ p3690) ∨ (¬ p4129) ∨ (¬ p5503))
    (h10125 : p4129 ∨ (¬ p5663))
    (h66493 : p5659 ∨ p5663)
    (h10119 : (¬ p5659) ∨ p5660)
    (h55859 : (¬ p2098) ∨ (¬ p2589) ∨ (¬ p3266) ∨ (¬ p3609) ∨ (¬ p4235) ∨ (¬ p4729) ∨ (¬ p4831) ∨ (¬ p5660))
    (h8652 : p3266 ∨ (¬ p5120))
    (h66438 : p5115 ∨ p5120)
    (h8646 : p4444 ∨ (¬ p5115))
    (h66678 : (¬ p2387) ∨ (¬ p2352) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p2241) ∨ (¬ p4514) ∨ (¬ p4756) ∨ (¬ p2187))
    (h7361 : p2387 ∨ (¬ p4612))
    (h66351 : p4615 ∨ p4612)
    (h7367 : p2383 ∨ (¬ p4615))
    (h57165 : (¬ p2252) ∨ (¬ p2383) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2786) ∨ (¬ p2952) ∨ (¬ p3483) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4358) ∨ (¬ p4621))
    (h6818 : (¬ p2383) ∨ p3654 ∨ (¬ p3990))
    (h8968 : p3483 ∨ (¬ p5268))
    (h66454 : p5263 ∨ p5268)
    (h8962 : p3917 ∨ (¬ p5263))
    (h66679 : (¬ p4996) ∨ (¬ p3917) ∨ (¬ p3654) ∨ (¬ p4444) ∨ (¬ p3399) ∨ (¬ p3680) ∨ (¬ p2589) ∨ (¬ p3227) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4697) ∨ (¬ p2786) ∨ (¬ p4789) ∨ (¬ p4811) ∨ (¬ p4871) ∨ (¬ p3990) ∨ (¬ p3955) ∨ (¬ p2655) ∨ (¬ p2542))
    (h66420 : p4992 ∨ p4996)
    (h8333 : (¬ p4992) ∨ p4993)
    (h8334 : p3923 ∨ (¬ p4992))
    (h54781 : (¬ p2187) ∨ (¬ p3093) ∨ (¬ p3860) ∨ (¬ p4514) ∨ (¬ p4993))
    (h19898 : (¬ p2383) ∨ (¬ p3923) ∨ (¬ p5016))
    (h8392 : p3093 ∨ (¬ p5019))
    (h8385 : (¬ p5014) ∨ p5016)
    (h66423 : p5019 ∨ p5014)
    : (¬ p5192) ∨ (¬ p2098) ∨ (¬ p3237) ∨ (¬ p4358) ∨ (¬ p3860) ∨ (¬ p4697) ∨ (¬ p3690) ∨ (¬ p4402) ∨ (¬ p4621) ∨ (¬ p4729) ∨ (¬ p3609) ∨ (¬ p5216) ∨ (¬ p2786) ∨ (¬ p2241) ∨ (¬ p2252) ∨ (¬ p4514) ∨ (¬ p4811) ∨ (¬ p4756) ∨ (¬ p3570) ∨ (¬ p4871) ∨ (¬ p3990) ∨ (¬ p3955) ∨ (¬ p4732) ∨ (¬ p2187) ∨ (¬ p2542) ∨ (¬ p2952) ∨ (¬ p4320) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p4756 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p4871 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p4732 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))));
    let u25 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))));
    let u26 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))));
    let u27 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))))))))))))));
    let u28 : (¬ p4381) := (Or.elim h63296 (fun q0 => (False.elim (q0 u25))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u26))) (fun r2 => r2))))));
    let u29 : (¬ p4822) := (Or.elim h7902 (fun q0 => (False.elim (u28 q0))) (fun r0 => r0));
    let u30 : p4827 := (Or.elim h66390 (fun q0 => q0) (fun r0 => (False.elim (u29 r0))));
    let u31 : p4831 := (Or.elim h7910 (fun q0 => (False.elim (q0 u30))) (fun r0 => r0));
    let u32 : p2761 := (Or.elim h7908 (fun q0 => q0) (fun r0 => (False.elim (r0 u30))));
    let u33 : p3873 := (Or.elim h7679 (fun q0 => q0) (fun r0 => (False.elim (r0 u22))));
    let u34 : p3954 := (Or.elim h7681 (fun q0 => q0) (fun r0 => (False.elim (r0 u22))));
    let u35 : (¬ p2741) := (Or.elim h6267 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u34))))));
    let u36 : (¬ p2740) := (Or.elim h3606 (fun q0 => q0) (fun r0 => (False.elim (u35 r0))));
    let u37 : p2747 := (Or.elim h66387 (fun q0 => (False.elim (u36 q0))) (fun r0 => r0));
    let u38 : p2748 := (Or.elim h3620 (fun q0 => (False.elim (q0 u37))) (fun r0 => r0));
    let u39 : (¬ p3365) := (Or.elim h27638 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u38))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u33))))))));
    let u40 : (¬ p4785) := (Or.elim h7805 (fun q0 => (False.elim (u39 q0))) (fun r0 => r0));
    let u41 : p4788 := (Or.elim h66383 (fun q0 => (False.elim (u40 q0))) (fun r0 => r0));
    let u42 : p4789 := (Or.elim h7812 (fun q0 => (False.elim (q0 u41))) (fun r0 => r0));
    let u43 : p2750 := (Or.elim h3623 (fun q0 => (False.elim (q0 u37))) (fun r0 => r0));
    let u44 : (¬ p2440) := (Or.elim h9451 (fun q0 => q0) (fun r0 => (False.elim (r0 u24))));
    let u45 : (¬ p4699) := (Or.elim h7584 (fun q0 => (False.elim (u44 q0))) (fun r0 => r0));
    let u46 : p4703 := (Or.elim h66367 (fun q0 => q0) (fun r0 => (False.elim (u45 r0))));
    let u47 : p4241 := (Or.elim h7588 (fun q0 => q0) (fun r0 => (False.elim (r0 u46))));
    let u48 : (¬ p2427) := (Or.elim h24547 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u47))) (fun r1 => (False.elim (r1 u26))))));
    let u49 : (¬ p4645) := (Or.elim h7435 (fun q0 => (False.elim (u48 q0))) (fun r0 => r0));
    let u50 : p4643 := (Or.elim h66355 (fun q0 => q0) (fun r0 => (False.elim (u49 r0))));
    let u51 : p4001 := (Or.elim h7428 (fun q0 => q0) (fun r0 => (False.elim (r0 u50))));
    let u52 : (¬ p2911) := (Or.elim h20262 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u18))) (fun r1 => (False.elim (r1 u51))))));
    let u53 : (¬ p4923) := (Or.elim h8144 (fun q0 => (False.elim (u52 q0))) (fun r0 => r0));
    let u54 : p4921 := (Or.elim h66404 (fun q0 => (False.elim (u53 q0))) (fun r0 => r0));
    let u55 : p4383 := (Or.elim h8137 (fun q0 => q0) (fun r0 => (False.elim (r0 u54))));
    let u56 : (¬ p5558) := (Or.elim h63098 (fun q0 => (False.elim (q0 u25))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u18))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u26))) (fun r2 => r2))))));
    let u57 : (¬ p5555) := (Or.elim h9721 (fun q0 => q0) (fun r0 => (False.elim (u56 r0))));
    let u58 : p5561 := (Or.elim h66484 (fun q0 => (False.elim (u57 q0))) (fun r0 => r0));
    let u59 : p5564 := (Or.elim h9728 (fun q0 => (False.elim (q0 u58))) (fun r0 => r0));
    let u60 : p3644 := (Or.elim h5947 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u51))))));
    let u61 : p2753 := (Or.elim h7680 (fun q0 => q0) (fun r0 => (False.elim (r0 u22))));
    let u62 : p3413 := (Or.elim h7589 (fun q0 => q0) (fun r0 => (False.elim (r0 u46))));
    let u63 : (¬ p2651) := (Or.elim h14339 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u25))) (fun r1 => (False.elim (r1 u62))))));
    let u64 : (¬ p2661) := (Or.elim h3449 (fun q0 => (False.elim (u63 q0))) (fun r0 => r0));
    let u65 : p2654 := (Or.elim h66378 (fun q0 => q0) (fun r0 => (False.elim (u64 r0))));
    let u66 : p2655 := (Or.elim h3433 (fun q0 => (False.elim (q0 u65))) (fun r0 => r0));
    let u67 : p2441 := (Or.elim h7427 (fun q0 => q0) (fun r0 => (False.elim (r0 u50))));
    let u68 : p4235 := (Or.elim h26527 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u47))) (fun r1 => (False.elim (r1 u26))))));
    let u69 : p4079 := (Or.elim h8804 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u70 : p3379 := (Or.elim h8805 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u71 : (¬ p4688) := (Or.elim h20283 (fun q0 => (False.elim (q0 u70))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => r1))));
    let u72 : (¬ p4686) := (Or.elim h7555 (fun q0 => q0) (fun r0 => (False.elim (u71 r0))));
    let u73 : p4683 := (Or.elim h66365 (fun q0 => q0) (fun r0 => (False.elim (u72 r0))));
    let u74 : p4370 := (Or.elim h7549 (fun q0 => q0) (fun r0 => (False.elim (r0 u73))));
    let u75 : (¬ p2406) := (Or.elim h42186 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u70))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u74))) (fun r3 => (False.elim (r3 u27))))))))));
    let u76 : (¬ p3083) := (Or.elim h42261 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u70))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u74))) (fun r3 => (False.elim (r3 u16))))))))));
    let u77 : (¬ p4630) := (Or.elim h7401 (fun q0 => (False.elim (u75 q0))) (fun r0 => r0));
    let u78 : (¬ p5010) := (Or.elim h8375 (fun q0 => (False.elim (u76 q0))) (fun r0 => r0));
    let u79 : p4627 := (Or.elim h66353 (fun q0 => q0) (fun r0 => (False.elim (u77 r0))));
    let u80 : p5007 := (Or.elim h66422 (fun q0 => q0) (fun r0 => (False.elim (u78 r0))));
    let u81 : p3238 := (Or.elim h7395 (fun q0 => q0) (fun r0 => (False.elim (r0 u79))));
    let u82 : p4256 := (Or.elim h8369 (fun q0 => q0) (fun r0 => (False.elim (r0 u80))));
    let u83 : (¬ p2922) := (Or.elim h4598 (fun q0 => (False.elim (q0 u67))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u81))))));
    let u84 : (¬ p3222) := (Or.elim h4597 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u81))))));
    let u85 : (¬ p2230) := (Or.elim h49291 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u81))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u34))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u69))) (fun r3 => (False.elim (r3 u11))))))))));
    let u86 : (¬ p2932) := (Or.elim h3992 (fun q0 => (False.elim (u83 q0))) (fun r0 => r0));
    let u87 : (¬ p3231) := (Or.elim h4585 (fun q0 => (False.elim (u84 q0))) (fun r0 => r0));
    let u88 : (¬ p4537) := (Or.elim h7148 (fun q0 => (False.elim (u85 q0))) (fun r0 => r0));
    let u89 : p2925 := (Or.elim h66405 (fun q0 => (False.elim (u86 q0))) (fun r0 => r0));
    let u90 : p3225 := (Or.elim h66433 (fun q0 => q0) (fun r0 => (False.elim (u87 r0))));
    let u91 : p4535 := (Or.elim h66335 (fun q0 => q0) (fun r0 => (False.elim (u88 r0))));
    let u92 : p2927 := (Or.elim h3977 (fun q0 => (False.elim (q0 u89))) (fun r0 => r0));
    let u93 : p3227 := (Or.elim h4570 (fun q0 => (False.elim (q0 u90))) (fun r0 => r0));
    let u94 : p2589 := (Or.elim h7142 (fun q0 => q0) (fun r0 => (False.elim (r0 u91))));
    let u95 : (¬ p3742) := (Or.elim h53117 (fun q0 => (False.elim (q0 u24))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u94))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u60))) (fun r2 => r2))))));
    let u96 : (¬ p4322) := (Or.elim h44001 (fun q0 => (False.elim (q0 u94))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u32))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u68))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u7))))))))));
    let u97 : (¬ p4432) := (Or.elim h57164 (fun q0 => (False.elim (q0 u23))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u24))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u94))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u66))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u82))) (fun r4 => r4))))))))));
    let u98 : (¬ p4649) := (Or.elim h7447 (fun q0 => (False.elim (u95 q0))) (fun r0 => r0));
    let u99 : (¬ p5396) := (Or.elim h9308 (fun q0 => (False.elim (u96 q0))) (fun r0 => r0));
    let u100 : (¬ p4594) := (Or.elim h7308 (fun q0 => (False.elim (u97 q0))) (fun r0 => r0));
    let u101 : p4651 := (Or.elim h66356 (fun q0 => q0) (fun r0 => (False.elim (u98 r0))));
    let u102 : p5401 := (Or.elim h66468 (fun q0 => (False.elim (u99 q0))) (fun r0 => r0));
    let u103 : p4597 := (Or.elim h66348 (fun q0 => q0) (fun r0 => (False.elim (u100 r0))));
    let u104 : p2437 := (Or.elim h7453 (fun q0 => q0) (fun r0 => (False.elim (r0 u101))));
    let u105 : p3680 := (Or.elim h9314 (fun q0 => q0) (fun r0 => (False.elim (r0 u102))));
    let u106 : p2352 := (Or.elim h7315 (fun q0 => q0) (fun r0 => (False.elim (r0 u103))));
    let u107 : (¬ p4366) := (Or.elim h41590 (fun q0 => (False.elim (q0 u104))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u92))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u70))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u16))))))))));
    let u108 : (¬ p3868) := (Or.elim h42265 (fun q0 => (False.elim (q0 u104))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u82))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u55))) (fun r3 => (False.elim (r3 u59))))))))));
    let u109 : (¬ p5205) := (Or.elim h8833 (fun q0 => (False.elim (u107 q0))) (fun r0 => r0));
    let u110 : (¬ p5506) := (Or.elim h9589 (fun q0 => (False.elim (u108 q0))) (fun r0 => r0));
    let u111 : p5209 := (Or.elim h66447 (fun q0 => q0) (fun r0 => (False.elim (u109 r0))));
    let u112 : p5500 := (Or.elim h66479 (fun q0 => q0) (fun r0 => (False.elim (u110 r0))));
    let u113 : p3399 := (Or.elim h8839 (fun q0 => q0) (fun r0 => (False.elim (r0 u111))));
    let u114 : p5503 := (Or.elim h9583 (fun q0 => (False.elim (q0 u112))) (fun r0 => r0));
    let u115 : (¬ p4129) := (Or.elim h43991 (fun q0 => (False.elim (q0 u67))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u94))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u114))))))))));
    let u116 : (¬ p5663) := (Or.elim h10125 (fun q0 => (False.elim (u115 q0))) (fun r0 => r0));
    let u117 : p5659 := (Or.elim h66493 (fun q0 => q0) (fun r0 => (False.elim (u116 r0))));
    let u118 : p5660 := (Or.elim h10119 (fun q0 => (False.elim (q0 u117))) (fun r0 => r0));
    let u119 : (¬ p3266) := (Or.elim h55859 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u94))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u68))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u31))) (fun r6 => (False.elim (r6 u118))))))))))))))));
    let u120 : (¬ p5120) := (Or.elim h8652 (fun q0 => (False.elim (u119 q0))) (fun r0 => r0));
    let u121 : p5115 := (Or.elim h66438 (fun q0 => q0) (fun r0 => (False.elim (u120 r0))));
    let u122 : p4444 := (Or.elim h8646 (fun q0 => q0) (fun r0 => (False.elim (r0 u121))));
    let u123 : (¬ p2387) := (Or.elim h66678 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u106))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u70))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u15))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u17))) (fun r6 => (False.elim (r6 u23))))))))))))))));
    let u124 : (¬ p4612) := (Or.elim h7361 (fun q0 => (False.elim (u123 q0))) (fun r0 => r0));
    let u125 : p4615 := (Or.elim h66351 (fun q0 => q0) (fun r0 => (False.elim (u124 r0))));
    let u126 : p2383 := (Or.elim h7367 (fun q0 => q0) (fun r0 => (False.elim (r0 u125))));
    let u127 : (¬ p3483) := (Or.elim h57165 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u126))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u43))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u61))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u25))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u26))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (False.elim (r9 u8))))))))))))))))))))));
    let u128 : p3654 := (Or.elim h6818 (fun q0 => (False.elim (q0 u126))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u20))))));
    let u129 : (¬ p5268) := (Or.elim h8968 (fun q0 => (False.elim (u127 q0))) (fun r0 => r0));
    let u130 : p5263 := (Or.elim h66454 (fun q0 => q0) (fun r0 => (False.elim (u129 r0))));
    let u131 : p3917 := (Or.elim h8962 (fun q0 => q0) (fun r0 => (False.elim (r0 u130))));
    let u132 : (¬ p4996) := (Or.elim h66679 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u131))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u128))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u122))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u113))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u105))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u94))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u93))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u70))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u5))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u12))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u42))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u16))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u19))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u20))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u21))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u66))) (fun r17 => (False.elim (r17 u24))))))))))))))))))))))))))))))))))))));
    let u133 : p4992 := (Or.elim h66420 (fun q0 => q0) (fun r0 => (False.elim (u132 r0))));
    let u134 : p4993 := (Or.elim h8333 (fun q0 => (False.elim (q0 u133))) (fun r0 => r0));
    let u135 : p3923 := (Or.elim h8334 (fun q0 => q0) (fun r0 => (False.elim (r0 u133))));
    let u136 : (¬ p3093) := (Or.elim h54781 (fun q0 => (False.elim (q0 u23))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u15))) (fun r3 => (False.elim (r3 u134))))))))));
    let u137 : (¬ p5016) := (Or.elim h19898 (fun q0 => (False.elim (q0 u126))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u135))) (fun r1 => r1))));
    let u138 : (¬ p5019) := (Or.elim h8392 (fun q0 => (False.elim (u136 q0))) (fun r0 => r0));
    let u139 : (¬ p5014) := (Or.elim h8385 (fun q0 => q0) (fun r0 => (False.elim (u137 r0))));
    (Or.elim h66423 (fun q0 => (False.elim (u138 q0))) (fun r0 => (False.elim (u139 r0)))))

theorem step66681 (p2307 p2310 p2313 p2317 p2383 p3093 p3309 p3549 p3860 p3923 p3955 p4500 p4501 p4992 p4993 p4994 p5014 p5016 p5019 p5020 p5140 p5143 : Prop)
    (h8334 : p3923 ∨ (¬ p4992))
    (h19898 : (¬ p2383) ∨ (¬ p3923) ∨ (¬ p5016))
    (h8385 : (¬ p5014) ∨ p5016)
    (h66423 : p5019 ∨ p5014)
    (h8392 : p3093 ∨ (¬ p5019))
    (h8391 : (¬ p5019) ∨ p5020)
    (h8335 : (¬ p4992) ∨ p4994)
    (h8333 : (¬ p4992) ∨ p4993)
    (h7054 : p3955 ∨ (¬ p4500))
    (h7057 : (¬ p4500) ∨ p4501)
    (h19973 : (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3955))
    (h51073 : (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3860) ∨ (¬ p4501) ∨ (¬ p4993))
    (h2756 : (¬ p2310) ∨ p2313)
    (h8711 : p3309 ∨ (¬ p5143))
    (h66343 : p2317 ∨ p2310)
    (h66440 : p5140 ∨ p5143)
    (h2770 : p2307 ∨ (¬ p2317))
    (h8705 : p3549 ∨ (¬ p5140))
    (h61066 : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3860) ∨ (¬ p4994) ∨ (¬ p5020))
    : (¬ p4500) ∨ (¬ p4992) ∨ (¬ p2383) ∨ (¬ p3860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4500 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3923 := (Or.elim h8334 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u5 : (¬ p5016) := (Or.elim h19898 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => r1))));
    let u6 : (¬ p5014) := (Or.elim h8385 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u7 : p5019 := (Or.elim h66423 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u8 : p3093 := (Or.elim h8392 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u9 : p5020 := (Or.elim h8391 (fun q0 => (False.elim (q0 u7))) (fun r0 => r0));
    let u10 : p4994 := (Or.elim h8335 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u11 : p4993 := (Or.elim h8333 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u12 : p3955 := (Or.elim h7054 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u13 : p4501 := (Or.elim h7057 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u14 : (¬ p2313) := (Or.elim h19973 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u12))))));
    let u15 : (¬ p3309) := (Or.elim h51073 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (False.elim (r3 u11))))))))));
    let u16 : (¬ p2310) := (Or.elim h2756 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    let u17 : (¬ p5143) := (Or.elim h8711 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u18 : p2317 := (Or.elim h66343 (fun q0 => q0) (fun r0 => (False.elim (u16 r0))));
    let u19 : p5140 := (Or.elim h66440 (fun q0 => q0) (fun r0 => (False.elim (u17 r0))));
    let u20 : p2307 := (Or.elim h2770 (fun q0 => q0) (fun r0 => (False.elim (r0 u18))));
    let u21 : p3549 := (Or.elim h8705 (fun q0 => q0) (fun r0 => (False.elim (r0 u19))));
    (Or.elim h61066 (fun q0 => (False.elim (q0 u20))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u21))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (False.elim (r3 u9)))))))))))

theorem step66682 (p2383 p2493 p2496 p2497 p2503 p2608 p2829 p3093 p3452 p3541 p3584 p3590 p3923 p3954 p4732 p4735 p4868 p4870 p5014 p5016 p5019 p5020 p5213 p5215 p5219 p5223 p5224 : Prop)
    (h19898 : (¬ p2383) ∨ (¬ p3923) ∨ (¬ p5016))
    (h8385 : (¬ p5014) ∨ p5016)
    (h66423 : p5019 ∨ p5014)
    (h8392 : p3093 ∨ (¬ p5019))
    (h6132 : (¬ p2497) ∨ (¬ p3093) ∨ (¬ p3452))
    (h3125 : (¬ p2496) ∨ p2497)
    (h66362 : p2496 ∨ p2503)
    (h3141 : p2493 ∨ (¬ p2503))
    (h8391 : (¬ p5019) ∨ p5020)
    (h8006 : p2829 ∨ (¬ p4868))
    (h8007 : (¬ p4868) ∨ p4870)
    (h42586 : (¬ p2383) ∨ (¬ p3923) ∨ (¬ p3954) ∨ (¬ p4870) ∨ (¬ p5020))
    (h7681 : p3954 ∨ (¬ p4732))
    (h66374 : p4732 ∨ p4735)
    (h7687 : p2608 ∨ (¬ p4735))
    (h5163 : (¬ p2608) ∨ (¬ p3452) ∨ (¬ p3541))
    (h8858 : p3541 ∨ (¬ p5215))
    (h66448 : p5215 ∨ p5213)
    (h8852 : p3590 ∨ (¬ p5213))
    (h51425 : (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p5224))
    (h19922 : (¬ p2493) ∨ (¬ p3584) ∨ (¬ p3590))
    (h8880 : (¬ p5223) ∨ p5224)
    (h8873 : p3584 ∨ (¬ p5219))
    (h66449 : p5219 ∨ p5223)
    : (¬ p4868) ∨ (¬ p3452) ∨ (¬ p3923) ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5016) := (Or.elim h19898 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    let u5 : (¬ p5014) := (Or.elim h8385 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u6 : p5019 := (Or.elim h66423 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u7 : p3093 := (Or.elim h8392 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u8 : (¬ p2497) := (Or.elim h6132 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (False.elim (r1 u1))))));
    let u9 : (¬ p2496) := (Or.elim h3125 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u10 : p2503 := (Or.elim h66362 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u11 : p2493 := (Or.elim h3141 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    let u12 : p5020 := (Or.elim h8391 (fun q0 => (False.elim (q0 u6))) (fun r0 => r0));
    let u13 : p2829 := (Or.elim h8006 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u14 : p4870 := (Or.elim h8007 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u15 : (¬ p3954) := (Or.elim h42586 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (False.elim (r3 u12))))))))));
    let u16 : (¬ p4732) := (Or.elim h7681 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u17 : p4735 := (Or.elim h66374 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    let u18 : p2608 := (Or.elim h7687 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    let u19 : (¬ p3541) := (Or.elim h5163 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    let u20 : (¬ p5215) := (Or.elim h8858 (fun q0 => (False.elim (u19 q0))) (fun r0 => r0));
    let u21 : p5213 := (Or.elim h66448 (fun q0 => (False.elim (u20 q0))) (fun r0 => r0));
    let u22 : p3590 := (Or.elim h8852 (fun q0 => q0) (fun r0 => (False.elim (r0 u21))));
    let u23 : (¬ p5224) := (Or.elim h51425 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u22))) (fun r3 => r3))))))));
    let u24 : (¬ p3584) := (Or.elim h19922 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u22))))));
    let u25 : (¬ p5223) := (Or.elim h8880 (fun q0 => q0) (fun r0 => (False.elim (u23 r0))));
    let u26 : (¬ p5219) := (Or.elim h8873 (fun q0 => (False.elim (u24 q0))) (fun r0 => r0));
    (Or.elim h66449 (fun q0 => (False.elim (u26 q0))) (fun r0 => (False.elim (u25 r0)))))

theorem step66683 (p2383 p2608 p3093 p3452 p3541 p3923 p3953 p3954 p4376 p4732 p4735 p4865 p4868 p5014 p5016 p5019 p5020 p5213 p5215 : Prop)
    (h19898 : (¬ p2383) ∨ (¬ p3923) ∨ (¬ p5016))
    (h8385 : (¬ p5014) ∨ p5016)
    (h66423 : p5019 ∨ p5014)
    (h8392 : p3093 ∨ (¬ p5019))
    (h8391 : (¬ p5019) ∨ p5020)
    (h66682 : (¬ p4868) ∨ (¬ p3452) ∨ (¬ p3923) ∨ (¬ p2383))
    (h66396 : p4865 ∨ p4868)
    (h7998 : p3953 ∨ (¬ p4865))
    (h5866 : (¬ p3093) ∨ (¬ p3953) ∨ (¬ p3954))
    (h42594 : (¬ p2383) ∨ (¬ p3452) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p4376) ∨ (¬ p5020))
    (h7681 : p3954 ∨ (¬ p4732))
    (h8854 : p4376 ∨ (¬ p5213))
    (h66374 : p4732 ∨ p4735)
    (h66448 : p5215 ∨ p5213)
    (h7687 : p2608 ∨ (¬ p4735))
    (h8858 : p3541 ∨ (¬ p5215))
    (h5163 : (¬ p2608) ∨ (¬ p3452) ∨ (¬ p3541))
    : (¬ p3452) ∨ (¬ p3923) ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3452 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5016) := (Or.elim h19898 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    let u4 : (¬ p5014) := (Or.elim h8385 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u5 : p5019 := (Or.elim h66423 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u6 : p3093 := (Or.elim h8392 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u7 : p5020 := (Or.elim h8391 (fun q0 => (False.elim (q0 u5))) (fun r0 => r0));
    let u8 : (¬ p4868) := (Or.elim h66682 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    let u9 : p4865 := (Or.elim h66396 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u10 : p3953 := (Or.elim h7998 (fun q0 => q0) (fun r0 => (False.elim (r0 u9))));
    let u11 : (¬ p3954) := (Or.elim h5866 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => r1))));
    let u12 : (¬ p4376) := (Or.elim h42594 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u7))))))))))));
    let u13 : (¬ p4732) := (Or.elim h7681 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    let u14 : (¬ p5213) := (Or.elim h8854 (fun q0 => (False.elim (u12 q0))) (fun r0 => r0));
    let u15 : p4735 := (Or.elim h66374 (fun q0 => (False.elim (u13 q0))) (fun r0 => r0));
    let u16 : p5215 := (Or.elim h66448 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    let u17 : p2608 := (Or.elim h7687 (fun q0 => q0) (fun r0 => (False.elim (r0 u15))));
    let u18 : p3541 := (Or.elim h8858 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    (Or.elim h5163 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u18)))))))

theorem step66684 (p2352 p2383 p2573 p2576 p2578 p2583 p2819 p3055 p3093 p3366 p3367 p3688 p3923 p3953 p3954 p4342 p4358 p4375 p4726 p4728 p4730 p4732 p4735 p4856 p4860 p4865 p5014 p5016 p5019 p5219 p5221 p5223 : Prop)
    (h19898 : (¬ p2383) ∨ (¬ p3923) ∨ (¬ p5016))
    (h8385 : (¬ p5014) ∨ p5016)
    (h66423 : p5019 ∨ p5014)
    (h8392 : p3093 ∨ (¬ p5019))
    (h7998 : p3953 ∨ (¬ p4865))
    (h5866 : (¬ p3093) ∨ (¬ p3953) ∨ (¬ p3954))
    (h7681 : p3954 ∨ (¬ p4732))
    (h66374 : p4732 ∨ p4735)
    (h7685 : p3366 ∨ (¬ p4735))
    (h8000 : p3688 ∨ (¬ p4865))
    (h4835 : (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3367))
    (h23622 : (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4375))
    (h7664 : p3055 ∨ (¬ p4726))
    (h8878 : p4375 ∨ (¬ p5223))
    (h66373 : p4728 ∨ p4726)
    (h66449 : p5219 ∨ p5223)
    (h7672 : (¬ p4728) ∨ p4730)
    (h8872 : p4342 ∨ (¬ p5219))
    (h8874 : (¬ p5219) ∨ p5221)
    (h41027 : (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4730))
    (h41149 : (¬ p2819) ∨ (¬ p3367) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p5221))
    (h3293 : p2573 ∨ (¬ p2583))
    (h7989 : p2819 ∨ (¬ p4860))
    (h66370 : p2576 ∨ p2583)
    (h66395 : p4856 ∨ p4860)
    (h3278 : (¬ p2576) ∨ p2578)
    (h7983 : p4358 ∨ (¬ p4856))
    (h29119 : p2352 ∨ (¬ p2383) ∨ (¬ p2578))
    (h43129 : (¬ p2352) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4358))
    : (¬ p3367) ∨ (¬ p4865) ∨ (¬ p3923) ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4865 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5016) := (Or.elim h19898 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    let u5 : (¬ p5014) := (Or.elim h8385 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u6 : p5019 := (Or.elim h66423 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u7 : p3093 := (Or.elim h8392 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u8 : p3953 := (Or.elim h7998 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u9 : (¬ p3954) := (Or.elim h5866 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => r1))));
    let u10 : (¬ p4732) := (Or.elim h7681 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u11 : p4735 := (Or.elim h66374 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u12 : p3366 := (Or.elim h7685 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    let u13 : p3688 := (Or.elim h8000 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u14 : (¬ p3055) := (Or.elim h4835 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (False.elim (r1 u0))))));
    let u15 : (¬ p4375) := (Or.elim h23622 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => r1))));
    let u16 : (¬ p4726) := (Or.elim h7664 (fun q0 => (False.elim (u14 q0))) (fun r0 => r0));
    let u17 : (¬ p5223) := (Or.elim h8878 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u18 : p4728 := (Or.elim h66373 (fun q0 => q0) (fun r0 => (False.elim (u16 r0))));
    let u19 : p5219 := (Or.elim h66449 (fun q0 => q0) (fun r0 => (False.elim (u17 r0))));
    let u20 : p4730 := (Or.elim h7672 (fun q0 => (False.elim (q0 u18))) (fun r0 => r0));
    let u21 : p4342 := (Or.elim h8872 (fun q0 => q0) (fun r0 => (False.elim (r0 u19))));
    let u22 : p5221 := (Or.elim h8874 (fun q0 => (False.elim (q0 u19))) (fun r0 => r0));
    let u23 : (¬ p2573) := (Or.elim h41027 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u21))) (fun r3 => (False.elim (r3 u20))))))))));
    let u24 : (¬ p2819) := (Or.elim h41149 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u22))))))))));
    let u25 : (¬ p2583) := (Or.elim h3293 (fun q0 => (False.elim (u23 q0))) (fun r0 => r0));
    let u26 : (¬ p4860) := (Or.elim h7989 (fun q0 => (False.elim (u24 q0))) (fun r0 => r0));
    let u27 : p2576 := (Or.elim h66370 (fun q0 => q0) (fun r0 => (False.elim (u25 r0))));
    let u28 : p4856 := (Or.elim h66395 (fun q0 => q0) (fun r0 => (False.elim (u26 r0))));
    let u29 : p2578 := (Or.elim h3278 (fun q0 => (False.elim (q0 u27))) (fun r0 => r0));
    let u30 : p4358 := (Or.elim h7983 (fun q0 => q0) (fun r0 => (False.elim (r0 u28))));
    let u31 : p2352 := (Or.elim h29119 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u29))))));
    (Or.elim h43129 (fun q0 => (False.elim (q0 u31))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (False.elim (r2 u30)))))))))

theorem step66687 (p2839 p3054 p3583 p3585 p3695 p3874 p4608 p4873 p4876 p4880 p4883 : Prop)
    (h8017 : p3583 ∨ (¬ p4873))
    (h37227 : (¬ p3054) ∨ p3583 ∨ (¬ p3585))
    (h66397 : p4873 ∨ p4876)
    (h8032 : p3054 ∨ (¬ p4880))
    (h8023 : p2839 ∨ (¬ p4876))
    (h66398 : p4880 ∨ p4883)
    (h52514 : (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3695) ∨ (¬ p3874) ∨ (¬ p4608))
    (h8038 : p3695 ∨ (¬ p4883))
    : p3583 ∨ (¬ p4608) ∨ (¬ p3874) ∨ (¬ p3585) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3583) := (fun h => hn (Or.inl h));
    let u1 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4873) := (Or.elim h8017 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u5 : (¬ p3054) := (Or.elim h37227 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u3))))));
    let u6 : p4876 := (Or.elim h66397 (fun q0 => (False.elim (u4 q0))) (fun r0 => r0));
    let u7 : (¬ p4880) := (Or.elim h8032 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    let u8 : p2839 := (Or.elim h8023 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u9 : p4883 := (Or.elim h66398 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u10 : (¬ p3695) := (Or.elim h52514 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h8038 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u9)))))

theorem step66698 (p2387 p2608 p2774 p2777 p2779 p2784 p3063 p3589 p3591 p3918 p4358 p4866 p5014 p5015 : Prop)
    (h8384 : (¬ p5014) ∨ p5015)
    (h8386 : p3591 ∨ (¬ p5014))
    (h48555 : (¬ p2387) ∨ (¬ p2608) ∨ (¬ p3063) ∨ (¬ p4866) ∨ (¬ p5015))
    (h32770 : (¬ p2774) ∨ (¬ p3589) ∨ (¬ p3591) ∨ (¬ p3918))
    (h19665 : p2387 ∨ (¬ p2779) ∨ (¬ p4358))
    (h3697 : p2774 ∨ (¬ p2784))
    (h3682 : (¬ p2777) ∨ p2779)
    (h66391 : p2784 ∨ p2777)
    : (¬ p5014) ∨ (¬ p3063) ∨ (¬ p2608) ∨ (¬ p3589) ∨ (¬ p4866) ∨ (¬ p3918) ∨ (¬ p4358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5014 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5015 := (Or.elim h8384 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u8 : p3591 := (Or.elim h8386 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u9 : (¬ p2387) := (Or.elim h48555 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u7))))))))));
    let u10 : (¬ p2774) := (Or.elim h32770 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (False.elim (r2 u5))))))));
    let u11 : (¬ p2779) := (Or.elim h19665 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u6))))));
    let u12 : (¬ p2784) := (Or.elim h3697 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : (¬ p2777) := (Or.elim h3682 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h66391 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u13 r0)))))

theorem step66699 (p2352 p2383 p2440 p2573 p2576 p2578 p2579 p2583 p2584 p2590 p2654 p2656 p2661 p2665 p3125 p3322 p3564 p3574 p3956 p4203 p4594 p4597 p4714 p4716 : Prop)
    (h7315 : p2352 ∨ (¬ p4597))
    (h29119 : p2352 ∨ (¬ p2383) ∨ (¬ p2578))
    (h27945 : p2352 ∨ (¬ p3322) ∨ (¬ p3564))
    (h66348 : p4597 ∨ p4594)
    (h3278 : (¬ p2576) ∨ p2578)
    (h6764 : (¬ p3125) ∨ p3564 ∨ (¬ p4203))
    (h7309 : p3956 ∨ (¬ p4594))
    (h66370 : p2576 ∨ p2583)
    (h7622 : p4203 ∨ (¬ p4716))
    (h3292 : (¬ p2583) ∨ p2584)
    (h3293 : p2573 ∨ (¬ p2583))
    (h66369 : p4714 ∨ p4716)
    (h9992 : (¬ p2573) ∨ (¬ p2579))
    (h7616 : p2590 ∨ (¬ p4714))
    (h16654 : (¬ p2440) ∨ (¬ p2590) ∨ p3574)
    (h5860 : p2579 ∨ (¬ p2656) ∨ (¬ p3574))
    (h48290 : (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2665) ∨ (¬ p3574) ∨ (¬ p3956))
    (h3434 : (¬ p2654) ∨ p2656)
    (h3451 : (¬ p2661) ∨ p2665)
    (h66378 : p2654 ∨ p2661)
    : p2352 ∨ (¬ p2440) ∨ (¬ p3125) ∨ (¬ p3322) ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2352) := (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4597) := (Or.elim h7315 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u6 : (¬ p2578) := (Or.elim h29119 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => r1))));
    let u7 : (¬ p3564) := (Or.elim h27945 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => r1))));
    let u8 : p4594 := (Or.elim h66348 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    let u9 : (¬ p2576) := (Or.elim h3278 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : (¬ p4203) := (Or.elim h6764 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => r1))));
    let u11 : p3956 := (Or.elim h7309 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u12 : p2583 := (Or.elim h66370 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u13 : (¬ p4716) := (Or.elim h7622 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u14 : p2584 := (Or.elim h3292 (fun q0 => (False.elim (q0 u12))) (fun r0 => r0));
    let u15 : p2573 := (Or.elim h3293 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u16 : p4714 := (Or.elim h66369 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u17 : (¬ p2579) := (Or.elim h9992 (fun q0 => (False.elim (q0 u15))) (fun r0 => r0));
    let u18 : p2590 := (Or.elim h7616 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    let u19 : p3574 := (Or.elim h16654 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u18))) (fun r1 => r1))));
    let u20 : (¬ p2656) := (Or.elim h5860 (fun q0 => (False.elim (u17 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u19))))));
    let u21 : (¬ p2665) := (Or.elim h48290 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u19))) (fun r3 => (False.elim (r3 u11))))))))));
    let u22 : (¬ p2654) := (Or.elim h3434 (fun q0 => q0) (fun r0 => (False.elim (u20 r0))));
    let u23 : (¬ p2661) := (Or.elim h3451 (fun q0 => q0) (fun r0 => (False.elim (u21 r0))));
    (Or.elim h66378 (fun q0 => (False.elim (u22 q0))) (fun r0 => (False.elim (u23 r0)))))

theorem step66701 (p2132 p2230 p2437 p2542 p2589 p2753 p3362 p3363 p3367 p3389 p3540 p3574 p3583 p3585 p3683 p3684 p3698 p3742 p3876 p4535 p4537 p4649 p4651 p4732 p4735 p4737 p4748 p4750 p4751 p5196 p5200 p5213 p5215 : Prop)
    (h5390 : (¬ p2542) ∨ (¬ p3683) ∨ (¬ p3684))
    (h7719 : p3683 ∨ (¬ p4751))
    (h66376 : p4751 ∨ p4748)
    (h7717 : (¬ p4748) ∨ p4750)
    (h5391 : (¬ p2132) ∨ (¬ p2753) ∨ (¬ p3583))
    (h50540 : (¬ p2542) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4750))
    (h7680 : p2753 ∨ (¬ p4732))
    (h8859 : p3367 ∨ (¬ p5215))
    (h66374 : p4732 ∨ p4735)
    (h66448 : p5215 ∨ p5213)
    (h7689 : (¬ p4735) ∨ p4737)
    (h8853 : p3585 ∨ (¬ p5213))
    (h41001 : (¬ p2230) ∨ (¬ p3362) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p4737))
    (h49312 : (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3585) ∨ (¬ p3876) ∨ (¬ p4737))
    (h7148 : p2230 ∨ (¬ p4537))
    (h8822 : p3389 ∨ (¬ p5200))
    (h66335 : p4535 ∨ p4537)
    (h66446 : p5196 ∨ p5200)
    (h7142 : p2589 ∨ (¬ p4535))
    (h8816 : p3540 ∨ (¬ p5196))
    (h43004 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3742))
    (h46819 : (¬ p2437) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p3585))
    (h7447 : p3742 ∨ (¬ p4649))
    (h7453 : p2437 ∨ (¬ p4651))
    (h66356 : p4651 ∨ p4649)
    : (¬ p3583) ∨ (¬ p3876) ∨ (¬ p3574) ∨ (¬ p3684) ∨ (¬ p3698) ∨ (¬ p3362) ∨ (¬ p3363) ∨ (¬ p2132) ∨ (¬ p2542) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3583 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3683) := (Or.elim h5390 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u3))))));
    let u10 : (¬ p4751) := (Or.elim h7719 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u11 : p4748 := (Or.elim h66376 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u12 : p4750 := (Or.elim h7717 (fun q0 => (False.elim (q0 u11))) (fun r0 => r0));
    let u13 : (¬ p2753) := (Or.elim h5391 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u0))))));
    let u14 : (¬ p3367) := (Or.elim h50540 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u12))))))))));
    let u15 : (¬ p4732) := (Or.elim h7680 (fun q0 => (False.elim (u13 q0))) (fun r0 => r0));
    let u16 : (¬ p5215) := (Or.elim h8859 (fun q0 => (False.elim (u14 q0))) (fun r0 => r0));
    let u17 : p4735 := (Or.elim h66374 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u18 : p5213 := (Or.elim h66448 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    let u19 : p4737 := (Or.elim h7689 (fun q0 => (False.elim (q0 u17))) (fun r0 => r0));
    let u20 : p3585 := (Or.elim h8853 (fun q0 => q0) (fun r0 => (False.elim (r0 u18))));
    let u21 : (¬ p2230) := (Or.elim h41001 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u20))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u19))))))))));
    let u22 : (¬ p3389) := (Or.elim h49312 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u20))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u19))))))))));
    let u23 : (¬ p4537) := (Or.elim h7148 (fun q0 => (False.elim (u21 q0))) (fun r0 => r0));
    let u24 : (¬ p5200) := (Or.elim h8822 (fun q0 => (False.elim (u22 q0))) (fun r0 => r0));
    let u25 : p4535 := (Or.elim h66335 (fun q0 => q0) (fun r0 => (False.elim (u23 r0))));
    let u26 : p5196 := (Or.elim h66446 (fun q0 => q0) (fun r0 => (False.elim (u24 r0))));
    let u27 : p2589 := (Or.elim h7142 (fun q0 => q0) (fun r0 => (False.elim (r0 u25))));
    let u28 : p3540 := (Or.elim h8816 (fun q0 => q0) (fun r0 => (False.elim (r0 u26))));
    let u29 : (¬ p3742) := (Or.elim h43004 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u27))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u20))) (fun r3 => r3))))))));
    let u30 : (¬ p2437) := (Or.elim h46819 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u28))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u20))))))))));
    let u31 : (¬ p4649) := (Or.elim h7447 (fun q0 => (False.elim (u29 q0))) (fun r0 => r0));
    let u32 : (¬ p4651) := (Or.elim h7453 (fun q0 => (False.elim (u30 q0))) (fun r0 => r0));
    (Or.elim h66356 (fun q0 => (False.elim (u32 q0))) (fun r0 => (False.elim (u31 r0)))))

theorem step66703 (p2122 p2177 p2244 p2247 p2251 p2252 p2299 p2318 p2319 p2341 p2383 p2437 p2459 p2534 p2542 p2553 p2589 p2655 p2657 p2717 p2750 p2751 p2753 p2786 p2788 p2810 p2911 p2922 p2925 p2927 p2932 p3222 p3225 p3227 p3231 p3343 p3346 p3347 p3359 p3379 p3402 p3471 p3540 p3551 p3609 p3644 p3659 p3689 p3742 p3822 p3834 p3920 p4256 p4348 p4366 p4438 p4470 p4474 p4500 p4502 p4586 p4589 p4649 p4651 p4665 p4667 p4692 p4694 p4697 p4729 p4799 p4803 p4809 p4811 p4812 p4857 p4921 p4923 p5169 p5174 p5192 p5222 : Prop)
    (h9529 : (¬ p2122) ∨ (¬ p3822))
    (h6990 : p2122 ∨ (¬ p4474))
    (h66324 : p4474 ∨ p4470)
    (h6982 : p3689 ∨ (¬ p4470))
    (h46836 : (¬ p2534) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p4256))
    (h7567 : p2534 ∨ (¬ p4692))
    (h66366 : p4692 ∨ p4694)
    (h7575 : (¬ p4694) ∨ p4697)
    (h8803 : p3347 ∨ (¬ p5192))
    (h8805 : p3379 ∨ (¬ p5192))
    (h5162 : (¬ p2922) ∨ (¬ p3347) ∨ (¬ p3540))
    (h4809 : (¬ p3222) ∨ (¬ p3346) ∨ (¬ p3347))
    (h66648 : (¬ p4812) ∨ (¬ p2810) ∨ (¬ p2751) ∨ (¬ p2657) ∨ (¬ p3379))
    (h3992 : p2922 ∨ (¬ p2932))
    (h4585 : p3222 ∨ (¬ p3231))
    (h66386 : p4809 ∨ p4812)
    (h66405 : p2932 ∨ p2925)
    (h66433 : p3225 ∨ p3231)
    (h7855 : p3402 ∨ (¬ p4809))
    (h7859 : (¬ p4809) ∨ p4811)
    (h3977 : (¬ p2925) ∨ p2927)
    (h4570 : (¬ p3225) ∨ p3227)
    (h4899 : (¬ p2247) ∨ (¬ p3379) ∨ (¬ p3402))
    (h41590 : (¬ p2437) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p4811))
    (h42260 : (¬ p3227) ∨ (¬ p3343) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p4811))
    (h2625 : (¬ p2244) ∨ p2247)
    (h7453 : p2437 ∨ (¬ p4651))
    (h8765 : p3343 ∨ (¬ p5174))
    (h66336 : p2244 ∨ p2251)
    (h66356 : p4651 ∨ p4649)
    (h66443 : p5169 ∨ p5174)
    (h2637 : (¬ p2251) ∨ p2252)
    (h7447 : p3742 ∨ (¬ p4649))
    (h8759 : p3359 ∨ (¬ p5169))
    (h53117 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3644) ∨ (¬ p3742))
    (h8138 : p3644 ∨ (¬ p4921))
    (h66404 : p4923 ∨ p4921)
    (h8144 : p2911 ∨ (¬ p4923))
    (h8146 : p4438 ∨ (¬ p4923))
    (h42286 : (¬ p2318) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3822) ∨ (¬ p3920) ∨ (¬ p5222))
    (h61974 : (¬ p2252) ∨ (¬ p2383) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2786) ∨ (¬ p3609) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4857))
    (h7292 : p3551 ∨ (¬ p4586))
    (h7481 : p4348 ∨ (¬ p4665))
    (h66347 : p4589 ∨ p4586)
    (h66358 : p4665 ∨ p4667)
    (h7298 : p2341 ∨ (¬ p4589))
    (h7487 : p2459 ∨ (¬ p4667))
    (h40958 : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2788) ∨ (¬ p3822))
    (h50993 : (¬ p2459) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2717) ∨ (¬ p3359) ∨ (¬ p3471) ∨ (¬ p4697) ∨ (¬ p4729))
    (h7056 : p2299 ∨ (¬ p4500))
    (h7846 : p2717 ∨ (¬ p4803))
    (h66330 : p4502 ∨ p4500)
    (h66385 : p4803 ∨ p4799)
    (h7062 : p2177 ∨ (¬ p4502))
    (h7840 : p3659 ∨ (¬ p4799))
    (h53108 : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3659) ∨ (¬ p3689) ∨ (¬ p5222))
    : (¬ p5192) ∨ (¬ p3834) ∨ (¬ p3471) ∨ (¬ p4366) ∨ (¬ p3822) ∨ (¬ p2753) ∨ (¬ p3609) ∨ (¬ p4256) ∨ (¬ p3346) ∨ (¬ p3540) ∨ (¬ p2589) ∨ (¬ p2751) ∨ (¬ p2750) ∨ (¬ p2319) ∨ (¬ p2318) ∨ (¬ p2553) ∨ (¬ p3920) ∨ (¬ p2657) ∨ (¬ p2655) ∨ (¬ p2810) ∨ (¬ p4729) ∨ (¬ p5222) ∨ (¬ p2788) ∨ (¬ p2786) ∨ (¬ p4857) ∨ (¬ p2383) ∨ (¬ p2542) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p2788 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : p4857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))));
    let u25 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))));
    let u26 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))))))));
    let u27 : (¬ p2122) := (Or.elim h9529 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u28 : (¬ p4474) := (Or.elim h6990 (fun q0 => (False.elim (u27 q0))) (fun r0 => r0));
    let u29 : p4470 := (Or.elim h66324 (fun q0 => (False.elim (u28 q0))) (fun r0 => r0));
    let u30 : p3689 := (Or.elim h6982 (fun q0 => q0) (fun r0 => (False.elim (r0 u29))));
    let u31 : (¬ p2534) := (Or.elim h46836 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u26))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u18))) (fun r3 => (False.elim (r3 u7))))))))));
    let u32 : (¬ p4692) := (Or.elim h7567 (fun q0 => (False.elim (u31 q0))) (fun r0 => r0));
    let u33 : p4694 := (Or.elim h66366 (fun q0 => (False.elim (u32 q0))) (fun r0 => r0));
    let u34 : p4697 := (Or.elim h7575 (fun q0 => (False.elim (q0 u33))) (fun r0 => r0));
    let u35 : p3347 := (Or.elim h8803 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u36 : p3379 := (Or.elim h8805 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u37 : (¬ p2922) := (Or.elim h5162 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u35))) (fun r1 => (False.elim (r1 u9))))));
    let u38 : (¬ p3222) := (Or.elim h4809 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (False.elim (r1 u35))))));
    let u39 : (¬ p4812) := (Or.elim h66648 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u19))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u17))) (fun r3 => (False.elim (r3 u36))))))))));
    let u40 : (¬ p2932) := (Or.elim h3992 (fun q0 => (False.elim (u37 q0))) (fun r0 => r0));
    let u41 : (¬ p3231) := (Or.elim h4585 (fun q0 => (False.elim (u38 q0))) (fun r0 => r0));
    let u42 : p4809 := (Or.elim h66386 (fun q0 => q0) (fun r0 => (False.elim (u39 r0))));
    let u43 : p2925 := (Or.elim h66405 (fun q0 => (False.elim (u40 q0))) (fun r0 => r0));
    let u44 : p3225 := (Or.elim h66433 (fun q0 => q0) (fun r0 => (False.elim (u41 r0))));
    let u45 : p3402 := (Or.elim h7855 (fun q0 => q0) (fun r0 => (False.elim (r0 u42))));
    let u46 : p4811 := (Or.elim h7859 (fun q0 => (False.elim (q0 u42))) (fun r0 => r0));
    let u47 : p2927 := (Or.elim h3977 (fun q0 => (False.elim (q0 u43))) (fun r0 => r0));
    let u48 : p3227 := (Or.elim h4570 (fun q0 => (False.elim (q0 u44))) (fun r0 => r0));
    let u49 : (¬ p2247) := (Or.elim h4899 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u36))) (fun r1 => (False.elim (r1 u45))))));
    let u50 : (¬ p2437) := (Or.elim h41590 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u47))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u36))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u46))))))))));
    let u51 : (¬ p3343) := (Or.elim h42260 (fun q0 => (False.elim (q0 u48))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u36))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u46))))))))));
    let u52 : (¬ p2244) := (Or.elim h2625 (fun q0 => q0) (fun r0 => (False.elim (u49 r0))));
    let u53 : (¬ p4651) := (Or.elim h7453 (fun q0 => (False.elim (u50 q0))) (fun r0 => r0));
    let u54 : (¬ p5174) := (Or.elim h8765 (fun q0 => (False.elim (u51 q0))) (fun r0 => r0));
    let u55 : p2251 := (Or.elim h66336 (fun q0 => (False.elim (u52 q0))) (fun r0 => r0));
    let u56 : p4649 := (Or.elim h66356 (fun q0 => (False.elim (u53 q0))) (fun r0 => r0));
    let u57 : p5169 := (Or.elim h66443 (fun q0 => q0) (fun r0 => (False.elim (u54 r0))));
    let u58 : p2252 := (Or.elim h2637 (fun q0 => (False.elim (q0 u55))) (fun r0 => r0));
    let u59 : p3742 := (Or.elim h7447 (fun q0 => q0) (fun r0 => (False.elim (r0 u56))));
    let u60 : p3359 := (Or.elim h8759 (fun q0 => q0) (fun r0 => (False.elim (r0 u57))));
    let u61 : (¬ p3644) := (Or.elim h53117 (fun q0 => (False.elim (q0 u26))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u59))))))));
    let u62 : (¬ p4921) := (Or.elim h8138 (fun q0 => (False.elim (u61 q0))) (fun r0 => r0));
    let u63 : p4923 := (Or.elim h66404 (fun q0 => q0) (fun r0 => (False.elim (u62 r0))));
    let u64 : p2911 := (Or.elim h8144 (fun q0 => q0) (fun r0 => (False.elim (r0 u63))));
    let u65 : p4438 := (Or.elim h8146 (fun q0 => q0) (fun r0 => (False.elim (r0 u63))));
    let u66 : (¬ p3551) := (Or.elim h42286 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u64))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u16))) (fun r4 => (False.elim (r4 u21))))))))))));
    let u67 : (¬ p4348) := (Or.elim h61974 (fun q0 => (False.elim (q0 u58))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u25))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u26))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u18))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u23))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (Or.elim r9 (fun q10 => q10) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u65))) (fun r11 => (False.elim (r11 u24))))))))))))))))))))))))));
    let u68 : (¬ p4586) := (Or.elim h7292 (fun q0 => (False.elim (u66 q0))) (fun r0 => r0));
    let u69 : (¬ p4665) := (Or.elim h7481 (fun q0 => (False.elim (u67 q0))) (fun r0 => r0));
    let u70 : p4589 := (Or.elim h66347 (fun q0 => q0) (fun r0 => (False.elim (u68 r0))));
    let u71 : p4667 := (Or.elim h66358 (fun q0 => (False.elim (u69 q0))) (fun r0 => r0));
    let u72 : p2341 := (Or.elim h7298 (fun q0 => q0) (fun r0 => (False.elim (r0 u70))));
    let u73 : p2459 := (Or.elim h7487 (fun q0 => q0) (fun r0 => (False.elim (r0 u71))));
    let u74 : (¬ p2299) := (Or.elim h40958 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u72))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u22))) (fun r3 => (False.elim (r3 u4))))))))));
    let u75 : (¬ p2717) := (Or.elim h50993 (fun q0 => (False.elim (q0 u73))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u26))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u60))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u34))) (fun r6 => (False.elim (r6 u20))))))))))))))));
    let u76 : (¬ p4500) := (Or.elim h7056 (fun q0 => (False.elim (u74 q0))) (fun r0 => r0));
    let u77 : (¬ p4803) := (Or.elim h7846 (fun q0 => (False.elim (u75 q0))) (fun r0 => r0));
    let u78 : p4502 := (Or.elim h66330 (fun q0 => q0) (fun r0 => (False.elim (u76 r0))));
    let u79 : p4799 := (Or.elim h66385 (fun q0 => (False.elim (u77 q0))) (fun r0 => r0));
    let u80 : p2177 := (Or.elim h7062 (fun q0 => q0) (fun r0 => (False.elim (r0 u78))));
    let u81 : p3659 := (Or.elim h7840 (fun q0 => q0) (fun r0 => (False.elim (r0 u79))));
    (Or.elim h53108 (fun q0 => (False.elim (q0 u80))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u15))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u81))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u30))) (fun r3 => (False.elim (r3 u21)))))))))))

theorem step66705 (p2220 p2247 p2373 p2509 p2542 p2553 p2659 p2850 p2982 p3016 p3083 p3096 p3193 p3222 p3225 p3231 p3237 p3238 p3343 p3359 p3402 p3452 p3574 p3584 p3660 p3683 p3684 p3744 p3822 p3904 p3989 p4109 p4111 p4120 p4137 p4256 p4505 p4508 p4509 p4527 p4530 p4535 p4606 p4607 p4609 p4714 p4716 p4748 p4750 p4751 p4880 p4883 p4946 p4951 p4971 p4974 p5042 p5044 p5046 p5169 p5174 p5219 p5220 p5977 p5978 : Prop)
    (h8873 : p3584 ∨ (¬ p5219))
    (h8871 : (¬ p5219) ∨ p5220)
    (h7141 : p4109 ∨ (¬ p4535))
    (h7140 : p3904 ∨ (¬ p4535))
    (h48558 : (¬ p2542) ∨ (¬ p3238) ∨ (¬ p3359) ∨ (¬ p3452))
    (h44020 : (¬ p2850) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3584))
    (h8759 : p3359 ∨ (¬ p5169))
    (h8040 : p2850 ∨ (¬ p4883))
    (h66443 : p5169 ∨ p5174)
    (h66398 : p4880 ∨ p4883)
    (h8765 : p3343 ∨ (¬ p5174))
    (h8034 : p3684 ∨ (¬ p4880))
    (h5390 : (¬ p2542) ∨ (¬ p3683) ∨ (¬ p3684))
    (h7719 : p3683 ∨ (¬ p4751))
    (h66376 : p4751 ∨ p4748)
    (h7717 : (¬ p4748) ∨ p4750)
    (h59246 : (¬ p2553) ∨ (¬ p3016) ∨ (¬ p3822) ∨ (¬ p4750) ∨ (¬ p5220))
    (h8280 : p3016 ∨ (¬ p4974))
    (h6621 : (¬ p2542) ∨ p3016 ∨ (¬ p3660))
    (h66415 : p4974 ∨ p4971)
    (h7623 : p3660 ∨ (¬ p4716))
    (h8274 : p3574 ∨ (¬ p4971))
    (h66369 : p4714 ∨ p4716)
    (h44194 : (¬ p2247) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p4137))
    (h7617 : p3096 ∨ (¬ p4714))
    (h6861 : (¬ p3096) ∨ (¬ p3744) ∨ p4137)
    (h44325 : (¬ p2542) ∨ (¬ p3096) ∨ (¬ p3238) ∨ (¬ p3574) ∨ (¬ p3989))
    (h8439 : p3744 ∨ (¬ p5042))
    (h7073 : p3989 ∨ (¬ p4505))
    (h66426 : p5042 ∨ p5044)
    (h66331 : p4508 ∨ p4505)
    (h8446 : (¬ p5044) ∨ p5046)
    (h7080 : (¬ p4508) ∨ p4509)
    (h50990 : (¬ p2542) ∨ (¬ p2982) ∨ (¬ p3096) ∨ (¬ p3574) ∨ (¬ p5046))
    (h61866 : (¬ p2220) ∨ (¬ p2542) ∨ (¬ p3096) ∨ (¬ p3574) ∨ (¬ p4109) ∨ (¬ p4509))
    (h8229 : p2982 ∨ (¬ p4951))
    (h7130 : p2220 ∨ (¬ p4530))
    (h66412 : p4946 ∨ p4951)
    (h66334 : p4527 ∨ p4530)
    (h8221 : p3237 ∨ (¬ p4946))
    (h7124 : p4120 ∨ (¬ p4527))
    (h4597 : (¬ p3222) ∨ (¬ p3237) ∨ (¬ p3238))
    (h40922 : (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2659) ∨ (¬ p3904) ∨ (¬ p4120))
    (h4585 : p3222 ∨ (¬ p3231))
    (h7349 : p2373 ∨ (¬ p4609))
    (h66433 : p3225 ∨ p3231)
    (h66350 : p4609 ∨ p4606)
    (h4571 : p3193 ∨ (¬ p3225))
    (h7341 : (¬ p4606) ∨ p4607)
    (h43960 : (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3452) ∨ (¬ p4256))
    (h22568 : p2509 ∨ (¬ p3238) ∨ (¬ p4607))
    (h12853 : p4256 ∨ p5977)
    (h43963 : (¬ p2247) ∨ (¬ p2509) ∨ (¬ p3083) ∨ (¬ p3402) ∨ (¬ p3574))
    (h66566 : (¬ p5977) ∨ (¬ p5978))
    (h12860 : p3083 ∨ p5978)
    : (¬ p3238) ∨ (¬ p4111) ∨ (¬ p3402) ∨ (¬ p2247) ∨ (¬ p3452) ∨ (¬ p3822) ∨ (¬ p5219) ∨ (¬ p2553) ∨ (¬ p2659) ∨ (¬ p2542) ∨ (¬ p4535) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3238 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5219 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4535 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3584 := (Or.elim h8873 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u12 : p5220 := (Or.elim h8871 (fun q0 => (False.elim (q0 u6))) (fun r0 => r0));
    let u13 : p4109 := (Or.elim h7141 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    let u14 : p3904 := (Or.elim h7140 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    let u15 : (¬ p3359) := (Or.elim h48558 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u4))))))));
    let u16 : (¬ p2850) := (Or.elim h44020 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u11))))))));
    let u17 : (¬ p5169) := (Or.elim h8759 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u18 : (¬ p4883) := (Or.elim h8040 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    let u19 : p5174 := (Or.elim h66443 (fun q0 => (False.elim (u17 q0))) (fun r0 => r0));
    let u20 : p4880 := (Or.elim h66398 (fun q0 => q0) (fun r0 => (False.elim (u18 r0))));
    let u21 : p3343 := (Or.elim h8765 (fun q0 => q0) (fun r0 => (False.elim (r0 u19))));
    let u22 : p3684 := (Or.elim h8034 (fun q0 => q0) (fun r0 => (False.elim (r0 u20))));
    let u23 : (¬ p3683) := (Or.elim h5390 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u22))))));
    let u24 : (¬ p4751) := (Or.elim h7719 (fun q0 => (False.elim (u23 q0))) (fun r0 => r0));
    let u25 : p4748 := (Or.elim h66376 (fun q0 => (False.elim (u24 q0))) (fun r0 => r0));
    let u26 : p4750 := (Or.elim h7717 (fun q0 => (False.elim (q0 u25))) (fun r0 => r0));
    let u27 : (¬ p3016) := (Or.elim h59246 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u26))) (fun r3 => (False.elim (r3 u12))))))))));
    let u28 : (¬ p4974) := (Or.elim h8280 (fun q0 => (False.elim (u27 q0))) (fun r0 => r0));
    let u29 : (¬ p3660) := (Or.elim h6621 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u27 q1))) (fun r1 => r1))));
    let u30 : p4971 := (Or.elim h66415 (fun q0 => (False.elim (u28 q0))) (fun r0 => r0));
    let u31 : (¬ p4716) := (Or.elim h7623 (fun q0 => (False.elim (u29 q0))) (fun r0 => r0));
    let u32 : p3574 := (Or.elim h8274 (fun q0 => q0) (fun r0 => (False.elim (r0 u30))));
    let u33 : p4714 := (Or.elim h66369 (fun q0 => q0) (fun r0 => (False.elim (u31 r0))));
    let u34 : (¬ p4137) := (Or.elim h44194 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u32))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    let u35 : p3096 := (Or.elim h7617 (fun q0 => q0) (fun r0 => (False.elim (r0 u33))));
    let u36 : (¬ p3744) := (Or.elim h6861 (fun q0 => (False.elim (q0 u35))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u34 r1))))));
    let u37 : (¬ p3989) := (Or.elim h44325 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u35))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u32))) (fun r3 => r3))))))));
    let u38 : (¬ p5042) := (Or.elim h8439 (fun q0 => (False.elim (u36 q0))) (fun r0 => r0));
    let u39 : (¬ p4505) := (Or.elim h7073 (fun q0 => (False.elim (u37 q0))) (fun r0 => r0));
    let u40 : p5044 := (Or.elim h66426 (fun q0 => (False.elim (u38 q0))) (fun r0 => r0));
    let u41 : p4508 := (Or.elim h66331 (fun q0 => q0) (fun r0 => (False.elim (u39 r0))));
    let u42 : p5046 := (Or.elim h8446 (fun q0 => (False.elim (q0 u40))) (fun r0 => r0));
    let u43 : p4509 := (Or.elim h7080 (fun q0 => (False.elim (q0 u41))) (fun r0 => r0));
    let u44 : (¬ p2982) := (Or.elim h50990 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u35))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u32))) (fun r3 => (False.elim (r3 u42))))))))));
    let u45 : (¬ p2220) := (Or.elim h61866 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u35))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u32))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (False.elim (r4 u43))))))))))));
    let u46 : (¬ p4951) := (Or.elim h8229 (fun q0 => (False.elim (u44 q0))) (fun r0 => r0));
    let u47 : (¬ p4530) := (Or.elim h7130 (fun q0 => (False.elim (u45 q0))) (fun r0 => r0));
    let u48 : p4946 := (Or.elim h66412 (fun q0 => q0) (fun r0 => (False.elim (u46 r0))));
    let u49 : p4527 := (Or.elim h66334 (fun q0 => q0) (fun r0 => (False.elim (u47 r0))));
    let u50 : p3237 := (Or.elim h8221 (fun q0 => q0) (fun r0 => (False.elim (r0 u48))));
    let u51 : p4120 := (Or.elim h7124 (fun q0 => q0) (fun r0 => (False.elim (r0 u49))));
    let u52 : (¬ p3222) := (Or.elim h4597 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u50))) (fun r1 => (False.elim (r1 u0))))));
    let u53 : (¬ p2373) := (Or.elim h40922 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (False.elim (r3 u51))))))))));
    let u54 : (¬ p3231) := (Or.elim h4585 (fun q0 => (False.elim (u52 q0))) (fun r0 => r0));
    let u55 : (¬ p4609) := (Or.elim h7349 (fun q0 => (False.elim (u53 q0))) (fun r0 => r0));
    let u56 : p3225 := (Or.elim h66433 (fun q0 => q0) (fun r0 => (False.elim (u54 r0))));
    let u57 : p4606 := (Or.elim h66350 (fun q0 => (False.elim (u55 q0))) (fun r0 => r0));
    let u58 : p3193 := (Or.elim h4571 (fun q0 => q0) (fun r0 => (False.elim (r0 u56))));
    let u59 : p4607 := (Or.elim h7341 (fun q0 => (False.elim (q0 u57))) (fun r0 => r0));
    let u60 : (¬ p4256) := (Or.elim h43960 (fun q0 => (False.elim (q0 u58))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u21))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => r2))))));
    let u61 : p2509 := (Or.elim h22568 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u59))))));
    let u62 : p5977 := (Or.elim h12853 (fun q0 => (False.elim (u60 q0))) (fun r0 => r0));
    let u63 : (¬ p3083) := (Or.elim h43963 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u61))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u32))))))))));
    let u64 : (¬ p5978) := (Or.elim h66566 (fun q0 => (False.elim (q0 u62))) (fun r0 => r0));
    (Or.elim h12860 (fun q0 => (False.elim (u63 q0))) (fun r0 => (False.elim (u64 r0)))))

theorem step66707 (p2247 p2509 p2534 p3083 p3193 p3256 p3343 p3358 p3402 p3452 p3574 p4121 p4256 p4598 p5007 p5010 p5869 p5870 : Prop)
    (h43960 : (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3452) ∨ (¬ p4256))
    (h8369 : p4256 ∨ (¬ p5007))
    (h66422 : p5007 ∨ p5010)
    (h8374 : p4121 ∨ (¬ p5010))
    (h8375 : p3083 ∨ (¬ p5010))
    (h41271 : (¬ p2534) ∨ (¬ p3256) ∨ (¬ p3574) ∨ (¬ p4121) ∨ (¬ p4598))
    (h43963 : (¬ p2247) ∨ (¬ p2509) ∨ (¬ p3083) ∨ (¬ p3402) ∨ (¬ p3574))
    (h12206 : p2534 ∨ p5869)
    (h33686 : p2509 ∨ (¬ p3193) ∨ (¬ p3358))
    (h66531 : (¬ p5869) ∨ (¬ p5870))
    (h12212 : p3358 ∨ p5870)
    : (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3256) ∨ (¬ p3574) ∨ (¬ p4598) ∨ (¬ p3402) ∨ (¬ p2247) ∨ (¬ p3452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4256) := (Or.elim h43960 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => r2))))));
    let u9 : (¬ p5007) := (Or.elim h8369 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u10 : p5010 := (Or.elim h66422 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u11 : p4121 := (Or.elim h8374 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    let u12 : p3083 := (Or.elim h8375 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    let u13 : (¬ p2534) := (Or.elim h41271 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (False.elim (r3 u4))))))))));
    let u14 : (¬ p2509) := (Or.elim h43963 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3))))))))));
    let u15 : p5869 := (Or.elim h12206 (fun q0 => (False.elim (u13 q0))) (fun r0 => r0));
    let u16 : (¬ p3358) := (Or.elim h33686 (fun q0 => (False.elim (u14 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => r1))));
    let u17 : (¬ p5870) := (Or.elim h66531 (fun q0 => (False.elim (q0 u15))) (fun r0 => r0));
    (Or.elim h12212 (fun q0 => (False.elim (u16 q0))) (fun r0 => (False.elim (u17 r0)))))

theorem step66709 (p2534 p3083 p3256 p3358 p3359 p3574 p4121 p4598 p4692 p4694 p5010 : Prop)
    (h8374 : p4121 ∨ (¬ p5010))
    (h8375 : p3083 ∨ (¬ p5010))
    (h41271 : (¬ p2534) ∨ (¬ p3256) ∨ (¬ p3574) ∨ (¬ p4121) ∨ (¬ p4598))
    (h4830 : (¬ p3083) ∨ (¬ p3358) ∨ (¬ p3359))
    (h7567 : p2534 ∨ (¬ p4692))
    (h7572 : p3358 ∨ (¬ p4694))
    (h66366 : p4692 ∨ p4694)
    : (¬ p5010) ∨ (¬ p3359) ∨ (¬ p3256) ∨ (¬ p3574) ∨ (¬ p4598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5010 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4121 := (Or.elim h8374 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p3083 := (Or.elim h8375 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : (¬ p2534) := (Or.elim h41271 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4))))))))));
    let u8 : (¬ p3358) := (Or.elim h4830 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    let u9 : (¬ p4692) := (Or.elim h7567 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u10 : (¬ p4694) := (Or.elim h7572 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    (Or.elim h66366 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step66712 (p2363 p3063 p3256 p4078 p4340 p4341 p4347 p4358 p4600 p4602 p4843 p4856 p4871 : Prop)
    (h7981 : p4078 ∨ (¬ p4856))
    (h7983 : p4358 ∨ (¬ p4856))
    (h64438 : (¬ p2363) ∨ (¬ p3063) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4871))
    (h51999 : (¬ p3256) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4843))
    (h7332 : p2363 ∨ (¬ p4602))
    (h7326 : p4347 ∨ (¬ p4600))
    (h66349 : p4602 ∨ p4600)
    : (¬ p4856) ∨ (¬ p4340) ∨ (¬ p4871) ∨ (¬ p3063) ∨ (¬ p4341) ∨ (¬ p4843) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4856 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4871 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4843 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4078 := (Or.elim h7981 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : p4358 := (Or.elim h7983 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u9 : (¬ p2363) := (Or.elim h64438 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2))))))))));
    let u10 : (¬ p4347) := (Or.elim h51999 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u5))))))))));
    let u11 : (¬ p4602) := (Or.elim h7332 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u12 : (¬ p4600) := (Or.elim h7326 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    (Or.elim h66349 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u12 r0)))))

theorem step66713 (p2528 p2533 p3266 p3322 p3680 p3692 p3693 p4134 p4191 p4347 p4444 p4600 p5055 p5057 p5115 p5120 : Prop)
    (h5396 : (¬ p2528) ∨ (¬ p3692) ∨ (¬ p3693))
    (h8473 : p3692 ∨ (¬ p5055))
    (h66428 : p5055 ∨ p5057)
    (h8478 : p2533 ∨ (¬ p5057))
    (h7324 : p3322 ∨ (¬ p4600))
    (h7326 : p4347 ∨ (¬ p4600))
    (h56571 : (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3693) ∨ (¬ p4134) ∨ (¬ p4191))
    (h55233 : (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4444))
    (h8652 : p3266 ∨ (¬ p5120))
    (h8646 : p4444 ∨ (¬ p5115))
    (h66438 : p5115 ∨ p5120)
    : (¬ p4600) ∨ (¬ p3680) ∨ (¬ p4134) ∨ (¬ p3693) ∨ (¬ p4191) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4600 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3692) := (Or.elim h5396 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u3))))));
    let u7 : (¬ p5055) := (Or.elim h8473 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    let u8 : p5057 := (Or.elim h66428 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u9 : p2533 := (Or.elim h8478 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u10 : p3322 := (Or.elim h7324 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u11 : p4347 := (Or.elim h7326 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u12 : (¬ p3266) := (Or.elim h56571 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4))))))))))));
    let u13 : (¬ p4444) := (Or.elim h55233 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => r3))))))));
    let u14 : (¬ p5120) := (Or.elim h8652 (fun q0 => (False.elim (u12 q0))) (fun r0 => r0));
    let u15 : (¬ p5115) := (Or.elim h8646 (fun q0 => (False.elim (u13 q0))) (fun r0 => r0));
    (Or.elim h66438 (fun q0 => (False.elim (u15 q0))) (fun r0 => (False.elim (u14 r0)))))

theorem step66717 (p2244 p2245 p2247 p2274 p2284 p2295 p2313 p2440 p2563 p2590 p2651 p2654 p2657 p2661 p2667 p2727 p3016 p3568 p3662 p3879 p3952 p3983 p4110 p4111 p4153 p4154 p4198 p4533 p4562 p4565 p4568 p4571 p4579 p4582 p4714 p4716 p4809 p4812 p4971 p4972 p4974 : Prop)
    (h2625 : (¬ p2244) ∨ p2247)
    (h2623 : (¬ p2244) ∨ p2245)
    (h60888 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2563) ∨ (¬ p4198) ∨ (¬ p4533))
    (h7624 : p2563 ∨ (¬ p4716))
    (h66369 : p4714 ∨ p4716)
    (h7616 : p2590 ∨ (¬ p4714))
    (h7618 : p4110 ∨ (¬ p4714))
    (h20304 : (¬ p2440) ∨ (¬ p2590) ∨ (¬ p3016))
    (h43961 : (¬ p2247) ∨ (¬ p2440) ∨ (¬ p4110) ∨ (¬ p4111))
    (h27148 : (¬ p3879) ∨ p3952 ∨ (¬ p4110))
    (h19752 : (¬ p2284) ∨ (¬ p3879) ∨ (¬ p4110))
    (h8280 : p3016 ∨ (¬ p4974))
    (h7857 : p4111 ∨ (¬ p4809))
    (h7226 : p2284 ∨ (¬ p4565))
    (h66415 : p4974 ∨ p4971)
    (h66386 : p4809 ∨ p4812)
    (h66341 : p4565 ∨ p4562)
    (h8275 : (¬ p4971) ∨ p4972)
    (h7863 : p2727 ∨ (¬ p4812))
    (h7218 : p4153 ∨ (¬ p4562))
    (h44003 : (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3952))
    (h6201 : (¬ p3662) ∨ (¬ p4153) ∨ p4154)
    (h3435 : (¬ p2654) ∨ p2657)
    (h47738 : (¬ p2247) ∨ (¬ p2274) ∨ (¬ p3568) ∨ (¬ p4154))
    (h66378 : p2654 ∨ p2661)
    (h7237 : p3568 ∨ (¬ p4568))
    (h33740 : (¬ p2313) ∨ (¬ p2667) ∨ p3568)
    (h3449 : p2651 ∨ (¬ p2661))
    (h66342 : p4571 ∨ p4568)
    (h7279 : p2667 ∨ (¬ p4582))
    (h7243 : p2295 ∨ (¬ p4571))
    (h66346 : p4579 ∨ p4582)
    (h51734 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2651) ∨ (¬ p3983) ∨ (¬ p4972))
    (h7273 : p3983 ∨ (¬ p4579))
    : (¬ p2313) ∨ (¬ p4198) ∨ (¬ p4533) ∨ (¬ p2440) ∨ (¬ p3879) ∨ (¬ p2274) ∨ (¬ p3662) ∨ (¬ p2244) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2247 := (Or.elim h2625 (fun q0 => (False.elim (q0 u7))) (fun r0 => r0));
    let u9 : p2245 := (Or.elim h2623 (fun q0 => (False.elim (q0 u7))) (fun r0 => r0));
    let u10 : (¬ p2563) := (Or.elim h60888 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2))))))))));
    let u11 : (¬ p4716) := (Or.elim h7624 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u12 : p4714 := (Or.elim h66369 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u13 : p2590 := (Or.elim h7616 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u14 : p4110 := (Or.elim h7618 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u15 : (¬ p3016) := (Or.elim h20304 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => r1))));
    let u16 : (¬ p4111) := (Or.elim h43961 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => r2))))));
    let u17 : p3952 := (Or.elim h27148 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u14))))));
    let u18 : (¬ p2284) := (Or.elim h19752 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u14))))));
    let u19 : (¬ p4974) := (Or.elim h8280 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u20 : (¬ p4809) := (Or.elim h7857 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    let u21 : (¬ p4565) := (Or.elim h7226 (fun q0 => (False.elim (u18 q0))) (fun r0 => r0));
    let u22 : p4971 := (Or.elim h66415 (fun q0 => (False.elim (u19 q0))) (fun r0 => r0));
    let u23 : p4812 := (Or.elim h66386 (fun q0 => (False.elim (u20 q0))) (fun r0 => r0));
    let u24 : p4562 := (Or.elim h66341 (fun q0 => (False.elim (u21 q0))) (fun r0 => r0));
    let u25 : p4972 := (Or.elim h8275 (fun q0 => (False.elim (q0 u22))) (fun r0 => r0));
    let u26 : p2727 := (Or.elim h7863 (fun q0 => q0) (fun r0 => (False.elim (r0 u23))));
    let u27 : p4153 := (Or.elim h7218 (fun q0 => q0) (fun r0 => (False.elim (r0 u24))));
    let u28 : (¬ p2657) := (Or.elim h44003 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u26))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u17))))))))));
    let u29 : p4154 := (Or.elim h6201 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u27))) (fun r1 => r1))));
    let u30 : (¬ p2654) := (Or.elim h3435 (fun q0 => q0) (fun r0 => (False.elim (u28 r0))));
    let u31 : (¬ p3568) := (Or.elim h47738 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u29))))))));
    let u32 : p2661 := (Or.elim h66378 (fun q0 => (False.elim (u30 q0))) (fun r0 => r0));
    let u33 : (¬ p4568) := (Or.elim h7237 (fun q0 => (False.elim (u31 q0))) (fun r0 => r0));
    let u34 : (¬ p2667) := (Or.elim h33740 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u31 r1))))));
    let u35 : p2651 := (Or.elim h3449 (fun q0 => q0) (fun r0 => (False.elim (r0 u32))));
    let u36 : p4571 := (Or.elim h66342 (fun q0 => q0) (fun r0 => (False.elim (u33 r0))));
    let u37 : (¬ p4582) := (Or.elim h7279 (fun q0 => (False.elim (u34 q0))) (fun r0 => r0));
    let u38 : p2295 := (Or.elim h7243 (fun q0 => q0) (fun r0 => (False.elim (r0 u36))));
    let u39 : p4579 := (Or.elim h66346 (fun q0 => q0) (fun r0 => (False.elim (u37 r0))));
    let u40 : (¬ p3983) := (Or.elim h51734 (fun q0 => (False.elim (q0 u38))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u35))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u25))))))))));
    (Or.elim h7273 (fun q0 => (False.elim (u40 q0))) (fun r0 => (False.elim (r0 u39)))))

theorem step66718 (p2244 p2245 p2246 p2247 p2274 p2284 p2307 p2310 p2313 p2317 p2318 p2331 p2437 p2440 p2553 p2563 p2573 p2576 p2578 p2583 p2589 p2590 p2630 p2651 p2654 p2657 p2661 p2727 p2777 p2779 p2784 p2786 p2810 p2850 p2901 p2946 p2949 p2952 p2956 p2996 p3016 p3051 p3055 p3097 p3363 p3414 p3567 p3568 p3646 p3662 p3691 p3743 p3822 p3879 p3952 p4110 p4111 p4140 p4153 p4154 p4185 p4193 p4198 p4328 p4386 p4484 p4533 p4554 p4557 p4562 p4565 p4579 p4582 p4646 p4649 p4650 p4651 p4714 p4716 p4726 p4728 p4748 p4751 p4809 p4812 p4840 p4841 p4844 p4880 p4882 p4883 p4887 p4889 p4890 p4916 p4918 p4971 p4972 p4974 p4983 p4987 p5224 : Prop)
    (h20290 : (¬ p2274) ∨ (¬ p3822) ∨ (¬ p4185))
    (h8055 : p4185 ∨ (¬ p4890))
    (h66399 : p4887 ∨ p4890)
    (h8053 : (¬ p4887) ∨ p4889)
    (h8049 : p4193 ∨ (¬ p4887))
    (h9860 : (¬ p2274) ∨ (¬ p3097))
    (h7202 : p3097 ∨ (¬ p4554))
    (h66340 : p4554 ∨ p4557)
    (h7206 : p4140 ∨ (¬ p4557))
    (h2625 : (¬ p2244) ∨ p2247)
    (h2624 : (¬ p2244) ∨ p2246)
    (h2623 : (¬ p2244) ∨ p2245)
    (h7020 : p4198 ∨ (¬ p4484))
    (h7021 : p3743 ∨ (¬ p4484))
    (h7022 : p3646 ∨ (¬ p4484))
    (h41366 : (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3822) ∨ (¬ p4140) ∨ (¬ p4889))
    (h8321 : p3051 ∨ (¬ p4987))
    (h66419 : p4983 ∨ p4987)
    (h8314 : p3691 ∨ (¬ p4983))
    (h66717 : (¬ p2313) ∨ (¬ p4198) ∨ (¬ p4533) ∨ (¬ p2440) ∨ (¬ p3879) ∨ (¬ p2274) ∨ (¬ p3662) ∨ (¬ p2244))
    (h2756 : (¬ p2310) ∨ p2313)
    (h66343 : p2317 ∨ p2310)
    (h2768 : (¬ p2317) ∨ p2318)
    (h2770 : p2307 ∨ (¬ p2317))
    (h5636 : (¬ p2307) ∨ (¬ p2779) ∨ (¬ p3822))
    (h3682 : (¬ p2777) ∨ p2779)
    (h66391 : p2784 ∨ p2777)
    (h3696 : (¬ p2784) ∨ p2786)
    (h49446 : (¬ p2307) ∨ (¬ p2786) ∨ (¬ p3055) ∨ (¬ p3822) ∨ (¬ p5224))
    (h7664 : p3055 ∨ (¬ p4726))
    (h66373 : p4728 ∨ p4726)
    (h7668 : p3363 ∨ (¬ p4728))
    (h20692 : (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3363))
    (h8040 : p2850 ∨ (¬ p4883))
    (h66398 : p4880 ∨ p4883)
    (h8036 : (¬ p4880) ∨ p4882)
    (h63220 : (¬ p2307) ∨ (¬ p2563) ∨ (¬ p3743) ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p4882))
    (h7624 : p2563 ∨ (¬ p4716))
    (h66369 : p4714 ∨ p4716)
    (h7616 : p2590 ∨ (¬ p4714))
    (h7618 : p4110 ∨ (¬ p4714))
    (h20304 : (¬ p2440) ∨ (¬ p2590) ∨ (¬ p3016))
    (h3306 : (¬ p2573) ∨ (¬ p2589) ∨ (¬ p2590))
    (h47642 : (¬ p4110) ∨ p4646)
    (h43961 : (¬ p2247) ∨ (¬ p2440) ∨ (¬ p4110) ∨ (¬ p4111))
    (h27148 : (¬ p3879) ∨ p3952 ∨ (¬ p4110))
    (h19752 : (¬ p2284) ∨ (¬ p3879) ∨ (¬ p4110))
    (h8280 : p3016 ∨ (¬ p4974))
    (h3293 : p2573 ∨ (¬ p2583))
    (h7857 : p4111 ∨ (¬ p4809))
    (h62924 : (¬ p2318) ∨ (¬ p2901) ∨ (¬ p3691) ∨ (¬ p3822) ∨ (¬ p3952) ∨ (¬ p4889))
    (h7226 : p2284 ∨ (¬ p4565))
    (h66415 : p4974 ∨ p4971)
    (h66370 : p2576 ∨ p2583)
    (h66386 : p4809 ∨ p4812)
    (h8127 : p2901 ∨ (¬ p4918))
    (h66341 : p4565 ∨ p4562)
    (h8275 : (¬ p4971) ∨ p4972)
    (h3278 : (¬ p2576) ∨ p2578)
    (h7863 : p2727 ∨ (¬ p4812))
    (h66403 : p4916 ∨ p4918)
    (h7218 : p4153 ∨ (¬ p4562))
    (h25746 : (¬ p2307) ∨ p2553 ∨ (¬ p2578))
    (h40954 : (¬ p2437) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4646))
    (h44003 : (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3952))
    (h8119 : p4386 ∨ (¬ p4916))
    (h6201 : (¬ p3662) ∨ (¬ p4153) ∨ p4154)
    (h44623 : (¬ p2553) ∨ (¬ p2727) ∨ (¬ p3568) ∨ (¬ p4154))
    (h7453 : p2437 ∨ (¬ p4651))
    (h3435 : (¬ p2654) ∨ p2657)
    (h25522 : p2996 ∨ (¬ p3662) ∨ (¬ p4386))
    (h25390 : p3568 ∨ (¬ p3822) ∨ (¬ p4328))
    (h66356 : p4651 ∨ p4649)
    (h66378 : p2654 ∨ p2661)
    (h21894 : (¬ p2246) ∨ (¬ p2996) ∨ p3414)
    (h7951 : p4328 ∨ (¬ p4844))
    (h7448 : (¬ p4649) ∨ p4650)
    (h3449 : p2651 ∨ (¬ p2661))
    (h48093 : (¬ p2727) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3662) ∨ (¬ p4650))
    (h45716 : (¬ p2331) ∨ (¬ p2727) ∨ (¬ p3414) ∨ (¬ p4154))
    (h66394 : p4844 ∨ p4840)
    (h4042 : p2946 ∨ (¬ p2956))
    (h7281 : p2331 ∨ (¬ p4582))
    (h7945 : (¬ p4840) ∨ p4841)
    (h66408 : p2956 ∨ p2949)
    (h66346 : p4579 ∨ p4582)
    (h4028 : (¬ p2949) ∨ p2952)
    (h7274 : p3567 ∨ (¬ p4579))
    (h64204 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2952) ∨ (¬ p3952))
    (h52981 : (¬ p2307) ∨ (¬ p2630) ∨ (¬ p3567) ∨ (¬ p3822) ∨ (¬ p4841) ∨ (¬ p4972))
    (h7715 : p2810 ∨ (¬ p4748))
    (h7721 : p2630 ∨ (¬ p4751))
    (h66376 : p4751 ∨ p4748)
    : (¬ p4484) ∨ (¬ p4533) ∨ (¬ p2589) ∨ (¬ p2440) ∨ (¬ p3879) ∨ (¬ p2274) ∨ (¬ p5224) ∨ (¬ p3662) ∨ (¬ p3822) ∨ (¬ p2244) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4484 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5224 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4185) := (Or.elim h20290 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => r1))));
    let u11 : (¬ p4890) := (Or.elim h8055 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u12 : p4887 := (Or.elim h66399 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u13 : p4889 := (Or.elim h8053 (fun q0 => (False.elim (q0 u12))) (fun r0 => r0));
    let u14 : p4193 := (Or.elim h8049 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u15 : (¬ p3097) := (Or.elim h9860 (fun q0 => (False.elim (q0 u5))) (fun r0 => r0));
    let u16 : (¬ p4554) := (Or.elim h7202 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u17 : p4557 := (Or.elim h66340 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    let u18 : p4140 := (Or.elim h7206 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    let u19 : p2247 := (Or.elim h2625 (fun q0 => (False.elim (q0 u9))) (fun r0 => r0));
    let u20 : p2246 := (Or.elim h2624 (fun q0 => (False.elim (q0 u9))) (fun r0 => r0));
    let u21 : p2245 := (Or.elim h2623 (fun q0 => (False.elim (q0 u9))) (fun r0 => r0));
    let u22 : p4198 := (Or.elim h7020 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u23 : p3743 := (Or.elim h7021 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u24 : p3646 := (Or.elim h7022 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u25 : (¬ p3051) := (Or.elim h41366 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u24))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u18))) (fun r3 => (False.elim (r3 u13))))))))));
    let u26 : (¬ p4987) := (Or.elim h8321 (fun q0 => (False.elim (u25 q0))) (fun r0 => r0));
    let u27 : p4983 := (Or.elim h66419 (fun q0 => q0) (fun r0 => (False.elim (u26 r0))));
    let u28 : p3691 := (Or.elim h8314 (fun q0 => q0) (fun r0 => (False.elim (r0 u27))));
    let u29 : (¬ p2313) := (Or.elim h66717 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u22))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u9))))))))))))))));
    let u30 : (¬ p2310) := (Or.elim h2756 (fun q0 => q0) (fun r0 => (False.elim (u29 r0))));
    let u31 : p2317 := (Or.elim h66343 (fun q0 => q0) (fun r0 => (False.elim (u30 r0))));
    let u32 : p2318 := (Or.elim h2768 (fun q0 => (False.elim (q0 u31))) (fun r0 => r0));
    let u33 : p2307 := (Or.elim h2770 (fun q0 => q0) (fun r0 => (False.elim (r0 u31))));
    let u34 : (¬ p2779) := (Or.elim h5636 (fun q0 => (False.elim (q0 u33))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u8))))));
    let u35 : (¬ p2777) := (Or.elim h3682 (fun q0 => q0) (fun r0 => (False.elim (u34 r0))));
    let u36 : p2784 := (Or.elim h66391 (fun q0 => q0) (fun r0 => (False.elim (u35 r0))));
    let u37 : p2786 := (Or.elim h3696 (fun q0 => (False.elim (q0 u36))) (fun r0 => r0));
    let u38 : (¬ p3055) := (Or.elim h49446 (fun q0 => (False.elim (q0 u33))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u37))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u6))))))))));
    let u39 : (¬ p4726) := (Or.elim h7664 (fun q0 => (False.elim (u38 q0))) (fun r0 => r0));
    let u40 : p4728 := (Or.elim h66373 (fun q0 => q0) (fun r0 => (False.elim (u39 r0))));
    let u41 : p3363 := (Or.elim h7668 (fun q0 => q0) (fun r0 => (False.elim (r0 u40))));
    let u42 : (¬ p2850) := (Or.elim h20692 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u41))))));
    let u43 : (¬ p4883) := (Or.elim h8040 (fun q0 => (False.elim (u42 q0))) (fun r0 => r0));
    let u44 : p4880 := (Or.elim h66398 (fun q0 => q0) (fun r0 => (False.elim (u43 r0))));
    let u45 : p4882 := (Or.elim h8036 (fun q0 => (False.elim (q0 u44))) (fun r0 => r0));
    let u46 : (¬ p2563) := (Or.elim h63220 (fun q0 => (False.elim (q0 u33))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u23))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (False.elim (r4 u45))))))))))));
    let u47 : (¬ p4716) := (Or.elim h7624 (fun q0 => (False.elim (u46 q0))) (fun r0 => r0));
    let u48 : p4714 := (Or.elim h66369 (fun q0 => q0) (fun r0 => (False.elim (u47 r0))));
    let u49 : p2590 := (Or.elim h7616 (fun q0 => q0) (fun r0 => (False.elim (r0 u48))));
    let u50 : p4110 := (Or.elim h7618 (fun q0 => q0) (fun r0 => (False.elim (r0 u48))));
    let u51 : (¬ p3016) := (Or.elim h20304 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u49))) (fun r1 => r1))));
    let u52 : (¬ p2573) := (Or.elim h3306 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u49))))));
    let u53 : p4646 := (Or.elim h47642 (fun q0 => (False.elim (q0 u50))) (fun r0 => r0));
    let u54 : (¬ p4111) := (Or.elim h43961 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u50))) (fun r2 => r2))))));
    let u55 : p3952 := (Or.elim h27148 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u50))))));
    let u56 : (¬ p2284) := (Or.elim h19752 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u50))))));
    let u57 : (¬ p4974) := (Or.elim h8280 (fun q0 => (False.elim (u51 q0))) (fun r0 => r0));
    let u58 : (¬ p2583) := (Or.elim h3293 (fun q0 => (False.elim (u52 q0))) (fun r0 => r0));
    let u59 : (¬ p4809) := (Or.elim h7857 (fun q0 => (False.elim (u54 q0))) (fun r0 => r0));
    let u60 : (¬ p2901) := (Or.elim h62924 (fun q0 => (False.elim (q0 u32))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u28))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u55))) (fun r4 => (False.elim (r4 u13))))))))))));
    let u61 : (¬ p4565) := (Or.elim h7226 (fun q0 => (False.elim (u56 q0))) (fun r0 => r0));
    let u62 : p4971 := (Or.elim h66415 (fun q0 => (False.elim (u57 q0))) (fun r0 => r0));
    let u63 : p2576 := (Or.elim h66370 (fun q0 => q0) (fun r0 => (False.elim (u58 r0))));
    let u64 : p4812 := (Or.elim h66386 (fun q0 => (False.elim (u59 q0))) (fun r0 => r0));
    let u65 : (¬ p4918) := (Or.elim h8127 (fun q0 => (False.elim (u60 q0))) (fun r0 => r0));
    let u66 : p4562 := (Or.elim h66341 (fun q0 => (False.elim (u61 q0))) (fun r0 => r0));
    let u67 : p4972 := (Or.elim h8275 (fun q0 => (False.elim (q0 u62))) (fun r0 => r0));
    let u68 : p2578 := (Or.elim h3278 (fun q0 => (False.elim (q0 u63))) (fun r0 => r0));
    let u69 : p2727 := (Or.elim h7863 (fun q0 => q0) (fun r0 => (False.elim (r0 u64))));
    let u70 : p4916 := (Or.elim h66403 (fun q0 => q0) (fun r0 => (False.elim (u65 r0))));
    let u71 : p4153 := (Or.elim h7218 (fun q0 => q0) (fun r0 => (False.elim (r0 u66))));
    let u72 : p2553 := (Or.elim h25746 (fun q0 => (False.elim (q0 u33))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u68))))));
    let u73 : (¬ p2437) := (Or.elim h40954 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u69))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u53))))))))));
    let u74 : (¬ p2657) := (Or.elim h44003 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u69))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u55))))))))));
    let u75 : p4386 := (Or.elim h8119 (fun q0 => q0) (fun r0 => (False.elim (r0 u70))));
    let u76 : p4154 := (Or.elim h6201 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u71))) (fun r1 => r1))));
    let u77 : (¬ p3568) := (Or.elim h44623 (fun q0 => (False.elim (q0 u72))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u69))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u76))))))));
    let u78 : (¬ p4651) := (Or.elim h7453 (fun q0 => (False.elim (u73 q0))) (fun r0 => r0));
    let u79 : (¬ p2654) := (Or.elim h3435 (fun q0 => q0) (fun r0 => (False.elim (u74 r0))));
    let u80 : p2996 := (Or.elim h25522 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (False.elim (r1 u75))))));
    let u81 : (¬ p4328) := (Or.elim h25390 (fun q0 => (False.elim (u77 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => r1))));
    let u82 : p4649 := (Or.elim h66356 (fun q0 => (False.elim (u78 q0))) (fun r0 => r0));
    let u83 : p2661 := (Or.elim h66378 (fun q0 => (False.elim (u79 q0))) (fun r0 => r0));
    let u84 : p3414 := (Or.elim h21894 (fun q0 => (False.elim (q0 u20))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u80))) (fun r1 => r1))));
    let u85 : (¬ p4844) := (Or.elim h7951 (fun q0 => (False.elim (u81 q0))) (fun r0 => r0));
    let u86 : p4650 := (Or.elim h7448 (fun q0 => (False.elim (q0 u82))) (fun r0 => r0));
    let u87 : p2651 := (Or.elim h3449 (fun q0 => q0) (fun r0 => (False.elim (r0 u83))));
    let u88 : (¬ p2946) := (Or.elim h48093 (fun q0 => (False.elim (q0 u69))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u84))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u86))))))))));
    let u89 : (¬ p2331) := (Or.elim h45716 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u69))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u84))) (fun r2 => (False.elim (r2 u76))))))));
    let u90 : p4840 := (Or.elim h66394 (fun q0 => (False.elim (u85 q0))) (fun r0 => r0));
    let u91 : (¬ p2956) := (Or.elim h4042 (fun q0 => (False.elim (u88 q0))) (fun r0 => r0));
    let u92 : (¬ p4582) := (Or.elim h7281 (fun q0 => (False.elim (u89 q0))) (fun r0 => r0));
    let u93 : p4841 := (Or.elim h7945 (fun q0 => (False.elim (q0 u90))) (fun r0 => r0));
    let u94 : p2949 := (Or.elim h66408 (fun q0 => (False.elim (u91 q0))) (fun r0 => r0));
    let u95 : p4579 := (Or.elim h66346 (fun q0 => q0) (fun r0 => (False.elim (u92 r0))));
    let u96 : p2952 := (Or.elim h4028 (fun q0 => (False.elim (q0 u94))) (fun r0 => r0));
    let u97 : p3567 := (Or.elim h7274 (fun q0 => q0) (fun r0 => (False.elim (r0 u95))));
    let u98 : (¬ p2810) := (Or.elim h64204 (fun q0 => (False.elim (q0 u87))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u96))) (fun r2 => (False.elim (r2 u55))))))));
    let u99 : (¬ p2630) := (Or.elim h52981 (fun q0 => (False.elim (q0 u33))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u97))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u93))) (fun r4 => (False.elim (r4 u67))))))))))));
    let u100 : (¬ p4748) := (Or.elim h7715 (fun q0 => (False.elim (u98 q0))) (fun r0 => r0));
    let u101 : (¬ p4751) := (Or.elim h7721 (fun q0 => (False.elim (u99 q0))) (fun r0 => r0));
    (Or.elim h66376 (fun q0 => (False.elim (u101 q0))) (fun r0 => (False.elim (u100 r0)))))

theorem step66719 (p2135 p2137 p2142 p2146 p2156 p2274 p3758 p3822 p4185 p4193 p4887 p4890 : Prop)
    (h20290 : (¬ p2274) ∨ (¬ p3822) ∨ (¬ p4185))
    (h8055 : p4185 ∨ (¬ p4890))
    (h66399 : p4887 ∨ p4890)
    (h8051 : p3758 ∨ (¬ p4887))
    (h8049 : p4193 ∨ (¬ p4887))
    (h49213 : (¬ p2146) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p3822) ∨ (¬ p4193))
    (h5508 : (¬ p2137) ∨ (¬ p2156) ∨ (¬ p3758))
    (h2424 : (¬ p2142) ∨ p2146)
    (h2407 : (¬ p2135) ∨ p2137)
    (h66325 : p2135 ∨ p2142)
    : (¬ p2156) ∨ (¬ p2274) ∨ (¬ p3822) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4185) := (Or.elim h20290 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    let u4 : (¬ p4890) := (Or.elim h8055 (fun q0 => (False.elim (u3 q0))) (fun r0 => r0));
    let u5 : p4887 := (Or.elim h66399 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u6 : p3758 := (Or.elim h8051 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u7 : p4193 := (Or.elim h8049 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u8 : (¬ p2146) := (Or.elim h49213 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u7))))))))));
    let u9 : (¬ p2137) := (Or.elim h5508 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u6))))));
    let u10 : (¬ p2142) := (Or.elim h2424 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u11 : (¬ p2135) := (Or.elim h2407 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h66325 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step66720 (p2244 p2274 p2313 p2440 p3662 p3879 p4198 p4533 p4699 : Prop)
    (h7583 : p3879 ∨ (¬ p4699))
    (h7584 : p2440 ∨ (¬ p4699))
    (h66717 : (¬ p2313) ∨ (¬ p4198) ∨ (¬ p4533) ∨ (¬ p2440) ∨ (¬ p3879) ∨ (¬ p2274) ∨ (¬ p3662) ∨ (¬ p2244))
    : (¬ p4699) ∨ (¬ p4533) ∨ (¬ p3662) ∨ (¬ p2244) ∨ (¬ p2313) ∨ (¬ p4198) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4699 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3879 := (Or.elim h7583 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : p2440 := (Or.elim h7584 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h66717 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step66721 (p2542 p2589 p2737 p2850 p3055 p3365 p3367 p3574 p3585 p3684 p3905 p4343 p4734 p4880 p4883 p5213 p5215 : Prop)
    (h54113 : (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3574) ∨ (¬ p3585) ∨ (¬ p4343))
    (h47342 : (¬ p2542) ∨ (¬ p3055) ∨ (¬ p3574) ∨ (¬ p3684))
    (h8853 : p3585 ∨ (¬ p5213))
    (h8034 : p3684 ∨ (¬ p4880))
    (h66448 : p5215 ∨ p5213)
    (h66398 : p4880 ∨ p4883)
    (h8859 : p3367 ∨ (¬ p5215))
    (h8040 : p2850 ∨ (¬ p4883))
    (h49770 : (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3367) ∨ (¬ p3905) ∨ (¬ p4734))
    : (¬ p3574) ∨ (¬ p2737) ∨ (¬ p4734) ∨ (¬ p3055) ∨ (¬ p4343) ∨ (¬ p3905) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3365) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3574 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3585) := (Or.elim h54113 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    let u10 : (¬ p3684) := (Or.elim h47342 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => r2))))));
    let u11 : (¬ p5213) := (Or.elim h8853 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u12 : (¬ p4880) := (Or.elim h8034 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : p5215 := (Or.elim h66448 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u14 : p4883 := (Or.elim h66398 (fun q0 => (False.elim (u12 q0))) (fun r0 => r0));
    let u15 : p3367 := (Or.elim h8859 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u16 : p2850 := (Or.elim h8040 (fun q0 => q0) (fun r0 => (False.elim (r0 u14))));
    (Or.elim h49770 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u16))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step66722 (p2244 p2247 p2274 p2284 p2295 p2313 p2427 p2542 p2553 p2563 p2577 p2579 p2588 p2589 p2590 p2608 p2630 p2654 p2655 p2659 p2661 p2662 p2737 p2740 p2743 p2747 p2810 p3016 p3019 p3055 p3097 p3136 p3364 p3365 p3413 p3568 p3574 p3662 p3872 p3904 p3905 p3952 p3954 p4110 p4140 p4153 p4154 p4198 p4235 p4236 p4315 p4343 p4484 p4486 p4533 p4535 p4554 p4557 p4562 p4565 p4568 p4571 p4643 p4645 p4699 p4703 p4705 p4707 p4709 p4714 p4716 p4732 p4734 p4735 p4748 p4751 p4787 p4971 p4974 p5048 p5050 : Prop)
    (h2625 : (¬ p2244) ∨ p2247)
    (h7024 : (¬ p4484) ∨ p4486)
    (h7020 : p4198 ∨ (¬ p4484))
    (h9860 : (¬ p2274) ∨ (¬ p3097))
    (h7202 : p3097 ∨ (¬ p4554))
    (h66340 : p4554 ∨ p4557)
    (h7207 : p3872 ∨ (¬ p4557))
    (h7206 : p4140 ∨ (¬ p4557))
    (h7140 : p3904 ∨ (¬ p4535))
    (h7142 : p2589 ∨ (¬ p4535))
    (h7144 : p4533 ∨ (¬ p4535))
    (h26538 : p2577 ∨ (¬ p3904) ∨ (¬ p4198))
    (h53718 : (¬ p2589) ∨ p4705)
    (h60888 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2563) ∨ (¬ p4198) ∨ (¬ p4533))
    (h7624 : p2563 ∨ (¬ p4716))
    (h66369 : p4714 ∨ p4716)
    (h7616 : p2590 ∨ (¬ p4714))
    (h7618 : p4110 ∨ (¬ p4714))
    (h22679 : p2579 ∨ (¬ p2589) ∨ (¬ p2590))
    (h51737 : (¬ p2313) ∨ (¬ p2427) ∨ (¬ p4110) ∨ (¬ p4140) ∨ (¬ p4486))
    (h7435 : p2427 ∨ (¬ p4645))
    (h66355 : p4643 ∨ p4645)
    (h7429 : p4235 ∨ (¬ p4643))
    (h66720 : (¬ p4699) ∨ (¬ p4533) ∨ (¬ p3662) ∨ (¬ p2244) ∨ (¬ p2313) ∨ (¬ p4198) ∨ (¬ p2274))
    (h66367 : p4703 ∨ p4699)
    (h7589 : p3413 ∨ (¬ p4703))
    (h7590 : p2542 ∨ (¬ p4703))
    (h6146 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2662))
    (h3447 : (¬ p2661) ∨ p2662)
    (h66378 : p2654 ∨ p2661)
    (h3433 : (¬ p2654) ∨ p2655)
    (h3437 : (¬ p2654) ∨ p2659)
    (h49377 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p4787))
    (h15561 : (¬ p2655) ∨ p3905 ∨ (¬ p4236))
    (h65914 : (¬ p4235) ∨ (¬ p2579) ∨ (¬ p2284) ∨ (¬ p2659) ∨ (¬ p4705) ∨ (¬ p3413) ∨ (¬ p3872))
    (h7721 : p2630 ∨ (¬ p4751))
    (h7226 : p2284 ∨ (¬ p4565))
    (h66376 : p4751 ∨ p4748)
    (h66341 : p4565 ∨ p4562)
    (h7713 : p3364 ∨ (¬ p4748))
    (h7714 : p4343 ∨ (¬ p4748))
    (h7715 : p2810 ∨ (¬ p4748))
    (h7218 : p4153 ∨ (¬ p4562))
    (h7220 : p3952 ∨ (¬ p4562))
    (h6408 : p3055 ∨ (¬ p3364) ∨ (¬ p3365))
    (h47356 : (¬ p2247) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p3662))
    (h6201 : (¬ p3662) ∨ (¬ p4153) ∨ p4154)
    (h46320 : (¬ p2247) ∨ (¬ p2608) ∨ (¬ p3662) ∨ (¬ p3952))
    (h8462 : p3136 ∨ (¬ p5050))
    (h47738 : (¬ p2247) ∨ (¬ p2274) ∨ (¬ p3568) ∨ (¬ p4154))
    (h7687 : p2608 ∨ (¬ p4735))
    (h66427 : p5048 ∨ p5050)
    (h7237 : p3568 ∨ (¬ p4568))
    (h66374 : p4732 ∨ p4735)
    (h8456 : p4315 ∨ (¬ p5048))
    (h66342 : p4571 ∨ p4568)
    (h7681 : p3954 ∨ (¬ p4732))
    (h7683 : (¬ p4732) ∨ p4734)
    (h46288 : (¬ p2743) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4315))
    (h7243 : p2295 ∨ (¬ p4571))
    (h3608 : (¬ p2740) ∨ p2743)
    (h66387 : p2740 ∨ p2747)
    (h3622 : p2737 ∨ (¬ p2747))
    (h66721 : (¬ p3574) ∨ (¬ p2737) ∨ (¬ p4734) ∨ (¬ p3055) ∨ (¬ p4343) ∨ (¬ p3905) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3365))
    (h8274 : p3574 ∨ (¬ p4971))
    (h66415 : p4974 ∨ p4971)
    (h8279 : p3019 ∨ (¬ p4974))
    (h8280 : p3016 ∨ (¬ p4974))
    (h41816 : (¬ p2295) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2659) ∨ (¬ p3019))
    (h48685 : (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2659) ∨ (¬ p3016))
    (h7601 : p2588 ∨ (¬ p4707))
    (h7607 : p2553 ∨ (¬ p4709))
    (h66368 : p4709 ∨ p4707)
    : (¬ p4535) ∨ (¬ p3662) ∨ (¬ p2244) ∨ (¬ p2313) ∨ (¬ p4787) ∨ (¬ p3365) ∨ (¬ p4236) ∨ (¬ p4484) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4535 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4484 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2247 := (Or.elim h2625 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u10 : p4486 := (Or.elim h7024 (fun q0 => (False.elim (q0 u7))) (fun r0 => r0));
    let u11 : p4198 := (Or.elim h7020 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u12 : (¬ p3097) := (Or.elim h9860 (fun q0 => (False.elim (q0 u8))) (fun r0 => r0));
    let u13 : (¬ p4554) := (Or.elim h7202 (fun q0 => (False.elim (u12 q0))) (fun r0 => r0));
    let u14 : p4557 := (Or.elim h66340 (fun q0 => (False.elim (u13 q0))) (fun r0 => r0));
    let u15 : p3872 := (Or.elim h7207 (fun q0 => q0) (fun r0 => (False.elim (r0 u14))));
    let u16 : p4140 := (Or.elim h7206 (fun q0 => q0) (fun r0 => (False.elim (r0 u14))));
    let u17 : p3904 := (Or.elim h7140 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u18 : p2589 := (Or.elim h7142 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u19 : p4533 := (Or.elim h7144 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u20 : p2577 := (Or.elim h26538 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u17))) (fun r1 => (False.elim (r1 u11))))));
    let u21 : p4705 := (Or.elim h53718 (fun q0 => (False.elim (q0 u18))) (fun r0 => r0));
    let u22 : (¬ p2563) := (Or.elim h60888 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (False.elim (r3 u19))))))))));
    let u23 : (¬ p4716) := (Or.elim h7624 (fun q0 => (False.elim (u22 q0))) (fun r0 => r0));
    let u24 : p4714 := (Or.elim h66369 (fun q0 => q0) (fun r0 => (False.elim (u23 r0))));
    let u25 : p2590 := (Or.elim h7616 (fun q0 => q0) (fun r0 => (False.elim (r0 u24))));
    let u26 : p4110 := (Or.elim h7618 (fun q0 => q0) (fun r0 => (False.elim (r0 u24))));
    let u27 : p2579 := (Or.elim h22679 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u18))) (fun r1 => (False.elim (r1 u25))))));
    let u28 : (¬ p2427) := (Or.elim h51737 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u26))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u16))) (fun r3 => (False.elim (r3 u10))))))))));
    let u29 : (¬ p4645) := (Or.elim h7435 (fun q0 => (False.elim (u28 q0))) (fun r0 => r0));
    let u30 : p4643 := (Or.elim h66355 (fun q0 => q0) (fun r0 => (False.elim (u29 r0))));
    let u31 : p4235 := (Or.elim h7429 (fun q0 => q0) (fun r0 => (False.elim (r0 u30))));
    let u32 : (¬ p4699) := (Or.elim h66720 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u19))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (False.elim (r5 u8))))))))))))));
    let u33 : p4703 := (Or.elim h66367 (fun q0 => q0) (fun r0 => (False.elim (u32 r0))));
    let u34 : p3413 := (Or.elim h7589 (fun q0 => q0) (fun r0 => (False.elim (r0 u33))));
    let u35 : p2542 := (Or.elim h7590 (fun q0 => q0) (fun r0 => (False.elim (r0 u33))));
    let u36 : (¬ p2662) := (Or.elim h6146 (fun q0 => (False.elim (q0 u35))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u18))) (fun r1 => r1))));
    let u37 : (¬ p2661) := (Or.elim h3447 (fun q0 => q0) (fun r0 => (False.elim (u36 r0))));
    let u38 : p2654 := (Or.elim h66378 (fun q0 => q0) (fun r0 => (False.elim (u37 r0))));
    let u39 : p2655 := (Or.elim h3433 (fun q0 => (False.elim (q0 u38))) (fun r0 => r0));
    let u40 : p2659 := (Or.elim h3437 (fun q0 => (False.elim (q0 u38))) (fun r0 => r0));
    let u41 : (¬ p2630) := (Or.elim h49377 (fun q0 => (False.elim (q0 u35))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u18))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u39))) (fun r3 => (False.elim (r3 u4))))))))));
    let u42 : p3905 := (Or.elim h15561 (fun q0 => (False.elim (q0 u39))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u6))))));
    let u43 : (¬ p2284) := (Or.elim h65914 (fun q0 => (False.elim (q0 u31))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u27))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u40))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u21))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u34))) (fun r5 => (False.elim (r5 u15))))))))))))));
    let u44 : (¬ p4751) := (Or.elim h7721 (fun q0 => (False.elim (u41 q0))) (fun r0 => r0));
    let u45 : (¬ p4565) := (Or.elim h7226 (fun q0 => (False.elim (u43 q0))) (fun r0 => r0));
    let u46 : p4748 := (Or.elim h66376 (fun q0 => (False.elim (u44 q0))) (fun r0 => r0));
    let u47 : p4562 := (Or.elim h66341 (fun q0 => (False.elim (u45 q0))) (fun r0 => r0));
    let u48 : p3364 := (Or.elim h7713 (fun q0 => q0) (fun r0 => (False.elim (r0 u46))));
    let u49 : p4343 := (Or.elim h7714 (fun q0 => q0) (fun r0 => (False.elim (r0 u46))));
    let u50 : p2810 := (Or.elim h7715 (fun q0 => q0) (fun r0 => (False.elim (r0 u46))));
    let u51 : p4153 := (Or.elim h7218 (fun q0 => q0) (fun r0 => (False.elim (r0 u47))));
    let u52 : p3952 := (Or.elim h7220 (fun q0 => q0) (fun r0 => (False.elim (r0 u47))));
    let u53 : p3055 := (Or.elim h6408 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u48))) (fun r1 => (False.elim (r1 u5))))));
    let u54 : (¬ p3136) := (Or.elim h47356 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u50))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    let u55 : p4154 := (Or.elim h6201 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u51))) (fun r1 => r1))));
    let u56 : (¬ p2608) := (Or.elim h46320 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u52))))))));
    let u57 : (¬ p5050) := (Or.elim h8462 (fun q0 => (False.elim (u54 q0))) (fun r0 => r0));
    let u58 : (¬ p3568) := (Or.elim h47738 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u55))))))));
    let u59 : (¬ p4735) := (Or.elim h7687 (fun q0 => (False.elim (u56 q0))) (fun r0 => r0));
    let u60 : p5048 := (Or.elim h66427 (fun q0 => q0) (fun r0 => (False.elim (u57 r0))));
    let u61 : (¬ p4568) := (Or.elim h7237 (fun q0 => (False.elim (u58 q0))) (fun r0 => r0));
    let u62 : p4732 := (Or.elim h66374 (fun q0 => q0) (fun r0 => (False.elim (u59 r0))));
    let u63 : p4315 := (Or.elim h8456 (fun q0 => q0) (fun r0 => (False.elim (r0 u60))));
    let u64 : p4571 := (Or.elim h66342 (fun q0 => q0) (fun r0 => (False.elim (u61 r0))));
    let u65 : p3954 := (Or.elim h7681 (fun q0 => q0) (fun r0 => (False.elim (r0 u62))));
    let u66 : p4734 := (Or.elim h7683 (fun q0 => (False.elim (q0 u62))) (fun r0 => r0));
    let u67 : (¬ p2743) := (Or.elim h46288 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u52))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u65))) (fun r2 => (False.elim (r2 u63))))))));
    let u68 : p2295 := (Or.elim h7243 (fun q0 => q0) (fun r0 => (False.elim (r0 u64))));
    let u69 : (¬ p2740) := (Or.elim h3608 (fun q0 => q0) (fun r0 => (False.elim (u67 r0))));
    let u70 : p2747 := (Or.elim h66387 (fun q0 => (False.elim (u69 q0))) (fun r0 => r0));
    let u71 : p2737 := (Or.elim h3622 (fun q0 => q0) (fun r0 => (False.elim (r0 u70))));
    let u72 : (¬ p3574) := (Or.elim h66721 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u71))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u66))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u53))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u49))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u42))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u35))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u18))) (fun r7 => (False.elim (r7 u5))))))))))))))))));
    let u73 : (¬ p4971) := (Or.elim h8274 (fun q0 => (False.elim (u72 q0))) (fun r0 => r0));
    let u74 : p4974 := (Or.elim h66415 (fun q0 => q0) (fun r0 => (False.elim (u73 r0))));
    let u75 : p3019 := (Or.elim h8279 (fun q0 => q0) (fun r0 => (False.elim (r0 u74))));
    let u76 : p3016 := (Or.elim h8280 (fun q0 => q0) (fun r0 => (False.elim (r0 u74))));
    let u77 : (¬ p2588) := (Or.elim h41816 (fun q0 => (False.elim (q0 u68))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u27))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u40))) (fun r3 => (False.elim (r3 u75))))))))));
    let u78 : (¬ p2553) := (Or.elim h48685 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u20))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u40))) (fun r3 => (False.elim (r3 u76))))))))));
    let u79 : (¬ p4707) := (Or.elim h7601 (fun q0 => (False.elim (u77 q0))) (fun r0 => r0));
    let u80 : (¬ p4709) := (Or.elim h7607 (fun q0 => (False.elim (u78 q0))) (fun r0 => r0));
    (Or.elim h66368 (fun q0 => (False.elim (u80 q0))) (fun r0 => (False.elim (u79 r0)))))

theorem step66727 (p2313 p2386 p2553 p2576 p2577 p2583 p2659 p3016 : Prop)
    (h15355 : (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2553))
    (h48685 : (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2659) ∨ (¬ p3016))
    (h3291 : p2386 ∨ (¬ p2583))
    (h3277 : (¬ p2576) ∨ p2577)
    (h66370 : p2576 ∨ p2583)
    : (¬ p2553) ∨ (¬ p2313) ∨ (¬ p2659) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2386) := (Or.elim h15355 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u0))))));
    let u5 : (¬ p2577) := (Or.elim h48685 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    let u6 : (¬ p2583) := (Or.elim h3291 (fun q0 => (False.elim (u4 q0))) (fun r0 => r0));
    let u7 : (¬ p2576) := (Or.elim h3277 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h66370 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step66733 (p2122 p2177 p2190 p2274 p2295 p2299 p2307 p2352 p2363 p2383 p2459 p2553 p2576 p2578 p2583 p2584 p2588 p2598 p2630 p2737 p2780 p2797 p2811 p2881 p2911 p2946 p3019 p3146 p3325 p3367 p3389 p3581 p3585 p3644 p3759 p3822 p3872 p3921 p3956 p3958 p3989 p4342 p4343 p4347 p4348 p4375 p4389 p4470 p4474 p4500 p4502 p4505 p4508 p4594 p4597 p4600 p4602 p4665 p4667 p4704 p4707 p4709 p4726 p4728 p4748 p4751 p4921 p4923 p4971 p4974 p5213 p5215 p5219 p5223 : Prop)
    (h6984 : p3822 ∨ (¬ p4470))
    (h66324 : p4474 ∨ p4470)
    (h6990 : p2122 ∨ (¬ p4474))
    (h9753 : (¬ p2553) ∨ (¬ p2588))
    (h14557 : (¬ p2307) ∨ (¬ p2578) ∨ (¬ p2588))
    (h51714 : (¬ p2299) ∨ (¬ p2588) ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p3958))
    (h6589 : (¬ p2588) ∨ p3822 ∨ (¬ p4342))
    (h20173 : (¬ p2295) ∨ (¬ p2588) ∨ (¬ p4389))
    (h7607 : p2553 ∨ (¬ p4709))
    (h3278 : (¬ p2576) ∨ p2578)
    (h7056 : p2299 ∨ (¬ p4500))
    (h8872 : p4342 ∨ (¬ p5219))
    (h8273 : p4389 ∨ (¬ p4971))
    (h66368 : p4709 ∨ p4707)
    (h66370 : p2576 ∨ p2583)
    (h66330 : p4502 ∨ p4500)
    (h66449 : p5219 ∨ p5223)
    (h66415 : p4974 ∨ p4971)
    (h7599 : p3581 ∨ (¬ p4707))
    (h7600 : p3921 ∨ (¬ p4707))
    (h3292 : (¬ p2583) ∨ p2584)
    (h7061 : p3325 ∨ (¬ p4502))
    (h7062 : p2177 ∨ (¬ p4502))
    (h8878 : p4375 ∨ (¬ p5223))
    (h8279 : p3019 ∨ (¬ p4974))
    (h22168 : (¬ p2307) ∨ (¬ p2584) ∨ p3389 ∨ (¬ p3921))
    (h20380 : (¬ p2274) ∨ (¬ p3325) ∨ (¬ p3989))
    (h6137 : (¬ p2307) ∨ p2383 ∨ (¬ p3325))
    (h60360 : (¬ p2177) ∨ (¬ p2274) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p3958))
    (h20127 : (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4375))
    (h27541 : (¬ p2630) ∨ p2797 ∨ (¬ p3019))
    (h7073 : p3989 ∨ (¬ p4505))
    (h8138 : p3644 ∨ (¬ p4921))
    (h7670 : p2598 ∨ (¬ p4728))
    (h7721 : p2630 ∨ (¬ p4751))
    (h66331 : p4508 ∨ p4505)
    (h66404 : p4923 ∨ p4921)
    (h66373 : p4728 ∨ p4726)
    (h66376 : p4751 ∨ p4748)
    (h7078 : p2190 ∨ (¬ p4508))
    (h8144 : p2911 ∨ (¬ p4923))
    (h7663 : p3759 ∨ (¬ p4726))
    (h7714 : p4343 ∨ (¬ p4748))
    (h52009 : (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4704))
    (h8853 : p3585 ∨ (¬ p5213))
    (h66448 : p5215 ∨ p5213)
    (h8859 : p3367 ∨ (¬ p5215))
    (h45031 : (¬ p2122) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3367) ∨ (¬ p4375))
    (h44970 : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759))
    (h7315 : p2352 ∨ (¬ p4597))
    (h7487 : p2459 ∨ (¬ p4667))
    (h66348 : p4597 ∨ p4594)
    (h66358 : p4665 ∨ p4667)
    (h7309 : p3956 ∨ (¬ p4594))
    (h7481 : p4348 ∨ (¬ p4665))
    (h41157 : (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4347))
    (h43183 : (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4348))
    (h7326 : p4347 ∨ (¬ p4600))
    (h7332 : p2363 ∨ (¬ p4602))
    (h66349 : p4602 ∨ p4600)
    : (¬ p2588) ∨ p2797 ∨ (¬ p2295) ∨ (¬ p3146) ∨ (¬ p3958) ∨ (¬ p4704) ∨ (¬ p3872) ∨ (¬ p2274) ∨ p3822 ∨ (¬ p2780) ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p2811) ∨ (¬ p2737) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3822) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))));
    let u15 : (¬ p4470) := (Or.elim h6984 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u16 : p4474 := (Or.elim h66324 (fun q0 => q0) (fun r0 => (False.elim (u15 r0))));
    let u17 : p2122 := (Or.elim h6990 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    let u18 : (¬ p2553) := (Or.elim h9753 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u19 : (¬ p2578) := (Or.elim h14557 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u0))))));
    let u20 : (¬ p2299) := (Or.elim h51714 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4))))))))));
    let u21 : (¬ p4342) := (Or.elim h6589 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => r1))));
    let u22 : (¬ p4389) := (Or.elim h20173 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => r1))));
    let u23 : (¬ p4709) := (Or.elim h7607 (fun q0 => (False.elim (u18 q0))) (fun r0 => r0));
    let u24 : (¬ p2576) := (Or.elim h3278 (fun q0 => q0) (fun r0 => (False.elim (u19 r0))));
    let u25 : (¬ p4500) := (Or.elim h7056 (fun q0 => (False.elim (u20 q0))) (fun r0 => r0));
    let u26 : (¬ p5219) := (Or.elim h8872 (fun q0 => (False.elim (u21 q0))) (fun r0 => r0));
    let u27 : (¬ p4971) := (Or.elim h8273 (fun q0 => (False.elim (u22 q0))) (fun r0 => r0));
    let u28 : p4707 := (Or.elim h66368 (fun q0 => (False.elim (u23 q0))) (fun r0 => r0));
    let u29 : p2583 := (Or.elim h66370 (fun q0 => (False.elim (u24 q0))) (fun r0 => r0));
    let u30 : p4502 := (Or.elim h66330 (fun q0 => q0) (fun r0 => (False.elim (u25 r0))));
    let u31 : p5223 := (Or.elim h66449 (fun q0 => (False.elim (u26 q0))) (fun r0 => r0));
    let u32 : p4974 := (Or.elim h66415 (fun q0 => q0) (fun r0 => (False.elim (u27 r0))));
    let u33 : p3581 := (Or.elim h7599 (fun q0 => q0) (fun r0 => (False.elim (r0 u28))));
    let u34 : p3921 := (Or.elim h7600 (fun q0 => q0) (fun r0 => (False.elim (r0 u28))));
    let u35 : p2584 := (Or.elim h3292 (fun q0 => (False.elim (q0 u29))) (fun r0 => r0));
    let u36 : p3325 := (Or.elim h7061 (fun q0 => q0) (fun r0 => (False.elim (r0 u30))));
    let u37 : p2177 := (Or.elim h7062 (fun q0 => q0) (fun r0 => (False.elim (r0 u30))));
    let u38 : p4375 := (Or.elim h8878 (fun q0 => q0) (fun r0 => (False.elim (r0 u31))));
    let u39 : p3019 := (Or.elim h8279 (fun q0 => q0) (fun r0 => (False.elim (r0 u32))));
    let u40 : p3389 := (Or.elim h22168 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u35))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u34))))))));
    let u41 : (¬ p3989) := (Or.elim h20380 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u36))) (fun r1 => r1))));
    let u42 : p2383 := (Or.elim h6137 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u36))))));
    let u43 : (¬ p3644) := (Or.elim h60360 (fun q0 => (False.elim (q0 u37))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u33))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    let u44 : (¬ p2598) := (Or.elim h20127 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (False.elim (r1 u38))))));
    let u45 : (¬ p2630) := (Or.elim h27541 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u39))))));
    let u46 : (¬ p4505) := (Or.elim h7073 (fun q0 => (False.elim (u41 q0))) (fun r0 => r0));
    let u47 : (¬ p4921) := (Or.elim h8138 (fun q0 => (False.elim (u43 q0))) (fun r0 => r0));
    let u48 : (¬ p4728) := (Or.elim h7670 (fun q0 => (False.elim (u44 q0))) (fun r0 => r0));
    let u49 : (¬ p4751) := (Or.elim h7721 (fun q0 => (False.elim (u45 q0))) (fun r0 => r0));
    let u50 : p4508 := (Or.elim h66331 (fun q0 => q0) (fun r0 => (False.elim (u46 r0))));
    let u51 : p4923 := (Or.elim h66404 (fun q0 => q0) (fun r0 => (False.elim (u47 r0))));
    let u52 : p4726 := (Or.elim h66373 (fun q0 => (False.elim (u48 q0))) (fun r0 => r0));
    let u53 : p4748 := (Or.elim h66376 (fun q0 => (False.elim (u49 q0))) (fun r0 => r0));
    let u54 : p2190 := (Or.elim h7078 (fun q0 => q0) (fun r0 => (False.elim (r0 u50))));
    let u55 : p2911 := (Or.elim h8144 (fun q0 => q0) (fun r0 => (False.elim (r0 u51))));
    let u56 : p3759 := (Or.elim h7663 (fun q0 => q0) (fun r0 => (False.elim (r0 u52))));
    let u57 : p4343 := (Or.elim h7714 (fun q0 => q0) (fun r0 => (False.elim (r0 u53))));
    let u58 : (¬ p3585) := (Or.elim h52009 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u57))) (fun r4 => (False.elim (r4 u5))))))))))));
    let u59 : (¬ p5213) := (Or.elim h8853 (fun q0 => (False.elim (u58 q0))) (fun r0 => r0));
    let u60 : p5215 := (Or.elim h66448 (fun q0 => q0) (fun r0 => (False.elim (u59 r0))));
    let u61 : p3367 := (Or.elim h8859 (fun q0 => q0) (fun r0 => (False.elim (r0 u60))));
    let u62 : (¬ p2352) := (Or.elim h45031 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u61))) (fun r3 => (False.elim (r3 u38))))))))));
    let u63 : (¬ p2459) := (Or.elim h44970 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u55))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u61))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u40))) (fun r3 => (False.elim (r3 u56))))))))));
    let u64 : (¬ p4597) := (Or.elim h7315 (fun q0 => (False.elim (u62 q0))) (fun r0 => r0));
    let u65 : (¬ p4667) := (Or.elim h7487 (fun q0 => (False.elim (u63 q0))) (fun r0 => r0));
    let u66 : p4594 := (Or.elim h66348 (fun q0 => (False.elim (u64 q0))) (fun r0 => r0));
    let u67 : p4665 := (Or.elim h66358 (fun q0 => q0) (fun r0 => (False.elim (u65 r0))));
    let u68 : p3956 := (Or.elim h7309 (fun q0 => q0) (fun r0 => (False.elim (r0 u66))));
    let u69 : p4348 := (Or.elim h7481 (fun q0 => q0) (fun r0 => (False.elim (r0 u67))));
    let u70 : (¬ p4347) := (Or.elim h41157 (fun q0 => (False.elim (q0 u54))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u68))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    let u71 : (¬ p2363) := (Or.elim h43183 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u42))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u35))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u61))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u56))) (fun r4 => (False.elim (r4 u69))))))))))));
    let u72 : (¬ p4600) := (Or.elim h7326 (fun q0 => (False.elim (u70 q0))) (fun r0 => r0));
    let u73 : (¬ p4602) := (Or.elim h7332 (fun q0 => (False.elim (u71 q0))) (fun r0 => r0));
    (Or.elim h66349 (fun q0 => (False.elim (u73 q0))) (fun r0 => (False.elim (u72 r0)))))

theorem step66734 (p2396 p2493 p2496 p2499 p2503 p2553 p2573 p2576 p2579 p2583 p2651 p2654 p2655 p2661 p2727 p2737 p2747 p2749 p2810 p2811 p2946 p2949 p2952 p2956 p2992 p3136 p3365 p3367 p3585 p3759 p4116 p4236 p4315 p4343 p4703 p4704 p4715 p4734 p4748 p4785 p4809 p4812 p5048 p5050 p5213 p5215 : Prop)
    (h7591 : (¬ p4703) ∨ p4704)
    (h7803 : p4236 ∨ (¬ p4785))
    (h3622 : p2737 ∨ (¬ p2747))
    (h3621 : (¬ p2747) ∨ p2749)
    (h7805 : p3365 ∨ (¬ p4785))
    (h53161 : (¬ p2749) ∨ (¬ p2992) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p4734))
    (h8456 : p4315 ∨ (¬ p5048))
    (h66427 : p5048 ∨ p5050)
    (h8462 : p3136 ∨ (¬ p5050))
    (h51323 : (¬ p2737) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4236) ∨ (¬ p4734))
    (h4028 : (¬ p2949) ∨ p2952)
    (h66408 : p2956 ∨ p2949)
    (h4042 : p2946 ∨ (¬ p2956))
    (h7804 : p2811 ∨ (¬ p4785))
    (h7714 : p4343 ∨ (¬ p4748))
    (h7715 : p2810 ∨ (¬ p4748))
    (h52009 : (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4704))
    (h50005 : (¬ p2727) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4734))
    (h3749 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2811))
    (h8853 : p3585 ∨ (¬ p5213))
    (h7863 : p2727 ∨ (¬ p4812))
    (h3449 : p2651 ∨ (¬ p2661))
    (h66448 : p5215 ∨ p5213)
    (h66386 : p4809 ∨ p4812)
    (h66378 : p2654 ∨ p2661)
    (h8859 : p3367 ∨ (¬ p5215))
    (h7856 : p4116 ∨ (¬ p4809))
    (h65966 : (¬ p4809) ∨ (¬ p4703) ∨ (¬ p2499) ∨ (¬ p4715) ∨ (¬ p2992))
    (h3433 : (¬ p2654) ∨ p2655)
    (h46194 : (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3759))
    (h3127 : (¬ p2496) ∨ p2499)
    (h3293 : p2573 ∨ (¬ p2583))
    (h66362 : p2496 ∨ p2503)
    (h66370 : p2576 ∨ p2583)
    (h3141 : p2493 ∨ (¬ p2503))
    (h3279 : (¬ p2576) ∨ p2579)
    (h53224 : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2946) ∨ (¬ p4116) ∨ (¬ p4704))
    : (¬ p4748) ∨ (¬ p3759) ∨ (¬ p2553) ∨ (¬ p2396) ∨ (¬ p4715) ∨ (¬ p4703) ∨ (¬ p4785) ∨ (¬ p2747) ∨ (¬ p4734) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4748 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4703 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4704 := (Or.elim h7591 (fun q0 => (False.elim (q0 u5))) (fun r0 => r0));
    let u11 : p4236 := (Or.elim h7803 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u12 : p2737 := (Or.elim h3622 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u13 : p2749 := (Or.elim h3621 (fun q0 => (False.elim (q0 u7))) (fun r0 => r0));
    let u14 : p3365 := (Or.elim h7805 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u15 : (¬ p4315) := (Or.elim h53161 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u8))))))))));
    let u16 : (¬ p5048) := (Or.elim h8456 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u17 : p5050 := (Or.elim h66427 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    let u18 : p3136 := (Or.elim h8462 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    let u19 : (¬ p2952) := (Or.elim h51323 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u18))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (False.elim (r3 u8))))))))));
    let u20 : (¬ p2949) := (Or.elim h4028 (fun q0 => q0) (fun r0 => (False.elim (u19 r0))));
    let u21 : p2956 := (Or.elim h66408 (fun q0 => q0) (fun r0 => (False.elim (u20 r0))));
    let u22 : p2946 := (Or.elim h4042 (fun q0 => q0) (fun r0 => (False.elim (r0 u21))));
    let u23 : p2811 := (Or.elim h7804 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u24 : p4343 := (Or.elim h7714 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u25 : p2810 := (Or.elim h7715 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u26 : (¬ p3585) := (Or.elim h52009 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u23))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u22))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u24))) (fun r4 => (False.elim (r4 u10))))))))))));
    let u27 : (¬ p2727) := (Or.elim h50005 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u25))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (False.elim (r3 u8))))))))));
    let u28 : (¬ p2651) := (Or.elim h3749 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u25))) (fun r1 => (False.elim (r1 u23))))));
    let u29 : (¬ p5213) := (Or.elim h8853 (fun q0 => (False.elim (u26 q0))) (fun r0 => r0));
    let u30 : (¬ p4812) := (Or.elim h7863 (fun q0 => (False.elim (u27 q0))) (fun r0 => r0));
    let u31 : (¬ p2661) := (Or.elim h3449 (fun q0 => (False.elim (u28 q0))) (fun r0 => r0));
    let u32 : p5215 := (Or.elim h66448 (fun q0 => q0) (fun r0 => (False.elim (u29 r0))));
    let u33 : p4809 := (Or.elim h66386 (fun q0 => q0) (fun r0 => (False.elim (u30 r0))));
    let u34 : p2654 := (Or.elim h66378 (fun q0 => q0) (fun r0 => (False.elim (u31 r0))));
    let u35 : p3367 := (Or.elim h8859 (fun q0 => q0) (fun r0 => (False.elim (r0 u32))));
    let u36 : p4116 := (Or.elim h7856 (fun q0 => q0) (fun r0 => (False.elim (r0 u33))));
    let u37 : (¬ p2499) := (Or.elim h65966 (fun q0 => (False.elim (q0 u33))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u9))))))))));
    let u38 : p2655 := (Or.elim h3433 (fun q0 => (False.elim (q0 u34))) (fun r0 => r0));
    let u39 : (¬ p2573) := (Or.elim h46194 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u35))) (fun r3 => (False.elim (r3 u1))))))))));
    let u40 : (¬ p2496) := (Or.elim h3127 (fun q0 => q0) (fun r0 => (False.elim (u37 r0))));
    let u41 : (¬ p2583) := (Or.elim h3293 (fun q0 => (False.elim (u39 q0))) (fun r0 => r0));
    let u42 : p2503 := (Or.elim h66362 (fun q0 => (False.elim (u40 q0))) (fun r0 => r0));
    let u43 : p2576 := (Or.elim h66370 (fun q0 => q0) (fun r0 => (False.elim (u41 r0))));
    let u44 : p2493 := (Or.elim h3141 (fun q0 => q0) (fun r0 => (False.elim (r0 u42))));
    let u45 : p2579 := (Or.elim h3279 (fun q0 => (False.elim (q0 u43))) (fun r0 => r0));
    (Or.elim h53224 (fun q0 => (False.elim (q0 u44))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u45))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u38))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u22))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u36))) (fun r4 => (False.elim (r4 u10)))))))))))))

theorem step66735 (p2542 p2553 p2630 p2651 p2654 p2657 p2661 p2737 p2797 p2963 p3016 p4195 p4236 p4389 p4715 p4734 p4840 p4844 p4971 p4974 : Prop)
    (h62070 : (¬ p2737) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4236) ∨ (¬ p4734))
    (h7953 : p2797 ∨ (¬ p4844))
    (h66394 : p4844 ∨ p4840)
    (h7947 : p4195 ∨ (¬ p4840))
    (h51929 : (¬ p2553) ∨ (¬ p2630) ∨ (¬ p3016) ∨ (¬ p4195))
    (h42791 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2737) ∨ (¬ p4236) ∨ (¬ p4734))
    (h8280 : p3016 ∨ (¬ p4974))
    (h3435 : (¬ p2654) ∨ p2657)
    (h66415 : p4974 ∨ p4971)
    (h66378 : p2654 ∨ p2661)
    (h8273 : p4389 ∨ (¬ p4971))
    (h3449 : p2651 ∨ (¬ p2661))
    (h49230 : (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p4389) ∨ (¬ p4715))
    : (¬ p2630) ∨ (¬ p2553) ∨ (¬ p2963) ∨ (¬ p4715) ∨ (¬ p2542) ∨ (¬ p4236) ∨ (¬ p2737) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2797) := (Or.elim h62070 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7))))))))));
    let u9 : (¬ p4844) := (Or.elim h7953 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u10 : p4840 := (Or.elim h66394 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u11 : p4195 := (Or.elim h7947 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    let u12 : (¬ p3016) := (Or.elim h51929 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u11))))))));
    let u13 : (¬ p2657) := (Or.elim h42791 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7))))))))));
    let u14 : (¬ p4974) := (Or.elim h8280 (fun q0 => (False.elim (u12 q0))) (fun r0 => r0));
    let u15 : (¬ p2654) := (Or.elim h3435 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u16 : p4971 := (Or.elim h66415 (fun q0 => (False.elim (u14 q0))) (fun r0 => r0));
    let u17 : p2661 := (Or.elim h66378 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u18 : p4389 := (Or.elim h8273 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    let u19 : p2651 := (Or.elim h3449 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    (Or.elim h49230 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u19))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u18))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step66736 (p2274 p2295 p2307 p2331 p2396 p2542 p2553 p2588 p2598 p2630 p2737 p2747 p2749 p2780 p2797 p2811 p2881 p2946 p2949 p2952 p2956 p2963 p2992 p3055 p3136 p3146 p3364 p3365 p3759 p3822 p3872 p3958 p4236 p4315 p4579 p4582 p4703 p4704 p4707 p4709 p4715 p4734 p4748 p4751 p4785 p5048 p5050 p5881 p5882 : Prop)
    (h7591 : (¬ p4703) ∨ p4704)
    (h7590 : p2542 ∨ (¬ p4703))
    (h7803 : p4236 ∨ (¬ p4785))
    (h3622 : p2737 ∨ (¬ p2747))
    (h3621 : (¬ p2747) ∨ p2749)
    (h7805 : p3365 ∨ (¬ p4785))
    (h53161 : (¬ p2749) ∨ (¬ p2992) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p4734))
    (h8456 : p4315 ∨ (¬ p5048))
    (h66427 : p5048 ∨ p5050)
    (h8462 : p3136 ∨ (¬ p5050))
    (h51323 : (¬ p2737) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4236) ∨ (¬ p4734))
    (h4028 : (¬ p2949) ∨ p2952)
    (h66408 : p2956 ∨ p2949)
    (h4042 : p2946 ∨ (¬ p2956))
    (h7804 : p2811 ∨ (¬ p4785))
    (h45486 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p2737) ∨ (¬ p2811))
    (h7281 : p2331 ∨ (¬ p4582))
    (h66346 : p4579 ∨ p4582)
    (h7275 : p2963 ∨ (¬ p4579))
    (h62070 : (¬ p2737) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4236) ∨ (¬ p4734))
    (h66733 : (¬ p2588) ∨ p2797 ∨ (¬ p2295) ∨ (¬ p3146) ∨ (¬ p3958) ∨ (¬ p4704) ∨ (¬ p3872) ∨ (¬ p2274) ∨ p3822 ∨ (¬ p2780) ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p2811) ∨ (¬ p2737) ∨ (¬ p2307))
    (h7601 : p2588 ∨ (¬ p4707))
    (h66368 : p4709 ∨ p4707)
    (h7607 : p2553 ∨ (¬ p4709))
    (h66735 : (¬ p2630) ∨ (¬ p2553) ∨ (¬ p2963) ∨ (¬ p4715) ∨ (¬ p2542) ∨ (¬ p4236) ∨ (¬ p2737) ∨ (¬ p4734))
    (h7721 : p2630 ∨ (¬ p4751))
    (h66376 : p4751 ∨ p4748)
    (h7713 : p3364 ∨ (¬ p4748))
    (h66734 : (¬ p4748) ∨ (¬ p3759) ∨ (¬ p2553) ∨ (¬ p2396) ∨ (¬ p4715) ∨ (¬ p4703) ∨ (¬ p4785) ∨ (¬ p2747) ∨ (¬ p4734) ∨ (¬ p2992))
    (h6408 : p3055 ∨ (¬ p3364) ∨ (¬ p3365))
    (h12278 : p3759 ∨ p5881)
    (h9095 : (¬ p2598) ∨ (¬ p3055))
    (h66535 : (¬ p5882) ∨ (¬ p5881))
    (h12280 : p2598 ∨ p5882)
    : (¬ p2295) ∨ (¬ p2396) ∨ (¬ p3146) ∨ (¬ p3958) ∨ (¬ p4715) ∨ (¬ p4703) ∨ (¬ p3872) ∨ (¬ p2274) ∨ p3822 ∨ (¬ p2780) ∨ (¬ p2881) ∨ (¬ p4785) ∨ (¬ p2747) ∨ (¬ p4734) ∨ (¬ p2307) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4703 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3822) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))));
    let u16 : p4704 := (Or.elim h7591 (fun q0 => (False.elim (q0 u5))) (fun r0 => r0));
    let u17 : p2542 := (Or.elim h7590 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u18 : p4236 := (Or.elim h7803 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    let u19 : p2737 := (Or.elim h3622 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u20 : p2749 := (Or.elim h3621 (fun q0 => (False.elim (q0 u12))) (fun r0 => r0));
    let u21 : p3365 := (Or.elim h7805 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    let u22 : (¬ p4315) := (Or.elim h53161 (fun q0 => (False.elim (q0 u20))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u15))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u21))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u13))))))))));
    let u23 : (¬ p5048) := (Or.elim h8456 (fun q0 => (False.elim (u22 q0))) (fun r0 => r0));
    let u24 : p5050 := (Or.elim h66427 (fun q0 => (False.elim (u23 q0))) (fun r0 => r0));
    let u25 : p3136 := (Or.elim h8462 (fun q0 => q0) (fun r0 => (False.elim (r0 u24))));
    let u26 : (¬ p2952) := (Or.elim h51323 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u25))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u18))) (fun r3 => (False.elim (r3 u13))))))))));
    let u27 : (¬ p2949) := (Or.elim h4028 (fun q0 => q0) (fun r0 => (False.elim (u26 r0))));
    let u28 : p2956 := (Or.elim h66408 (fun q0 => q0) (fun r0 => (False.elim (u27 r0))));
    let u29 : p2946 := (Or.elim h4042 (fun q0 => q0) (fun r0 => (False.elim (r0 u28))));
    let u30 : p2811 := (Or.elim h7804 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    let u31 : (¬ p2331) := (Or.elim h45486 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u19))) (fun r3 => (False.elim (r3 u30))))))))));
    let u32 : (¬ p4582) := (Or.elim h7281 (fun q0 => (False.elim (u31 q0))) (fun r0 => r0));
    let u33 : p4579 := (Or.elim h66346 (fun q0 => q0) (fun r0 => (False.elim (u32 r0))));
    let u34 : p2963 := (Or.elim h7275 (fun q0 => q0) (fun r0 => (False.elim (r0 u33))));
    let u35 : (¬ p2797) := (Or.elim h62070 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u34))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u18))) (fun r3 => (False.elim (r3 u13))))))))));
    let u36 : (¬ p2588) := (Or.elim h66733 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u35 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u16))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u8 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u29))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u30))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u19))) (fun r13 => (False.elim (r13 u14))))))))))))))))))))))))))))));
    let u37 : (¬ p4707) := (Or.elim h7601 (fun q0 => (False.elim (u36 q0))) (fun r0 => r0));
    let u38 : p4709 := (Or.elim h66368 (fun q0 => q0) (fun r0 => (False.elim (u37 r0))));
    let u39 : p2553 := (Or.elim h7607 (fun q0 => q0) (fun r0 => (False.elim (r0 u38))));
    let u40 : (¬ p2630) := (Or.elim h66735 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u39))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u34))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u17))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u18))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u19))) (fun r6 => (False.elim (r6 u13))))))))))))))));
    let u41 : (¬ p4751) := (Or.elim h7721 (fun q0 => (False.elim (u40 q0))) (fun r0 => r0));
    let u42 : p4748 := (Or.elim h66376 (fun q0 => (False.elim (u41 q0))) (fun r0 => r0));
    let u43 : p3364 := (Or.elim h7713 (fun q0 => q0) (fun r0 => (False.elim (r0 u42))));
    let u44 : (¬ p3759) := (Or.elim h66734 (fun q0 => (False.elim (q0 u42))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u39))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (False.elim (r8 u15))))))))))))))))))));
    let u45 : p3055 := (Or.elim h6408 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u43))) (fun r1 => (False.elim (r1 u21))))));
    let u46 : p5881 := (Or.elim h12278 (fun q0 => (False.elim (u44 q0))) (fun r0 => r0));
    let u47 : (¬ p2598) := (Or.elim h9095 (fun q0 => q0) (fun r0 => (False.elim (r0 u45))));
    let u48 : (¬ p5882) := (Or.elim h66535 (fun q0 => q0) (fun r0 => (False.elim (r0 u46))));
    (Or.elim h12280 (fun q0 => (False.elim (u47 q0))) (fun r0 => (False.elim (u48 r0)))))

theorem step66737 (p2122 p2138 p2177 p2190 p2274 p2295 p2299 p2307 p2363 p2396 p2459 p2532 p2533 p2619 p2668 p2737 p2743 p2747 p2749 p2761 p2779 p2780 p2811 p2829 p2881 p2946 p2949 p2952 p2956 p2963 p2972 p2992 p3073 p3105 p3136 p3146 p3266 p3309 p3324 p3325 p3365 p3371 p3547 p3548 p3549 p3568 p3583 p3657 p3680 p3694 p3758 p3791 p3822 p3872 p3923 p3941 p3958 p3987 p3989 p4075 p4189 p4236 p4243 p4260 p4313 p4315 p4318 p4319 p4322 p4337 p4347 p4348 p4363 p4381 p4385 p4426 p4442 p4444 p4452 p4470 p4474 p4500 p4502 p4503 p4505 p4508 p4564 p4568 p4571 p4579 p4582 p4600 p4602 p4665 p4667 p4703 p4715 p4734 p4739 p4743 p4755 p4758 p4761 p4768 p4772 p4785 p4822 p4826 p4827 p4840 p4844 p4873 p4876 p4903 p4905 p4937 p4941 p4992 p4996 p5024 p5029 p5048 p5050 p5057 p5115 p5120 p5140 p5143 p5304 p5306 p5396 p5401 p5469 p5474 p5555 p5559 p5561 p5643 p5648 : Prop)
    (h8479 : p3146 ∨ (¬ p5057))
    (h8478 : p2533 ∨ (¬ p5057))
    (h8477 : p2532 ∨ (¬ p5057))
    (h8705 : p3549 ∨ (¬ p5140))
    (h66440 : p5140 ∨ p5143)
    (h8710 : p4452 ∨ (¬ p5143))
    (h8709 : p3547 ∨ (¬ p5143))
    (h5636 : (¬ p2307) ∨ (¬ p2779) ∨ (¬ p3822))
    (h6984 : p3822 ∨ (¬ p4470))
    (h66324 : p4474 ∨ p4470)
    (h6990 : p2122 ∨ (¬ p4474))
    (h8094 : (¬ p4903) ∨ p4905)
    (h8092 : p2881 ∨ (¬ p4903))
    (h7803 : p4236 ∨ (¬ p4785))
    (h3622 : p2737 ∨ (¬ p2747))
    (h3621 : (¬ p2747) ∨ p2749)
    (h7805 : p3365 ∨ (¬ p4785))
    (h53161 : (¬ p2749) ∨ (¬ p2992) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p4734))
    (h8456 : p4315 ∨ (¬ p5048))
    (h66427 : p5048 ∨ p5050)
    (h8462 : p3136 ∨ (¬ p5050))
    (h51323 : (¬ p2737) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4236) ∨ (¬ p4734))
    (h4028 : (¬ p2949) ∨ p2952)
    (h66408 : p2956 ∨ p2949)
    (h4042 : p2946 ∨ (¬ p2956))
    (h10031 : (¬ p2737) ∨ (¬ p2743))
    (h8461 : p4313 ∨ (¬ p5050))
    (h29019 : p2743 ∨ (¬ p3583) ∨ (¬ p4313))
    (h8017 : p3583 ∨ (¬ p4873))
    (h66397 : p4873 ∨ p4876)
    (h8021 : p4243 ∨ (¬ p4876))
    (h7804 : p2811 ∨ (¬ p4785))
    (h66736 : (¬ p2295) ∨ (¬ p2396) ∨ (¬ p3146) ∨ (¬ p3958) ∨ (¬ p4715) ∨ (¬ p4703) ∨ (¬ p3872) ∨ (¬ p2274) ∨ p3822 ∨ (¬ p2780) ∨ (¬ p2881) ∨ (¬ p4785) ∨ (¬ p2747) ∨ (¬ p4734) ∨ (¬ p2307) ∨ (¬ p2992))
    (h7243 : p2295 ∨ (¬ p4571))
    (h16173 : p2295 ∨ (¬ p3309) ∨ (¬ p4319))
    (h66342 : p4571 ∨ p4568)
    (h7732 : p4319 ∨ (¬ p4755))
    (h7237 : p3568 ∨ (¬ p4568))
    (h66377 : p4758 ∨ p4755)
    (h41403 : (¬ p2299) ∨ (¬ p2881) ∨ (¬ p3568) ∨ (¬ p3872) ∨ (¬ p4564))
    (h17602 : (¬ p3568) ∨ p3822 ∨ (¬ p4337))
    (h45307 : (¬ p2274) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3568))
    (h7741 : (¬ p4758) ∨ p4761)
    (h7056 : p2299 ∨ (¬ p4500))
    (h7946 : p4337 ∨ (¬ p4840))
    (h7275 : p2963 ∨ (¬ p4579))
    (h66330 : p4502 ∨ p4500)
    (h66394 : p4844 ∨ p4840)
    (h66346 : p4579 ∨ p4582)
    (h7061 : p3325 ∨ (¬ p4502))
    (h7062 : p2177 ∨ (¬ p4502))
    (h7064 : (¬ p4502) ∨ p4503)
    (h7952 : p4426 ∨ (¬ p4844))
    (h7280 : p3987 ∨ (¬ p4582))
    (h20380 : (¬ p2274) ∨ (¬ p3325) ∨ (¬ p3989))
    (h6935 : (¬ p3325) ∨ p3549 ∨ (¬ p3923))
    (h5166 : (¬ p2177) ∨ (¬ p3547) ∨ (¬ p3548))
    (h6835 : (¬ p2737) ∨ p2829 ∨ (¬ p4426))
    (h64504 : (¬ p2307) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2779) ∨ (¬ p3568) ∨ (¬ p4426))
    (h7073 : p3989 ∨ (¬ p4505))
    (h8334 : p3923 ∨ (¬ p4992))
    (h9038 : p3548 ∨ (¬ p5304))
    (h46120 : (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2779) ∨ (¬ p2829))
    (h46850 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2459) ∨ (¬ p2829))
    (h46848 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2829) ∨ (¬ p3941))
    (h7777 : p2668 ∨ (¬ p4772))
    (h66331 : p4508 ∨ p4505)
    (h66420 : p4992 ∨ p4996)
    (h66458 : p5304 ∨ p5306)
    (h7908 : p2761 ∨ (¬ p4827))
    (h7487 : p2459 ∨ (¬ p4667))
    (h9727 : p3941 ∨ (¬ p5561))
    (h66381 : p4772 ∨ p4768)
    (h7078 : p2190 ∨ (¬ p4508))
    (h8338 : p4318 ∨ (¬ p4996))
    (h9043 : p4189 ∨ (¬ p5306))
    (h66390 : p4827 ∨ p4822)
    (h66358 : p4665 ∨ p4667)
    (h66484 : p5555 ∨ p5561)
    (h7771 : p3324 ∨ (¬ p4768))
    (h7902 : p4381 ∨ (¬ p4822))
    (h7904 : (¬ p4822) ∨ p4826)
    (h7479 : p3657 ∨ (¬ p4665))
    (h7481 : p4348 ∨ (¬ p4665))
    (h9722 : (¬ p5555) ∨ p5559)
    (h55133 : (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3324) ∨ (¬ p4347) ∨ (¬ p4564))
    (h54461 : (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3758) ∨ (¬ p4348))
    (h7326 : p4347 ∨ (¬ p4600))
    (h7704 : p2619 ∨ (¬ p4743))
    (h66349 : p4602 ∨ p4600)
    (h66375 : p4739 ∨ p4743)
    (h7332 : p2363 ∨ (¬ p4602))
    (h7698 : p3694 ∨ (¬ p4739))
    (h21751 : (¬ p2363) ∨ p3073 ∨ (¬ p4318))
    (h41140 : (¬ p2363) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4503))
    (h54699 : (¬ p2532) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4348) ∨ (¬ p4905))
    (h53989 : (¬ p3073) ∨ (¬ p4189) ∨ (¬ p4348) ∨ (¬ p4442) ∨ (¬ p5559))
    (h8652 : p3266 ∨ (¬ p5120))
    (h8411 : p3105 ∨ (¬ p5029))
    (h10001 : p4442 ∨ (¬ p5643))
    (h66438 : p5115 ∨ p5120)
    (h66424 : p5024 ∨ p5029)
    (h66492 : p5643 ∨ p5648)
    (h8646 : p4444 ∨ (¬ p5115))
    (h8405 : p4385 ∨ (¬ p5024))
    (h10007 : p4075 ∨ (¬ p5648))
    (h41740 : (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p4905))
    (h55011 : (¬ p2138) ∨ (¬ p2972) ∨ (¬ p3371) ∨ (¬ p4385) ∨ (¬ p4734))
    (h42554 : (¬ p3568) ∨ (¬ p4075) ∨ (¬ p4260) ∨ (¬ p4452) ∨ (¬ p4761))
    (h9314 : p3680 ∨ (¬ p5401))
    (h8212 : p2972 ∨ (¬ p4941))
    (h9481 : p4260 ∨ (¬ p5469))
    (h66468 : p5396 ∨ p5401)
    (h66411 : p4937 ∨ p4941)
    (h66477 : p5469 ∨ p5474)
    (h9308 : p4322 ∨ (¬ p5396))
    (h8206 : p4363 ∨ (¬ p4937))
    (h9487 : p3791 ∨ (¬ p5474))
    (h56274 : (¬ p2138) ∨ (¬ p2307) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3791) ∨ (¬ p3987) ∨ (¬ p4243) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p4734) ∨ (¬ p4826))
    : (¬ p2396) ∨ (¬ p5057) ∨ (¬ p3958) ∨ (¬ p4715) ∨ (¬ p4703) ∨ (¬ p3309) ∨ p3549 ∨ (¬ p3872) ∨ (¬ p2274) ∨ (¬ p2779) ∨ (¬ p2780) ∨ (¬ p3758) ∨ (¬ p4903) ∨ (¬ p2138) ∨ (¬ p4785) ∨ (¬ p3371) ∨ (¬ p2747) ∨ (¬ p4734) ∨ (¬ p2307) ∨ (¬ p4564) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5057 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4703 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3549) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4903 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p4785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))));
    let u21 : p3146 := (Or.elim h8479 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u22 : p2533 := (Or.elim h8478 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u23 : p2532 := (Or.elim h8477 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u24 : (¬ p5140) := (Or.elim h8705 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    let u25 : p5143 := (Or.elim h66440 (fun q0 => (False.elim (u24 q0))) (fun r0 => r0));
    let u26 : p4452 := (Or.elim h8710 (fun q0 => q0) (fun r0 => (False.elim (r0 u25))));
    let u27 : p3547 := (Or.elim h8709 (fun q0 => q0) (fun r0 => (False.elim (r0 u25))));
    let u28 : (¬ p3822) := (Or.elim h5636 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => r1))));
    let u29 : (¬ p4470) := (Or.elim h6984 (fun q0 => (False.elim (u28 q0))) (fun r0 => r0));
    let u30 : p4474 := (Or.elim h66324 (fun q0 => q0) (fun r0 => (False.elim (u29 r0))));
    let u31 : p2122 := (Or.elim h6990 (fun q0 => q0) (fun r0 => (False.elim (r0 u30))));
    let u32 : p4905 := (Or.elim h8094 (fun q0 => (False.elim (q0 u12))) (fun r0 => r0));
    let u33 : p2881 := (Or.elim h8092 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u34 : p4236 := (Or.elim h7803 (fun q0 => q0) (fun r0 => (False.elim (r0 u14))));
    let u35 : p2737 := (Or.elim h3622 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    let u36 : p2749 := (Or.elim h3621 (fun q0 => (False.elim (q0 u16))) (fun r0 => r0));
    let u37 : p3365 := (Or.elim h7805 (fun q0 => q0) (fun r0 => (False.elim (r0 u14))));
    let u38 : (¬ p4315) := (Or.elim h53161 (fun q0 => (False.elim (q0 u36))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u20))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u37))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u17))))))))));
    let u39 : (¬ p5048) := (Or.elim h8456 (fun q0 => (False.elim (u38 q0))) (fun r0 => r0));
    let u40 : p5050 := (Or.elim h66427 (fun q0 => (False.elim (u39 q0))) (fun r0 => r0));
    let u41 : p3136 := (Or.elim h8462 (fun q0 => q0) (fun r0 => (False.elim (r0 u40))));
    let u42 : (¬ p2952) := (Or.elim h51323 (fun q0 => (False.elim (q0 u35))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u41))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u34))) (fun r3 => (False.elim (r3 u17))))))))));
    let u43 : (¬ p2949) := (Or.elim h4028 (fun q0 => q0) (fun r0 => (False.elim (u42 r0))));
    let u44 : p2956 := (Or.elim h66408 (fun q0 => q0) (fun r0 => (False.elim (u43 r0))));
    let u45 : p2946 := (Or.elim h4042 (fun q0 => q0) (fun r0 => (False.elim (r0 u44))));
    let u46 : (¬ p2743) := (Or.elim h10031 (fun q0 => (False.elim (q0 u35))) (fun r0 => r0));
    let u47 : p4313 := (Or.elim h8461 (fun q0 => q0) (fun r0 => (False.elim (r0 u40))));
    let u48 : (¬ p3583) := (Or.elim h29019 (fun q0 => (False.elim (u46 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u47))))));
    let u49 : (¬ p4873) := (Or.elim h8017 (fun q0 => (False.elim (u48 q0))) (fun r0 => r0));
    let u50 : p4876 := (Or.elim h66397 (fun q0 => (False.elim (u49 q0))) (fun r0 => r0));
    let u51 : p4243 := (Or.elim h8021 (fun q0 => q0) (fun r0 => (False.elim (r0 u50))));
    let u52 : p2811 := (Or.elim h7804 (fun q0 => q0) (fun r0 => (False.elim (r0 u14))));
    let u53 : (¬ p2295) := (Or.elim h66736 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u21))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u28 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u33))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u14))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u16))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u17))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u18))) (fun r14 => (False.elim (r14 u20))))))))))))))))))))))))))))))));
    let u54 : (¬ p4571) := (Or.elim h7243 (fun q0 => (False.elim (u53 q0))) (fun r0 => r0));
    let u55 : (¬ p4319) := (Or.elim h16173 (fun q0 => (False.elim (u53 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => r1))));
    let u56 : p4568 := (Or.elim h66342 (fun q0 => (False.elim (u54 q0))) (fun r0 => r0));
    let u57 : (¬ p4755) := (Or.elim h7732 (fun q0 => (False.elim (u55 q0))) (fun r0 => r0));
    let u58 : p3568 := (Or.elim h7237 (fun q0 => q0) (fun r0 => (False.elim (r0 u56))));
    let u59 : p4758 := (Or.elim h66377 (fun q0 => q0) (fun r0 => (False.elim (u57 r0))));
    let u60 : (¬ p2299) := (Or.elim h41403 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u33))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u58))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u19))))))))));
    let u61 : (¬ p4337) := (Or.elim h17602 (fun q0 => (False.elim (q0 u58))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u28 q1))) (fun r1 => r1))));
    let u62 : (¬ p2963) := (Or.elim h45307 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u45))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u58))))))));
    let u63 : p4761 := (Or.elim h7741 (fun q0 => (False.elim (q0 u59))) (fun r0 => r0));
    let u64 : (¬ p4500) := (Or.elim h7056 (fun q0 => (False.elim (u60 q0))) (fun r0 => r0));
    let u65 : (¬ p4840) := (Or.elim h7946 (fun q0 => (False.elim (u61 q0))) (fun r0 => r0));
    let u66 : (¬ p4579) := (Or.elim h7275 (fun q0 => (False.elim (u62 q0))) (fun r0 => r0));
    let u67 : p4502 := (Or.elim h66330 (fun q0 => q0) (fun r0 => (False.elim (u64 r0))));
    let u68 : p4844 := (Or.elim h66394 (fun q0 => q0) (fun r0 => (False.elim (u65 r0))));
    let u69 : p4582 := (Or.elim h66346 (fun q0 => (False.elim (u66 q0))) (fun r0 => r0));
    let u70 : p3325 := (Or.elim h7061 (fun q0 => q0) (fun r0 => (False.elim (r0 u67))));
    let u71 : p2177 := (Or.elim h7062 (fun q0 => q0) (fun r0 => (False.elim (r0 u67))));
    let u72 : p4503 := (Or.elim h7064 (fun q0 => (False.elim (q0 u67))) (fun r0 => r0));
    let u73 : p4426 := (Or.elim h7952 (fun q0 => q0) (fun r0 => (False.elim (r0 u68))));
    let u74 : p3987 := (Or.elim h7280 (fun q0 => q0) (fun r0 => (False.elim (r0 u69))));
    let u75 : (¬ p3989) := (Or.elim h20380 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u70))) (fun r1 => r1))));
    let u76 : (¬ p3923) := (Or.elim h6935 (fun q0 => (False.elim (q0 u70))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => r1))));
    let u77 : (¬ p3548) := (Or.elim h5166 (fun q0 => (False.elim (q0 u71))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u27))) (fun r1 => r1))));
    let u78 : p2829 := (Or.elim h6835 (fun q0 => (False.elim (q0 u35))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u73))))));
    let u79 : (¬ p2668) := (Or.elim h64504 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u35))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u58))) (fun r4 => (False.elim (r4 u73))))))))))));
    let u80 : (¬ p4505) := (Or.elim h7073 (fun q0 => (False.elim (u75 q0))) (fun r0 => r0));
    let u81 : (¬ p4992) := (Or.elim h8334 (fun q0 => (False.elim (u76 q0))) (fun r0 => r0));
    let u82 : (¬ p5304) := (Or.elim h9038 (fun q0 => (False.elim (u77 q0))) (fun r0 => r0));
    let u83 : (¬ p2761) := (Or.elim h46120 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (False.elim (r3 u78))))))))));
    let u84 : (¬ p2459) := (Or.elim h46850 (fun q0 => (False.elim (q0 u31))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u71))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u78))))))));
    let u85 : (¬ p3941) := (Or.elim h46848 (fun q0 => (False.elim (q0 u31))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u71))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u78))) (fun r2 => r2))))));
    let u86 : (¬ p4772) := (Or.elim h7777 (fun q0 => (False.elim (u79 q0))) (fun r0 => r0));
    let u87 : p4508 := (Or.elim h66331 (fun q0 => q0) (fun r0 => (False.elim (u80 r0))));
    let u88 : p4996 := (Or.elim h66420 (fun q0 => (False.elim (u81 q0))) (fun r0 => r0));
    let u89 : p5306 := (Or.elim h66458 (fun q0 => (False.elim (u82 q0))) (fun r0 => r0));
    let u90 : (¬ p4827) := (Or.elim h7908 (fun q0 => (False.elim (u83 q0))) (fun r0 => r0));
    let u91 : (¬ p4667) := (Or.elim h7487 (fun q0 => (False.elim (u84 q0))) (fun r0 => r0));
    let u92 : (¬ p5561) := (Or.elim h9727 (fun q0 => (False.elim (u85 q0))) (fun r0 => r0));
    let u93 : p4768 := (Or.elim h66381 (fun q0 => (False.elim (u86 q0))) (fun r0 => r0));
    let u94 : p2190 := (Or.elim h7078 (fun q0 => q0) (fun r0 => (False.elim (r0 u87))));
    let u95 : p4318 := (Or.elim h8338 (fun q0 => q0) (fun r0 => (False.elim (r0 u88))));
    let u96 : p4189 := (Or.elim h9043 (fun q0 => q0) (fun r0 => (False.elim (r0 u89))));
    let u97 : p4822 := (Or.elim h66390 (fun q0 => (False.elim (u90 q0))) (fun r0 => r0));
    let u98 : p4665 := (Or.elim h66358 (fun q0 => q0) (fun r0 => (False.elim (u91 r0))));
    let u99 : p5555 := (Or.elim h66484 (fun q0 => q0) (fun r0 => (False.elim (u92 r0))));
    let u100 : p3324 := (Or.elim h7771 (fun q0 => q0) (fun r0 => (False.elim (r0 u93))));
    let u101 : p4381 := (Or.elim h7902 (fun q0 => q0) (fun r0 => (False.elim (r0 u97))));
    let u102 : p4826 := (Or.elim h7904 (fun q0 => (False.elim (q0 u97))) (fun r0 => r0));
    let u103 : p3657 := (Or.elim h7479 (fun q0 => q0) (fun r0 => (False.elim (r0 u98))));
    let u104 : p4348 := (Or.elim h7481 (fun q0 => q0) (fun r0 => (False.elim (r0 u98))));
    let u105 : p5559 := (Or.elim h9722 (fun q0 => (False.elim (q0 u99))) (fun r0 => r0));
    let u106 : (¬ p4347) := (Or.elim h55133 (fun q0 => (False.elim (q0 u94))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u21))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u100))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u19))))))))));
    let u107 : (¬ p2619) := (Or.elim h54461 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u21))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (False.elim (r2 u104))))))));
    let u108 : (¬ p4600) := (Or.elim h7326 (fun q0 => (False.elim (u106 q0))) (fun r0 => r0));
    let u109 : (¬ p4743) := (Or.elim h7704 (fun q0 => (False.elim (u107 q0))) (fun r0 => r0));
    let u110 : p4602 := (Or.elim h66349 (fun q0 => q0) (fun r0 => (False.elim (u108 r0))));
    let u111 : p4739 := (Or.elim h66375 (fun q0 => q0) (fun r0 => (False.elim (u109 r0))));
    let u112 : p2363 := (Or.elim h7332 (fun q0 => q0) (fun r0 => (False.elim (r0 u110))));
    let u113 : p3694 := (Or.elim h7698 (fun q0 => q0) (fun r0 => (False.elim (r0 u111))));
    let u114 : p3073 := (Or.elim h21751 (fun q0 => (False.elim (q0 u112))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u95))))));
    let u115 : (¬ p3266) := (Or.elim h41140 (fun q0 => (False.elim (q0 u112))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u103))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u101))) (fun r3 => (False.elim (r3 u72))))))))));
    let u116 : (¬ p3105) := (Or.elim h54699 (fun q0 => (False.elim (q0 u23))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u113))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u104))) (fun r3 => (False.elim (r3 u32))))))))));
    let u117 : (¬ p4442) := (Or.elim h53989 (fun q0 => (False.elim (q0 u114))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u96))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u104))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u105))))))))));
    let u118 : (¬ p5120) := (Or.elim h8652 (fun q0 => (False.elim (u115 q0))) (fun r0 => r0));
    let u119 : (¬ p5029) := (Or.elim h8411 (fun q0 => (False.elim (u116 q0))) (fun r0 => r0));
    let u120 : (¬ p5643) := (Or.elim h10001 (fun q0 => (False.elim (u117 q0))) (fun r0 => r0));
    let u121 : p5115 := (Or.elim h66438 (fun q0 => q0) (fun r0 => (False.elim (u118 r0))));
    let u122 : p5024 := (Or.elim h66424 (fun q0 => q0) (fun r0 => (False.elim (u119 r0))));
    let u123 : p5648 := (Or.elim h66492 (fun q0 => (False.elim (u120 q0))) (fun r0 => r0));
    let u124 : p4444 := (Or.elim h8646 (fun q0 => q0) (fun r0 => (False.elim (r0 u121))));
    let u125 : p4385 := (Or.elim h8405 (fun q0 => q0) (fun r0 => (False.elim (r0 u122))));
    let u126 : p4075 := (Or.elim h10007 (fun q0 => q0) (fun r0 => (False.elim (r0 u123))));
    let u127 : (¬ p3680) := (Or.elim h41740 (fun q0 => (False.elim (q0 u22))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u104))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u124))) (fun r3 => (False.elim (r3 u32))))))))));
    let u128 : (¬ p2972) := (Or.elim h55011 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u125))) (fun r3 => (False.elim (r3 u17))))))))));
    let u129 : (¬ p4260) := (Or.elim h42554 (fun q0 => (False.elim (q0 u58))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u126))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u26))) (fun r3 => (False.elim (r3 u63))))))))));
    let u130 : (¬ p5401) := (Or.elim h9314 (fun q0 => (False.elim (u127 q0))) (fun r0 => r0));
    let u131 : (¬ p4941) := (Or.elim h8212 (fun q0 => (False.elim (u128 q0))) (fun r0 => r0));
    let u132 : (¬ p5469) := (Or.elim h9481 (fun q0 => (False.elim (u129 q0))) (fun r0 => r0));
    let u133 : p5396 := (Or.elim h66468 (fun q0 => q0) (fun r0 => (False.elim (u130 r0))));
    let u134 : p4937 := (Or.elim h66411 (fun q0 => q0) (fun r0 => (False.elim (u131 r0))));
    let u135 : p5474 := (Or.elim h66477 (fun q0 => (False.elim (u132 q0))) (fun r0 => r0));
    let u136 : p4322 := (Or.elim h9308 (fun q0 => q0) (fun r0 => (False.elim (r0 u133))));
    let u137 : p4363 := (Or.elim h8206 (fun q0 => q0) (fun r0 => (False.elim (r0 u134))));
    let u138 : p3791 := (Or.elim h9487 (fun q0 => q0) (fun r0 => (False.elim (r0 u135))));
    (Or.elim h56274 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u18))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u35))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u52))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u138))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u74))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u51))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u136))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u137))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u17))) (fun r9 => (False.elim (r9 u102)))))))))))))))))))))))

theorem step66738 (p2138 p2177 p2274 p2295 p2299 p2307 p2331 p2352 p2363 p2396 p2459 p2493 p2496 p2499 p2503 p2542 p2553 p2573 p2576 p2579 p2583 p2588 p2598 p2630 p2651 p2654 p2655 p2661 p2668 p2727 p2737 p2747 p2749 p2779 p2780 p2810 p2811 p2881 p2946 p2949 p2952 p2956 p2963 p2992 p3055 p3136 p3146 p3309 p3324 p3364 p3365 p3367 p3371 p3549 p3568 p3585 p3758 p3759 p3872 p3945 p3955 p3956 p3958 p4107 p4116 p4138 p4236 p4315 p4343 p4347 p4500 p4502 p4559 p4564 p4568 p4571 p4579 p4582 p4594 p4597 p4600 p4602 p4619 p4622 p4665 p4667 p4703 p4704 p4707 p4709 p4715 p4726 p4728 p4734 p4748 p4751 p4768 p4772 p4785 p4809 p4812 p4903 p5048 p5050 p5057 p5213 p5215 : Prop)
    (h7591 : (¬ p4703) ∨ p4704)
    (h7590 : p2542 ∨ (¬ p4703))
    (h8092 : p2881 ∨ (¬ p4903))
    (h65788 : p4559 ∨ (¬ p2881))
    (h7803 : p4236 ∨ (¬ p4785))
    (h3622 : p2737 ∨ (¬ p2747))
    (h3621 : (¬ p2747) ∨ p2749)
    (h7805 : p3365 ∨ (¬ p4785))
    (h53161 : (¬ p2749) ∨ (¬ p2992) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p4734))
    (h8456 : p4315 ∨ (¬ p5048))
    (h66427 : p5048 ∨ p5050)
    (h8462 : p3136 ∨ (¬ p5050))
    (h51323 : (¬ p2737) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4236) ∨ (¬ p4734))
    (h4028 : (¬ p2949) ∨ p2952)
    (h66408 : p2956 ∨ p2949)
    (h4042 : p2946 ∨ (¬ p2956))
    (h7804 : p2811 ∨ (¬ p4785))
    (h8479 : p3146 ∨ (¬ p5057))
    (h66737 : (¬ p2396) ∨ (¬ p5057) ∨ (¬ p3958) ∨ (¬ p4715) ∨ (¬ p4703) ∨ (¬ p3309) ∨ p3549 ∨ (¬ p3872) ∨ (¬ p2274) ∨ (¬ p2779) ∨ (¬ p2780) ∨ (¬ p3758) ∨ (¬ p4903) ∨ (¬ p2138) ∨ (¬ p4785) ∨ (¬ p3371) ∨ (¬ p2747) ∨ (¬ p4734) ∨ (¬ p2307) ∨ (¬ p4564) ∨ (¬ p2992))
    (h7384 : p2396 ∨ (¬ p4622))
    (h66352 : p4619 ∨ p4622)
    (h7378 : p4107 ∨ (¬ p4619))
    (h65751 : (¬ p4665) ∨ (¬ p3146) ∨ (¬ p4903) ∨ (¬ p4107) ∨ (¬ p4559))
    (h66358 : p4665 ∨ p4667)
    (h7486 : p3945 ∨ (¬ p4667))
    (h7487 : p2459 ∨ (¬ p4667))
    (h20089 : (¬ p2177) ∨ (¬ p3945) ∨ (¬ p4107))
    (h24089 : p2299 ∨ (¬ p3945) ∨ (¬ p4107))
    (h7062 : p2177 ∨ (¬ p4502))
    (h51714 : (¬ p2299) ∨ (¬ p2588) ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p3958))
    (h41403 : (¬ p2299) ∨ (¬ p2881) ∨ (¬ p3568) ∨ (¬ p3872) ∨ (¬ p4564))
    (h66330 : p4502 ∨ p4500)
    (h7601 : p2588 ∨ (¬ p4707))
    (h7237 : p3568 ∨ (¬ p4568))
    (h7054 : p3955 ∨ (¬ p4500))
    (h7055 : p4138 ∨ (¬ p4500))
    (h66368 : p4709 ∨ p4707)
    (h66342 : p4571 ∨ p4568)
    (h41812 : (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p4559))
    (h7607 : p2553 ∨ (¬ p4709))
    (h7243 : p2295 ∨ (¬ p4571))
    (h7326 : p4347 ∨ (¬ p4600))
    (h41813 : (¬ p2553) ∨ (¬ p2881) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4559))
    (h48283 : (¬ p2295) ∨ (¬ p2881) ∨ (¬ p3324) ∨ (¬ p4138) ∨ (¬ p4559))
    (h66349 : p4602 ∨ p4600)
    (h7309 : p3956 ∨ (¬ p4594))
    (h7771 : p3324 ∨ (¬ p4768))
    (h7332 : p2363 ∨ (¬ p4602))
    (h66348 : p4597 ∨ p4594)
    (h66381 : p4772 ∨ p4768)
    (h7315 : p2352 ∨ (¬ p4597))
    (h7777 : p2668 ∨ (¬ p4772))
    (h45524 : (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2811))
    (h7281 : p2331 ∨ (¬ p4582))
    (h66346 : p4579 ∨ p4582)
    (h7275 : p2963 ∨ (¬ p4579))
    (h66735 : (¬ p2630) ∨ (¬ p2553) ∨ (¬ p2963) ∨ (¬ p4715) ∨ (¬ p2542) ∨ (¬ p4236) ∨ (¬ p2737) ∨ (¬ p4734))
    (h7721 : p2630 ∨ (¬ p4751))
    (h66376 : p4751 ∨ p4748)
    (h7713 : p3364 ∨ (¬ p4748))
    (h7714 : p4343 ∨ (¬ p4748))
    (h7715 : p2810 ∨ (¬ p4748))
    (h6408 : p3055 ∨ (¬ p3364) ∨ (¬ p3365))
    (h52009 : (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4704))
    (h50005 : (¬ p2727) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4734))
    (h3749 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2811))
    (h9095 : (¬ p2598) ∨ (¬ p3055))
    (h8853 : p3585 ∨ (¬ p5213))
    (h7863 : p2727 ∨ (¬ p4812))
    (h3449 : p2651 ∨ (¬ p2661))
    (h7670 : p2598 ∨ (¬ p4728))
    (h66448 : p5215 ∨ p5213)
    (h66386 : p4809 ∨ p4812)
    (h66378 : p2654 ∨ p2661)
    (h66373 : p4728 ∨ p4726)
    (h8859 : p3367 ∨ (¬ p5215))
    (h7856 : p4116 ∨ (¬ p4809))
    (h65966 : (¬ p4809) ∨ (¬ p4703) ∨ (¬ p2499) ∨ (¬ p4715) ∨ (¬ p2992))
    (h3433 : (¬ p2654) ∨ p2655)
    (h7663 : p3759 ∨ (¬ p4726))
    (h3127 : (¬ p2496) ∨ p2499)
    (h46189 : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3759))
    (h66362 : p2496 ∨ p2503)
    (h3293 : p2573 ∨ (¬ p2583))
    (h3141 : p2493 ∨ (¬ p2503))
    (h66370 : p2576 ∨ p2583)
    (h53224 : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2946) ∨ (¬ p4116) ∨ (¬ p4704))
    (h3279 : (¬ p2576) ∨ p2579)
    : (¬ p5057) ∨ (¬ p3958) ∨ (¬ p4715) ∨ (¬ p4703) ∨ (¬ p3309) ∨ p3549 ∨ (¬ p3872) ∨ (¬ p2274) ∨ (¬ p2779) ∨ (¬ p2780) ∨ (¬ p3758) ∨ (¬ p4903) ∨ (¬ p2138) ∨ (¬ p4785) ∨ (¬ p3371) ∨ (¬ p2747) ∨ (¬ p4734) ∨ (¬ p2307) ∨ (¬ p4564) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5057 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4703 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3549) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4903 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))))));
    let u20 : p4704 := (Or.elim h7591 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    let u21 : p2542 := (Or.elim h7590 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u22 : p2881 := (Or.elim h8092 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    let u23 : p4559 := (Or.elim h65788 (fun q0 => q0) (fun r0 => (False.elim (r0 u22))));
    let u24 : p4236 := (Or.elim h7803 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u25 : p2737 := (Or.elim h3622 (fun q0 => q0) (fun r0 => (False.elim (r0 u15))));
    let u26 : p2749 := (Or.elim h3621 (fun q0 => (False.elim (q0 u15))) (fun r0 => r0));
    let u27 : p3365 := (Or.elim h7805 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u28 : (¬ p4315) := (Or.elim h53161 (fun q0 => (False.elim (q0 u26))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u19))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u27))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u16))))))))));
    let u29 : (¬ p5048) := (Or.elim h8456 (fun q0 => (False.elim (u28 q0))) (fun r0 => r0));
    let u30 : p5050 := (Or.elim h66427 (fun q0 => (False.elim (u29 q0))) (fun r0 => r0));
    let u31 : p3136 := (Or.elim h8462 (fun q0 => q0) (fun r0 => (False.elim (r0 u30))));
    let u32 : (¬ p2952) := (Or.elim h51323 (fun q0 => (False.elim (q0 u25))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u31))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u24))) (fun r3 => (False.elim (r3 u16))))))))));
    let u33 : (¬ p2949) := (Or.elim h4028 (fun q0 => q0) (fun r0 => (False.elim (u32 r0))));
    let u34 : p2956 := (Or.elim h66408 (fun q0 => q0) (fun r0 => (False.elim (u33 r0))));
    let u35 : p2946 := (Or.elim h4042 (fun q0 => q0) (fun r0 => (False.elim (r0 u34))));
    let u36 : p2811 := (Or.elim h7804 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u37 : p3146 := (Or.elim h8479 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u38 : (¬ p2396) := (Or.elim h66737 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u11))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u12))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u13))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u14))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u15))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u16))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u17))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u18))) (fun r19 => (False.elim (r19 u19))))))))))))))))))))))))))))))))))))))))));
    let u39 : (¬ p4622) := (Or.elim h7384 (fun q0 => (False.elim (u38 q0))) (fun r0 => r0));
    let u40 : p4619 := (Or.elim h66352 (fun q0 => q0) (fun r0 => (False.elim (u39 r0))));
    let u41 : p4107 := (Or.elim h7378 (fun q0 => q0) (fun r0 => (False.elim (r0 u40))));
    let u42 : (¬ p4665) := (Or.elim h65751 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u37))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u41))) (fun r3 => (False.elim (r3 u23))))))))));
    let u43 : p4667 := (Or.elim h66358 (fun q0 => (False.elim (u42 q0))) (fun r0 => r0));
    let u44 : p3945 := (Or.elim h7486 (fun q0 => q0) (fun r0 => (False.elim (r0 u43))));
    let u45 : p2459 := (Or.elim h7487 (fun q0 => q0) (fun r0 => (False.elim (r0 u43))));
    let u46 : (¬ p2177) := (Or.elim h20089 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u44))) (fun r1 => (False.elim (r1 u41))))));
    let u47 : p2299 := (Or.elim h24089 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u44))) (fun r1 => (False.elim (r1 u41))))));
    let u48 : (¬ p4502) := (Or.elim h7062 (fun q0 => (False.elim (u46 q0))) (fun r0 => r0));
    let u49 : (¬ p2588) := (Or.elim h51714 (fun q0 => (False.elim (q0 u47))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u22))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1))))))))));
    let u50 : (¬ p3568) := (Or.elim h41403 (fun q0 => (False.elim (q0 u47))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u22))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u18))))))))));
    let u51 : p4500 := (Or.elim h66330 (fun q0 => (False.elim (u48 q0))) (fun r0 => r0));
    let u52 : (¬ p4707) := (Or.elim h7601 (fun q0 => (False.elim (u49 q0))) (fun r0 => r0));
    let u53 : (¬ p4568) := (Or.elim h7237 (fun q0 => (False.elim (u50 q0))) (fun r0 => r0));
    let u54 : p3955 := (Or.elim h7054 (fun q0 => q0) (fun r0 => (False.elim (r0 u51))));
    let u55 : p4138 := (Or.elim h7055 (fun q0 => q0) (fun r0 => (False.elim (r0 u51))));
    let u56 : p4709 := (Or.elim h66368 (fun q0 => q0) (fun r0 => (False.elim (u52 r0))));
    let u57 : p4571 := (Or.elim h66342 (fun q0 => q0) (fun r0 => (False.elim (u53 r0))));
    let u58 : (¬ p4347) := (Or.elim h41812 (fun q0 => (False.elim (q0 u45))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u22))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u54))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u23))))))))));
    let u59 : p2553 := (Or.elim h7607 (fun q0 => q0) (fun r0 => (False.elim (r0 u56))));
    let u60 : p2295 := (Or.elim h7243 (fun q0 => q0) (fun r0 => (False.elim (r0 u57))));
    let u61 : (¬ p4600) := (Or.elim h7326 (fun q0 => (False.elim (u58 q0))) (fun r0 => r0));
    let u62 : (¬ p3956) := (Or.elim h41813 (fun q0 => (False.elim (q0 u59))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u22))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u55))) (fun r3 => (False.elim (r3 u23))))))))));
    let u63 : (¬ p3324) := (Or.elim h48283 (fun q0 => (False.elim (q0 u60))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u22))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u55))) (fun r3 => (False.elim (r3 u23))))))))));
    let u64 : p4602 := (Or.elim h66349 (fun q0 => q0) (fun r0 => (False.elim (u61 r0))));
    let u65 : (¬ p4594) := (Or.elim h7309 (fun q0 => (False.elim (u62 q0))) (fun r0 => r0));
    let u66 : (¬ p4768) := (Or.elim h7771 (fun q0 => (False.elim (u63 q0))) (fun r0 => r0));
    let u67 : p2363 := (Or.elim h7332 (fun q0 => q0) (fun r0 => (False.elim (r0 u64))));
    let u68 : p4597 := (Or.elim h66348 (fun q0 => q0) (fun r0 => (False.elim (u65 r0))));
    let u69 : p4772 := (Or.elim h66381 (fun q0 => q0) (fun r0 => (False.elim (u66 r0))));
    let u70 : p2352 := (Or.elim h7315 (fun q0 => q0) (fun r0 => (False.elim (r0 u68))));
    let u71 : p2668 := (Or.elim h7777 (fun q0 => q0) (fun r0 => (False.elim (r0 u69))));
    let u72 : (¬ p2331) := (Or.elim h45524 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u67))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u71))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u25))) (fun r3 => (False.elim (r3 u36))))))))));
    let u73 : (¬ p4582) := (Or.elim h7281 (fun q0 => (False.elim (u72 q0))) (fun r0 => r0));
    let u74 : p4579 := (Or.elim h66346 (fun q0 => q0) (fun r0 => (False.elim (u73 r0))));
    let u75 : p2963 := (Or.elim h7275 (fun q0 => q0) (fun r0 => (False.elim (r0 u74))));
    let u76 : (¬ p2630) := (Or.elim h66735 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u59))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u75))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u21))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u24))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u25))) (fun r6 => (False.elim (r6 u16))))))))))))))));
    let u77 : (¬ p4751) := (Or.elim h7721 (fun q0 => (False.elim (u76 q0))) (fun r0 => r0));
    let u78 : p4748 := (Or.elim h66376 (fun q0 => (False.elim (u77 q0))) (fun r0 => r0));
    let u79 : p3364 := (Or.elim h7713 (fun q0 => q0) (fun r0 => (False.elim (r0 u78))));
    let u80 : p4343 := (Or.elim h7714 (fun q0 => q0) (fun r0 => (False.elim (r0 u78))));
    let u81 : p2810 := (Or.elim h7715 (fun q0 => q0) (fun r0 => (False.elim (r0 u78))));
    let u82 : p3055 := (Or.elim h6408 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u79))) (fun r1 => (False.elim (r1 u27))))));
    let u83 : (¬ p3585) := (Or.elim h52009 (fun q0 => (False.elim (q0 u25))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u36))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u35))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u80))) (fun r4 => (False.elim (r4 u20))))))))))));
    let u84 : (¬ p2727) := (Or.elim h50005 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u26))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u81))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u27))) (fun r3 => (False.elim (r3 u16))))))))));
    let u85 : (¬ p2651) := (Or.elim h3749 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u81))) (fun r1 => (False.elim (r1 u36))))));
    let u86 : (¬ p2598) := (Or.elim h9095 (fun q0 => q0) (fun r0 => (False.elim (r0 u82))));
    let u87 : (¬ p5213) := (Or.elim h8853 (fun q0 => (False.elim (u83 q0))) (fun r0 => r0));
    let u88 : (¬ p4812) := (Or.elim h7863 (fun q0 => (False.elim (u84 q0))) (fun r0 => r0));
    let u89 : (¬ p2661) := (Or.elim h3449 (fun q0 => (False.elim (u85 q0))) (fun r0 => r0));
    let u90 : (¬ p4728) := (Or.elim h7670 (fun q0 => (False.elim (u86 q0))) (fun r0 => r0));
    let u91 : p5215 := (Or.elim h66448 (fun q0 => q0) (fun r0 => (False.elim (u87 r0))));
    let u92 : p4809 := (Or.elim h66386 (fun q0 => q0) (fun r0 => (False.elim (u88 r0))));
    let u93 : p2654 := (Or.elim h66378 (fun q0 => q0) (fun r0 => (False.elim (u89 r0))));
    let u94 : p4726 := (Or.elim h66373 (fun q0 => (False.elim (u90 q0))) (fun r0 => r0));
    let u95 : p3367 := (Or.elim h8859 (fun q0 => q0) (fun r0 => (False.elim (r0 u91))));
    let u96 : p4116 := (Or.elim h7856 (fun q0 => q0) (fun r0 => (False.elim (r0 u92))));
    let u97 : (¬ p2499) := (Or.elim h65966 (fun q0 => (False.elim (q0 u92))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u19))))))))));
    let u98 : p2655 := (Or.elim h3433 (fun q0 => (False.elim (q0 u93))) (fun r0 => r0));
    let u99 : p3759 := (Or.elim h7663 (fun q0 => q0) (fun r0 => (False.elim (r0 u94))));
    let u100 : (¬ p2496) := (Or.elim h3127 (fun q0 => q0) (fun r0 => (False.elim (u97 r0))));
    let u101 : (¬ p2573) := (Or.elim h46189 (fun q0 => (False.elim (q0 u70))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u67))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u95))) (fun r3 => (False.elim (r3 u99))))))))));
    let u102 : p2503 := (Or.elim h66362 (fun q0 => (False.elim (u100 q0))) (fun r0 => r0));
    let u103 : (¬ p2583) := (Or.elim h3293 (fun q0 => (False.elim (u101 q0))) (fun r0 => r0));
    let u104 : p2493 := (Or.elim h3141 (fun q0 => q0) (fun r0 => (False.elim (r0 u102))));
    let u105 : p2576 := (Or.elim h66370 (fun q0 => q0) (fun r0 => (False.elim (u103 r0))));
    let u106 : (¬ p2579) := (Or.elim h53224 (fun q0 => (False.elim (q0 u104))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u98))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u35))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u96))) (fun r4 => (False.elim (r4 u20))))))))))));
    (Or.elim h3279 (fun q0 => (False.elim (q0 u105))) (fun r0 => (False.elim (u106 r0)))))

theorem step66741 (p2264 p2996 p3027 p3030 p3036 p3189 p3644 p4111 p4378 p4551 p4653 : Prop)
    (h7189 : p4378 ∨ (¬ p4551))
    (h7191 : p2264 ∨ (¬ p4551))
    (h48739 : (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3644) ∨ (¬ p4378) ∨ (¬ p4653))
    (h58487 : (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3644) ∨ (¬ p4111))
    (h4185 : p2996 ∨ (¬ p3030))
    (h4199 : p3027 ∨ (¬ p3036))
    (h66416 : p3036 ∨ p3030)
    : (¬ p4551) ∨ (¬ p3189) ∨ (¬ p3644) ∨ (¬ p4653) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4551 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4378 := (Or.elim h7189 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p2264 := (Or.elim h7191 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : (¬ p2996) := (Or.elim h48739 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3))))))))));
    let u8 : (¬ p3027) := (Or.elim h58487 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4))))))));
    let u9 : (¬ p3030) := (Or.elim h4185 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u10 : (¬ p3036) := (Or.elim h4199 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    (Or.elim h66416 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u9 r0)))))

theorem step66742 (p2996 p3030 p3036 p3038 p3189 p3527 p3553 p3644 p3919 p4111 p4547 p4551 p4652 p4653 : Prop)
    (h66741 : (¬ p4551) ∨ (¬ p3189) ∨ (¬ p3644) ∨ (¬ p4653) ∨ (¬ p4111))
    (h66339 : p4551 ∨ p4547)
    (h7183 : p3919 ∨ (¬ p4547))
    (h7185 : p3553 ∨ (¬ p4547))
    (h22466 : (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3919))
    (h52473 : (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4111) ∨ (¬ p4652))
    (h4185 : p2996 ∨ (¬ p3030))
    (h4198 : (¬ p3036) ∨ p3038)
    (h66416 : p3036 ∨ p3030)
    : (¬ p3189) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p4653) ∨ (¬ p4652) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4551) := (Or.elim h66741 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5))))))))));
    let u7 : p4547 := (Or.elim h66339 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    let u8 : p3919 := (Or.elim h7183 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u9 : p3553 := (Or.elim h7185 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u10 : (¬ p2996) := (Or.elim h22466 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u8))))));
    let u11 : (¬ p3038) := (Or.elim h52473 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4))))))))));
    let u12 : (¬ p3030) := (Or.elim h4185 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : (¬ p3036) := (Or.elim h4198 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h66416 (fun q0 => (False.elim (u13 q0))) (fun r0 => (False.elim (u12 r0)))))

theorem step66743 (p2138 p2192 p2241 p2244 p2247 p2251 p2274 p2295 p2299 p2307 p2310 p2313 p2317 p2331 p2341 p2352 p2363 p2417 p2427 p2437 p2459 p2493 p2496 p2499 p2503 p2542 p2553 p2573 p2576 p2579 p2583 p2588 p2598 p2619 p2630 p2641 p2651 p2654 p2655 p2661 p2707 p2717 p2727 p2737 p2743 p2747 p2748 p2749 p2774 p2777 p2779 p2780 p2784 p2797 p2810 p2811 p2870 p2881 p2901 p2911 p2925 p2928 p2932 p2934 p2946 p2963 p2992 p3055 p3093 p3097 p3136 p3156 p3189 p3246 p3266 p3276 p3309 p3346 p3355 p3364 p3365 p3366 p3367 p3371 p3389 p3425 p3461 p3471 p3527 p3540 p3541 p3548 p3549 p3551 p3564 p3568 p3576 p3583 p3585 p3588 p3644 p3659 p3662 p3687 p3690 p3692 p3694 p3742 p3745 p3746 p3747 p3758 p3759 p3820 p3872 p3873 p3876 p3920 p3941 p3956 p3958 p3969 p3983 p4042 p4107 p4111 p4116 p4118 p4136 p4137 p4138 p4154 p4169 p4173 p4191 p4195 p4236 p4241 p4243 p4244 p4245 p4312 p4313 p4315 p4320 p4330 p4336 p4343 p4360 p4365 p4396 p4425 p4444 p4445 p4500 p4511 p4515 p4554 p4557 p4558 p4559 p4562 p4563 p4564 p4565 p4568 p4571 p4579 p4582 p4586 p4589 p4594 p4597 p4600 p4602 p4619 p4620 p4634 p4637 p4639 p4643 p4644 p4645 p4649 p4651 p4652 p4653 p4665 p4667 p4703 p4704 p4707 p4709 p4714 p4715 p4726 p4728 p4732 p4734 p4735 p4739 p4743 p4748 p4751 p4755 p4758 p4785 p4792 p4795 p4799 p4803 p4809 p4812 p4840 p4841 p4844 p4873 p4876 p4893 p4896 p4903 p4916 p4918 p4921 p4923 p4956 p4958 p4960 p5014 p5016 p5019 p5048 p5050 p5055 p5057 p5061 p5064 p5073 p5077 p5081 p5084 p5085 p5101 p5103 p5115 p5120 p5122 p5123 p5125 p5130 p5180 p5185 p5196 p5200 p5201 p5213 p5215 p5246 p5251 p5256 p5259 p5304 p5306 p5320 p5323 p5555 p5558 p5561 p5567 p5568 p5571 : Prop)
    (h8090 : p4042 ∨ (¬ p4903))
    (h3620 : (¬ p2747) ∨ p2748)
    (h7804 : p2811 ∨ (¬ p4785))
    (h20425 : (¬ p2811) ∨ (¬ p2946) ∨ (¬ p4315))
    (h38119 : (¬ p2748) ∨ (¬ p3662) ∨ p4315)
    (h8240 : p3662 ∨ (¬ p4956))
    (h66413 : p4956 ∨ p4958)
    (h8246 : p2992 ∨ (¬ p4958))
    (h20688 : (¬ p2946) ∨ (¬ p2963) ∨ (¬ p4336))
    (h7225 : p4336 ∨ (¬ p4565))
    (h66341 : p4565 ∨ p4562)
    (h7222 : (¬ p4562) ∨ p4564)
    (h7221 : (¬ p4562) ∨ p4563)
    (h8311 : (¬ p2331) ∨ (¬ p2963))
    (h7281 : p2331 ∨ (¬ p4582))
    (h66346 : p4579 ∨ p4582)
    (h7273 : p3983 ∨ (¬ p4579))
    (h3622 : p2737 ∨ (¬ p2747))
    (h7805 : p3365 ∨ (¬ p4785))
    (h4837 : (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3366))
    (h7685 : p3366 ∨ (¬ p4735))
    (h66374 : p4732 ∨ p4735)
    (h7683 : (¬ p4732) ∨ p4734)
    (h3621 : (¬ p2747) ∨ p2749)
    (h7803 : p4236 ∨ (¬ p4785))
    (h62070 : (¬ p2737) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4236) ∨ (¬ p4734))
    (h7953 : p2797 ∨ (¬ p4844))
    (h66394 : p4844 ∨ p4840)
    (h7947 : p4195 ∨ (¬ p4840))
    (h49583 : (¬ p2641) ∨ (¬ p2749) ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p4734))
    (h7739 : p2641 ∨ (¬ p4758))
    (h66377 : p4758 ∨ p4755)
    (h7733 : p4154 ∨ (¬ p4755))
    (h7679 : p3873 ∨ (¬ p4732))
    (h27638 : (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3873))
    (h2639 : p2241 ∨ (¬ p2251))
    (h66336 : p2244 ∨ p2251)
    (h2625 : (¬ p2244) ∨ p2247)
    (h7378 : p4107 ∨ (¬ p4619))
    (h46396 : (¬ p2247) ∨ (¬ p3568) ∨ (¬ p4107) ∨ (¬ p4154))
    (h7237 : p3568 ∨ (¬ p4568))
    (h66342 : p4571 ∨ p4568)
    (h7243 : p2295 ∨ (¬ p4571))
    (h54164 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2946) ∨ (¬ p3983) ∨ (¬ p4563))
    (h2756 : (¬ p2310) ∨ p2313)
    (h66343 : p2317 ∨ p2310)
    (h2770 : p2307 ∨ (¬ p2317))
    (h8245 : p4365 ∨ (¬ p4958))
    (h31670 : (¬ p2749) ∨ p3371 ∨ (¬ p4365))
    (h7731 : p4245 ∨ (¬ p4755))
    (h6376 : (¬ p2247) ∨ (¬ p3093) ∨ (¬ p4245))
    (h8392 : p3093 ∨ (¬ p5019))
    (h66423 : p5019 ∨ p5014)
    (h8385 : (¬ p5014) ∨ p5016)
    (h19537 : (¬ p2307) ∨ p3309 ∨ (¬ p5016))
    (h10031 : (¬ p2737) ∨ (¬ p2743))
    (h8456 : p4315 ∨ (¬ p5048))
    (h66427 : p5048 ∨ p5050)
    (h8461 : p4313 ∨ (¬ p5050))
    (h29019 : p2743 ∨ (¬ p3583) ∨ (¬ p4313))
    (h8017 : p3583 ∨ (¬ p4873))
    (h66397 : p4873 ∨ p4876)
    (h8021 : p4243 ∨ (¬ p4876))
    (h8248 : (¬ p4958) ∨ p4960)
    (h7219 : p3745 ∨ (¬ p4562))
    (h53120 : (¬ p2192) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p4960))
    (h7096 : p2192 ∨ (¬ p4515))
    (h66332 : p4511 ∨ p4515)
    (h7090 : p4173 ∨ (¬ p4511))
    (h6606 : p3758 ∨ (¬ p4173) ∨ (¬ p4243))
    (h7945 : (¬ p4840) ∨ p4841)
    (h14306 : p2780 ∨ (¬ p3365) ∨ (¬ p4841))
    (h23885 : (¬ p2774) ∨ (¬ p3365) ∨ (¬ p4841))
    (h3697 : p2774 ∨ (¬ p2784))
    (h66391 : p2784 ∨ p2777)
    (h3682 : (¬ p2777) ∨ p2779)
    (h6546 : p2274 ∨ (¬ p2295) ∨ (¬ p3745))
    (h6933 : (¬ p3097) ∨ p3568 ∨ (¬ p3745))
    (h7202 : p3097 ∨ (¬ p4554))
    (h66340 : p4554 ∨ p4557)
    (h7207 : p3872 ∨ (¬ p4557))
    (h19100 : p2313 ∨ (¬ p3549) ∨ (¬ p5016))
    (h7620 : p3958 ∨ (¬ p4714))
    (h7619 : (¬ p4714) ∨ p4715)
    (h66738 : (¬ p5057) ∨ (¬ p3958) ∨ (¬ p4715) ∨ (¬ p4703) ∨ (¬ p3309) ∨ p3549 ∨ (¬ p3872) ∨ (¬ p2274) ∨ (¬ p2779) ∨ (¬ p2780) ∨ (¬ p3758) ∨ (¬ p4903) ∨ (¬ p2138) ∨ (¬ p4785) ∨ (¬ p3371) ∨ (¬ p2747) ∨ (¬ p4734) ∨ (¬ p2307) ∨ (¬ p4564) ∨ (¬ p2992))
    (h66428 : p5055 ∨ p5057)
    (h8473 : p3692 ∨ (¬ p5055))
    (h20084 : (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4042))
    (h7487 : p2459 ∨ (¬ p4667))
    (h66358 : p4665 ∨ p4667)
    (h7480 : p4445 ∨ (¬ p4665))
    (h8092 : p2881 ∨ (¬ p4903))
    (h8091 : p3747 ∨ (¬ p4903))
    (h7209 : (¬ p4557) ∨ p4558)
    (h62975 : (¬ p2901) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p4558))
    (h8127 : p2901 ∨ (¬ p4918))
    (h66403 : p4916 ∨ p4918)
    (h8121 : p4320 ∨ (¬ p4916))
    (h7588 : p4241 ∨ (¬ p4703))
    (h30539 : (¬ p2811) ∨ (¬ p2946) ∨ p3136)
    (h51039 : (¬ p2427) ∨ (¬ p3136) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4241) ∨ (¬ p4558))
    (h7435 : p2427 ∨ (¬ p4645))
    (h66355 : p4643 ∨ p4645)
    (h7430 : (¬ p4643) ∨ p4644)
    (h7210 : (¬ p4557) ∨ p4559)
    (h7379 : (¬ p4619) ∨ p4620)
    (h7377 : p4396 ∨ (¬ p4619))
    (h7591 : (¬ p4703) ∨ p4704)
    (h7590 : p2542 ∨ (¬ p4703))
    (h7055 : p4138 ∨ (¬ p4500))
    (h7056 : p2299 ∨ (¬ p4500))
    (h37912 : (¬ p2363) ∨ p2459 ∨ (¬ p4138))
    (h51714 : (¬ p2299) ∨ (¬ p2588) ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p3958))
    (h52582 : (¬ p2299) ∨ (¬ p3156) ∨ (¬ p4042) ∨ (¬ p4320) ∨ (¬ p4559))
    (h47805 : (¬ p2299) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3758))
    (h7332 : p2363 ∨ (¬ p4602))
    (h7601 : p2588 ∨ (¬ p4707))
    (h8496 : p3156 ∨ (¬ p5064))
    (h8074 : p2870 ∨ (¬ p4896))
    (h66349 : p4602 ∨ p4600)
    (h66368 : p4709 ∨ p4707)
    (h66429 : p5061 ∨ p5064)
    (h66400 : p4896 ∨ p4893)
    (h7328 : p4330 ∨ (¬ p4600))
    (h7606 : p3920 ∨ (¬ p4709))
    (h7607 : p2553 ∨ (¬ p4709))
    (h8489 : p4312 ∨ (¬ p5061))
    (h8066 : p4136 ∨ (¬ p4893))
    (h8067 : p4169 ∨ (¬ p4893))
    (h8068 : p4244 ∨ (¬ p4893))
    (h41813 : (¬ p2553) ∨ (¬ p2881) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4559))
    (h66735 : (¬ p2630) ∨ (¬ p2553) ∨ (¬ p2963) ∨ (¬ p4715) ∨ (¬ p2542) ∨ (¬ p4236) ∨ (¬ p2737) ∨ (¬ p4734))
    (h6676 : (¬ p3692) ∨ p4118 ∨ (¬ p4312))
    (h19003 : (¬ p2138) ∨ p3425 ∨ (¬ p4136))
    (h20417 : (¬ p2138) ∨ (¬ p3471) ∨ (¬ p4136))
    (h48827 : (¬ p2299) ∨ (¬ p2619) ∨ (¬ p4042) ∨ (¬ p4244) ∨ (¬ p4559))
    (h7309 : p3956 ∨ (¬ p4594))
    (h7721 : p2630 ∨ (¬ p4751))
    (h8951 : p3471 ∨ (¬ p5259))
    (h7704 : p2619 ∨ (¬ p4743))
    (h66348 : p4597 ∨ p4594)
    (h66376 : p4751 ∨ p4748)
    (h66453 : p5259 ∨ p5256)
    (h66375 : p4739 ∨ p4743)
    (h7315 : p2352 ∨ (¬ p4597))
    (h7713 : p3364 ∨ (¬ p4748))
    (h7714 : p4343 ∨ (¬ p4748))
    (h7715 : p2810 ∨ (¬ p4748))
    (h8943 : p3820 ∨ (¬ p5256))
    (h7698 : p3694 ∨ (¬ p4739))
    (h6408 : p3055 ∨ (¬ p3364) ∨ (¬ p3365))
    (h52009 : (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4704))
    (h50005 : (¬ p2727) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4734))
    (h3749 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2811))
    (h46195 : (¬ p2138) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4444))
    (h9095 : (¬ p2598) ∨ (¬ p3055))
    (h8853 : p3585 ∨ (¬ p5213))
    (h7863 : p2727 ∨ (¬ p4812))
    (h3449 : p2651 ∨ (¬ p2661))
    (h8646 : p4444 ∨ (¬ p5115))
    (h7670 : p2598 ∨ (¬ p4728))
    (h66448 : p5215 ∨ p5213)
    (h66386 : p4809 ∨ p4812)
    (h66378 : p2654 ∨ p2661)
    (h66438 : p5115 ∨ p5120)
    (h66373 : p4728 ∨ p4726)
    (h8858 : p3541 ∨ (¬ p5215))
    (h8859 : p3367 ∨ (¬ p5215))
    (h7856 : p4116 ∨ (¬ p4809))
    (h7857 : p4111 ∨ (¬ p4809))
    (h65966 : (¬ p4809) ∨ (¬ p4703) ∨ (¬ p2499) ∨ (¬ p4715) ∨ (¬ p2992))
    (h3433 : (¬ p2654) ∨ p2655)
    (h8652 : p3266 ∨ (¬ p5120))
    (h8653 : (¬ p5120) ∨ p5122)
    (h8654 : (¬ p5120) ∨ p5123)
    (h7663 : p3759 ∨ (¬ p4726))
    (h51415 : (¬ p2992) ∨ (¬ p3742) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4644))
    (h3127 : (¬ p2496) ∨ p2499)
    (h6412 : p2499 ∨ (¬ p2928) ∨ (¬ p3920))
    (h7447 : p3742 ∨ (¬ p4649))
    (h66362 : p2496 ∨ p2503)
    (h3978 : (¬ p2925) ∨ p2928)
    (h66356 : p4651 ∨ p4649)
    (h3141 : p2493 ∨ (¬ p2503))
    (h66405 : p2932 ∨ p2925)
    (h7453 : p2437 ∨ (¬ p4651))
    (h7454 : (¬ p4651) ∨ p4652)
    (h7455 : (¬ p4651) ∨ p4653)
    (h53224 : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2946) ∨ (¬ p4116) ∨ (¬ p4704))
    (h3991 : (¬ p2932) ∨ p2934)
    (h64741 : (¬ p2437) ∨ (¬ p2655) ∨ (¬ p2946) ∨ (¬ p3540) ∨ (¬ p4704))
    (h62601 : (¬ p2437) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3876) ∨ (¬ p4704))
    (h3279 : (¬ p2576) ∨ p2579)
    (h6633 : (¬ p2934) ∨ (¬ p3541) ∨ p3687)
    (h8816 : p3540 ∨ (¬ p5196))
    (h8552 : p3876 ∨ (¬ p5081))
    (h66370 : p2576 ∨ p2583)
    (h66446 : p5196 ∨ p5200)
    (h66431 : p5081 ∨ p5084)
    (h3293 : p2573 ∨ (¬ p2583))
    (h8821 : (¬ p5200) ∨ p5201)
    (h8822 : p3389 ∨ (¬ p5200))
    (h8557 : (¬ p5084) ∨ p5085)
    (h46172 : (¬ p2417) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p4107))
    (h46116 : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759))
    (h21328 : p2707 ∨ (¬ p3367) ∨ (¬ p5085))
    (h20121 : (¬ p3367) ∨ (¬ p3588) ∨ (¬ p5085))
    (h7418 : p2417 ∨ (¬ p4639))
    (h8144 : p2911 ∨ (¬ p4923))
    (h7823 : p3588 ∨ (¬ p4792))
    (h66354 : p4634 ∨ p4639)
    (h66404 : p4923 ∨ p4921)
    (h66384 : p4792 ∨ p4795)
    (h7413 : (¬ p4634) ∨ p4637)
    (h8138 : p3644 ∨ (¬ p4921))
    (h7827 : p3576 ∨ (¬ p4795))
    (h58648 : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2881) ∨ (¬ p3367) ∨ (¬ p3425) ∨ (¬ p3548) ∨ (¬ p3576) ∨ (¬ p3759) ∨ (¬ p4559) ∨ (¬ p4734))
    (h9038 : p3548 ∨ (¬ p5304))
    (h66458 : p5304 ∨ p5306)
    (h9044 : p3527 ∨ (¬ p5306))
    (h49902 : (¬ p3425) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3687) ∨ (¬ p4734))
    (h7840 : p3659 ∨ (¬ p4799))
    (h66385 : p4803 ∨ p4799)
    (h7846 : p2717 ∨ (¬ p4803))
    (h49693 : (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4734))
    (h7292 : p3551 ∨ (¬ p4586))
    (h66347 : p4589 ∨ p4586)
    (h7298 : p2341 ∨ (¬ p4589))
    (h52653 : (¬ p2341) ∨ (¬ p3346) ∨ (¬ p3644) ∨ (¬ p4637) ∨ (¬ p5201))
    (h8776 : p3346 ∨ (¬ p5180))
    (h66444 : p5180 ∨ p5185)
    (h8782 : p3355 ∨ (¬ p5185))
    (h66742 : (¬ p3189) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p4653) ∨ (¬ p4652) ∨ (¬ p4111))
    (h8540 : p3189 ∨ (¬ p5077))
    (h66430 : p5073 ∨ p5077)
    (h8534 : p4360 ∨ (¬ p5073))
    (h57122 : (¬ p2573) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3564) ∨ (¬ p3759) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4360) ∨ (¬ p4734))
    (h9108 : p3564 ∨ (¬ p5323))
    (h66460 : p5320 ∨ p5323)
    (h9100 : p3746 ∨ (¬ p5320))
    (h9102 : p4137 ∨ (¬ p5320))
    (h44831 : (¬ p2352) ∨ (¬ p3266) ∨ (¬ p4137) ∨ (¬ p4191))
    (h41334 : (¬ p2553) ∨ (¬ p3246) ∨ (¬ p4137) ∨ (¬ p4396) ∨ (¬ p4559))
    (h8928 : p4191 ∨ (¬ p5246))
    (h8615 : p3246 ∨ (¬ p5103))
    (h66452 : p5246 ∨ p5251)
    (h66436 : p5101 ∨ p5103)
    (h8934 : p3461 ∨ (¬ p5251))
    (h8609 : p3690 ∨ (¬ p5101))
    (h42566 : (¬ p2553) ∨ (¬ p3461) ∨ (¬ p3746) ∨ (¬ p4425) ∨ (¬ p4620))
    (h41331 : (¬ p2717) ∨ (¬ p3690) ∨ (¬ p3941) ∨ (¬ p4169) ∨ (¬ p4445) ∨ (¬ p5122))
    (h8664 : p4425 ∨ (¬ p5125))
    (h9727 : p3941 ∨ (¬ p5561))
    (h66439 : p5125 ∨ p5130)
    (h66484 : p5555 ∨ p5561)
    (h8670 : p3276 ∨ (¬ p5130))
    (h9721 : (¬ p5555) ∨ p5558)
    (h53296 : (¬ p2748) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4312) ∨ (¬ p4360) ∨ (¬ p4734) ∨ (¬ p5123) ∨ (¬ p5568))
    (h41327 : (¬ p2299) ∨ (¬ p3747) ∨ (¬ p3969) ∨ (¬ p4559) ∨ (¬ p5558))
    (h9791 : (¬ p5567) ∨ p5568)
    (h9797 : p3969 ∨ (¬ p5571))
    (h66485 : p5567 ∨ p5571)
    : (¬ p4500) ∨ (¬ p2138) ∨ (¬ p4903) ∨ (¬ p4619) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p4714) ∨ (¬ p4703) ∨ (¬ p4785) ∨ (¬ p2747) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4500 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4903 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4714 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4703 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4042 := (Or.elim h8090 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u11 : p2748 := (Or.elim h3620 (fun q0 => (False.elim (q0 u9))) (fun r0 => r0));
    let u12 : p2811 := (Or.elim h7804 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u13 : (¬ p4315) := (Or.elim h20425 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => r1))));
    let u14 : (¬ p3662) := (Or.elim h38119 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u13 r1))))));
    let u15 : (¬ p4956) := (Or.elim h8240 (fun q0 => (False.elim (u14 q0))) (fun r0 => r0));
    let u16 : p4958 := (Or.elim h66413 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u17 : p2992 := (Or.elim h8246 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    let u18 : (¬ p4336) := (Or.elim h20688 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => r1))));
    let u19 : (¬ p4565) := (Or.elim h7225 (fun q0 => (False.elim (u18 q0))) (fun r0 => r0));
    let u20 : p4562 := (Or.elim h66341 (fun q0 => (False.elim (u19 q0))) (fun r0 => r0));
    let u21 : p4564 := (Or.elim h7222 (fun q0 => (False.elim (q0 u20))) (fun r0 => r0));
    let u22 : p4563 := (Or.elim h7221 (fun q0 => (False.elim (q0 u20))) (fun r0 => r0));
    let u23 : (¬ p2331) := (Or.elim h8311 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u24 : (¬ p4582) := (Or.elim h7281 (fun q0 => (False.elim (u23 q0))) (fun r0 => r0));
    let u25 : p4579 := (Or.elim h66346 (fun q0 => q0) (fun r0 => (False.elim (u24 r0))));
    let u26 : p3983 := (Or.elim h7273 (fun q0 => q0) (fun r0 => (False.elim (r0 u25))));
    let u27 : p2737 := (Or.elim h3622 (fun q0 => q0) (fun r0 => (False.elim (r0 u9))));
    let u28 : p3365 := (Or.elim h7805 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u29 : (¬ p3366) := (Or.elim h4837 (fun q0 => (False.elim (q0 u27))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u28))) (fun r1 => r1))));
    let u30 : (¬ p4735) := (Or.elim h7685 (fun q0 => (False.elim (u29 q0))) (fun r0 => r0));
    let u31 : p4732 := (Or.elim h66374 (fun q0 => q0) (fun r0 => (False.elim (u30 r0))));
    let u32 : p4734 := (Or.elim h7683 (fun q0 => (False.elim (q0 u31))) (fun r0 => r0));
    let u33 : p2749 := (Or.elim h3621 (fun q0 => (False.elim (q0 u9))) (fun r0 => r0));
    let u34 : p4236 := (Or.elim h7803 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u35 : (¬ p2797) := (Or.elim h62070 (fun q0 => (False.elim (q0 u27))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u34))) (fun r3 => (False.elim (r3 u32))))))))));
    let u36 : (¬ p4844) := (Or.elim h7953 (fun q0 => (False.elim (u35 q0))) (fun r0 => r0));
    let u37 : p4840 := (Or.elim h66394 (fun q0 => (False.elim (u36 q0))) (fun r0 => r0));
    let u38 : p4195 := (Or.elim h7947 (fun q0 => q0) (fun r0 => (False.elim (r0 u37))));
    let u39 : (¬ p2641) := (Or.elim h49583 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u33))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u28))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u38))) (fun r3 => (False.elim (r3 u32))))))))));
    let u40 : (¬ p4758) := (Or.elim h7739 (fun q0 => (False.elim (u39 q0))) (fun r0 => r0));
    let u41 : p4755 := (Or.elim h66377 (fun q0 => (False.elim (u40 q0))) (fun r0 => r0));
    let u42 : p4154 := (Or.elim h7733 (fun q0 => q0) (fun r0 => (False.elim (r0 u41))));
    let u43 : p3873 := (Or.elim h7679 (fun q0 => q0) (fun r0 => (False.elim (r0 u31))));
    let u44 : (¬ p2241) := (Or.elim h27638 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u28))) (fun r2 => (False.elim (r2 u43))))))));
    let u45 : (¬ p2251) := (Or.elim h2639 (fun q0 => (False.elim (u44 q0))) (fun r0 => r0));
    let u46 : p2244 := (Or.elim h66336 (fun q0 => q0) (fun r0 => (False.elim (u45 r0))));
    let u47 : p2247 := (Or.elim h2625 (fun q0 => (False.elim (q0 u46))) (fun r0 => r0));
    let u48 : p4107 := (Or.elim h7378 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u49 : (¬ p3568) := (Or.elim h46396 (fun q0 => (False.elim (q0 u47))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u48))) (fun r2 => (False.elim (r2 u42))))))));
    let u50 : (¬ p4568) := (Or.elim h7237 (fun q0 => (False.elim (u49 q0))) (fun r0 => r0));
    let u51 : p4571 := (Or.elim h66342 (fun q0 => q0) (fun r0 => (False.elim (u50 r0))));
    let u52 : p2295 := (Or.elim h7243 (fun q0 => q0) (fun r0 => (False.elim (r0 u51))));
    let u53 : (¬ p2313) := (Or.elim h54164 (fun q0 => (False.elim (q0 u52))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u26))) (fun r3 => (False.elim (r3 u22))))))))));
    let u54 : (¬ p2310) := (Or.elim h2756 (fun q0 => q0) (fun r0 => (False.elim (u53 r0))));
    let u55 : p2317 := (Or.elim h66343 (fun q0 => q0) (fun r0 => (False.elim (u54 r0))));
    let u56 : p2307 := (Or.elim h2770 (fun q0 => q0) (fun r0 => (False.elim (r0 u55))));
    let u57 : p4365 := (Or.elim h8245 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    let u58 : p3371 := (Or.elim h31670 (fun q0 => (False.elim (q0 u33))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u57))))));
    let u59 : p4245 := (Or.elim h7731 (fun q0 => q0) (fun r0 => (False.elim (r0 u41))));
    let u60 : (¬ p3093) := (Or.elim h6376 (fun q0 => (False.elim (q0 u47))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u59))))));
    let u61 : (¬ p5019) := (Or.elim h8392 (fun q0 => (False.elim (u60 q0))) (fun r0 => r0));
    let u62 : p5014 := (Or.elim h66423 (fun q0 => (False.elim (u61 q0))) (fun r0 => r0));
    let u63 : p5016 := (Or.elim h8385 (fun q0 => (False.elim (q0 u62))) (fun r0 => r0));
    let u64 : p3309 := (Or.elim h19537 (fun q0 => (False.elim (q0 u56))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u63))))));
    let u65 : (¬ p2743) := (Or.elim h10031 (fun q0 => (False.elim (q0 u27))) (fun r0 => r0));
    let u66 : (¬ p5048) := (Or.elim h8456 (fun q0 => (False.elim (u13 q0))) (fun r0 => r0));
    let u67 : p5050 := (Or.elim h66427 (fun q0 => (False.elim (u66 q0))) (fun r0 => r0));
    let u68 : p4313 := (Or.elim h8461 (fun q0 => q0) (fun r0 => (False.elim (r0 u67))));
    let u69 : (¬ p3583) := (Or.elim h29019 (fun q0 => (False.elim (u65 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u68))))));
    let u70 : (¬ p4873) := (Or.elim h8017 (fun q0 => (False.elim (u69 q0))) (fun r0 => r0));
    let u71 : p4876 := (Or.elim h66397 (fun q0 => (False.elim (u70 q0))) (fun r0 => r0));
    let u72 : p4243 := (Or.elim h8021 (fun q0 => q0) (fun r0 => (False.elim (r0 u71))));
    let u73 : p4960 := (Or.elim h8248 (fun q0 => (False.elim (q0 u16))) (fun r0 => r0));
    let u74 : p3745 := (Or.elim h7219 (fun q0 => q0) (fun r0 => (False.elim (r0 u20))));
    let u75 : (¬ p2192) := (Or.elim h53120 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u74))) (fun r3 => (False.elim (r3 u73))))))))));
    let u76 : (¬ p4515) := (Or.elim h7096 (fun q0 => (False.elim (u75 q0))) (fun r0 => r0));
    let u77 : p4511 := (Or.elim h66332 (fun q0 => q0) (fun r0 => (False.elim (u76 r0))));
    let u78 : p4173 := (Or.elim h7090 (fun q0 => q0) (fun r0 => (False.elim (r0 u77))));
    let u79 : p3758 := (Or.elim h6606 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u78))) (fun r1 => (False.elim (r1 u72))))));
    let u80 : p4841 := (Or.elim h7945 (fun q0 => (False.elim (q0 u37))) (fun r0 => r0));
    let u81 : p2780 := (Or.elim h14306 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u28))) (fun r1 => (False.elim (r1 u80))))));
    let u82 : (¬ p2774) := (Or.elim h23885 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u28))) (fun r1 => (False.elim (r1 u80))))));
    let u83 : (¬ p2784) := (Or.elim h3697 (fun q0 => (False.elim (u82 q0))) (fun r0 => r0));
    let u84 : p2777 := (Or.elim h66391 (fun q0 => (False.elim (u83 q0))) (fun r0 => r0));
    let u85 : p2779 := (Or.elim h3682 (fun q0 => (False.elim (q0 u84))) (fun r0 => r0));
    let u86 : p2274 := (Or.elim h6546 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u52))) (fun r1 => (False.elim (r1 u74))))));
    let u87 : (¬ p3097) := (Or.elim h6933 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u49 q1))) (fun r1 => (False.elim (r1 u74))))));
    let u88 : (¬ p4554) := (Or.elim h7202 (fun q0 => (False.elim (u87 q0))) (fun r0 => r0));
    let u89 : p4557 := (Or.elim h66340 (fun q0 => (False.elim (u88 q0))) (fun r0 => r0));
    let u90 : p3872 := (Or.elim h7207 (fun q0 => q0) (fun r0 => (False.elim (r0 u89))));
    let u91 : (¬ p3549) := (Or.elim h19100 (fun q0 => (False.elim (u53 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u63))))));
    let u92 : p3958 := (Or.elim h7620 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u93 : p4715 := (Or.elim h7619 (fun q0 => (False.elim (q0 u6))) (fun r0 => r0));
    let u94 : (¬ p5057) := (Or.elim h66738 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u92))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u93))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u64))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u91 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u90))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u86))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u85))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u81))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u79))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u2))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u1))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u8))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u58))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u9))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u32))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u56))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u21))) (fun r18 => (False.elim (r18 u17))))))))))))))))))))))))))))))))))))))));
    let u95 : p5055 := (Or.elim h66428 (fun q0 => q0) (fun r0 => (False.elim (u94 r0))));
    let u96 : p3692 := (Or.elim h8473 (fun q0 => q0) (fun r0 => (False.elim (r0 u95))));
    let u97 : (¬ p2459) := (Or.elim h20084 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u96))) (fun r1 => (False.elim (r1 u10))))));
    let u98 : (¬ p4667) := (Or.elim h7487 (fun q0 => (False.elim (u97 q0))) (fun r0 => r0));
    let u99 : p4665 := (Or.elim h66358 (fun q0 => q0) (fun r0 => (False.elim (u98 r0))));
    let u100 : p4445 := (Or.elim h7480 (fun q0 => q0) (fun r0 => (False.elim (r0 u99))));
    let u101 : p2881 := (Or.elim h8092 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u102 : p3747 := (Or.elim h8091 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u103 : p4558 := (Or.elim h7209 (fun q0 => (False.elim (q0 u89))) (fun r0 => r0));
    let u104 : (¬ p2901) := (Or.elim h62975 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u74))) (fun r3 => (False.elim (r3 u103))))))))));
    let u105 : (¬ p4918) := (Or.elim h8127 (fun q0 => (False.elim (u104 q0))) (fun r0 => r0));
    let u106 : p4916 := (Or.elim h66403 (fun q0 => q0) (fun r0 => (False.elim (u105 r0))));
    let u107 : p4320 := (Or.elim h8121 (fun q0 => q0) (fun r0 => (False.elim (r0 u106))));
    let u108 : p4241 := (Or.elim h7588 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u109 : p3136 := (Or.elim h30539 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => r1))));
    let u110 : (¬ p2427) := (Or.elim h51039 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u109))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u74))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u38))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u108))) (fun r4 => (False.elim (r4 u103))))))))))));
    let u111 : (¬ p4645) := (Or.elim h7435 (fun q0 => (False.elim (u110 q0))) (fun r0 => r0));
    let u112 : p4643 := (Or.elim h66355 (fun q0 => q0) (fun r0 => (False.elim (u111 r0))));
    let u113 : p4644 := (Or.elim h7430 (fun q0 => (False.elim (q0 u112))) (fun r0 => r0));
    let u114 : p4559 := (Or.elim h7210 (fun q0 => (False.elim (q0 u89))) (fun r0 => r0));
    let u115 : p4620 := (Or.elim h7379 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    let u116 : p4396 := (Or.elim h7377 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u117 : p4704 := (Or.elim h7591 (fun q0 => (False.elim (q0 u7))) (fun r0 => r0));
    let u118 : p2542 := (Or.elim h7590 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u119 : p4138 := (Or.elim h7055 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u120 : p2299 := (Or.elim h7056 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u121 : (¬ p2363) := (Or.elim h37912 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u97 q1))) (fun r1 => (False.elim (r1 u119))))));
    let u122 : (¬ p2588) := (Or.elim h51714 (fun q0 => (False.elim (q0 u120))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u101))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u90))) (fun r3 => (False.elim (r3 u92))))))))));
    let u123 : (¬ p3156) := (Or.elim h52582 (fun q0 => (False.elim (q0 u120))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u107))) (fun r3 => (False.elim (r3 u114))))))))));
    let u124 : (¬ p2870) := (Or.elim h47805 (fun q0 => (False.elim (q0 u120))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u101))) (fun r2 => (False.elim (r2 u79))))))));
    let u125 : (¬ p4602) := (Or.elim h7332 (fun q0 => (False.elim (u121 q0))) (fun r0 => r0));
    let u126 : (¬ p4707) := (Or.elim h7601 (fun q0 => (False.elim (u122 q0))) (fun r0 => r0));
    let u127 : (¬ p5064) := (Or.elim h8496 (fun q0 => (False.elim (u123 q0))) (fun r0 => r0));
    let u128 : (¬ p4896) := (Or.elim h8074 (fun q0 => (False.elim (u124 q0))) (fun r0 => r0));
    let u129 : p4600 := (Or.elim h66349 (fun q0 => (False.elim (u125 q0))) (fun r0 => r0));
    let u130 : p4709 := (Or.elim h66368 (fun q0 => q0) (fun r0 => (False.elim (u126 r0))));
    let u131 : p5061 := (Or.elim h66429 (fun q0 => q0) (fun r0 => (False.elim (u127 r0))));
    let u132 : p4893 := (Or.elim h66400 (fun q0 => (False.elim (u128 q0))) (fun r0 => r0));
    let u133 : p4330 := (Or.elim h7328 (fun q0 => q0) (fun r0 => (False.elim (r0 u129))));
    let u134 : p3920 := (Or.elim h7606 (fun q0 => q0) (fun r0 => (False.elim (r0 u130))));
    let u135 : p2553 := (Or.elim h7607 (fun q0 => q0) (fun r0 => (False.elim (r0 u130))));
    let u136 : p4312 := (Or.elim h8489 (fun q0 => q0) (fun r0 => (False.elim (r0 u131))));
    let u137 : p4136 := (Or.elim h8066 (fun q0 => q0) (fun r0 => (False.elim (r0 u132))));
    let u138 : p4169 := (Or.elim h8067 (fun q0 => q0) (fun r0 => (False.elim (r0 u132))));
    let u139 : p4244 := (Or.elim h8068 (fun q0 => q0) (fun r0 => (False.elim (r0 u132))));
    let u140 : (¬ p3956) := (Or.elim h41813 (fun q0 => (False.elim (q0 u135))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u101))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u119))) (fun r3 => (False.elim (r3 u114))))))))));
    let u141 : (¬ p2630) := (Or.elim h66735 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u135))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u93))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u118))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u34))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u27))) (fun r6 => (False.elim (r6 u32))))))))))))))));
    let u142 : p4118 := (Or.elim h6676 (fun q0 => (False.elim (q0 u96))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u136))))));
    let u143 : p3425 := (Or.elim h19003 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u137))))));
    let u144 : (¬ p3471) := (Or.elim h20417 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u137))))));
    let u145 : (¬ p2619) := (Or.elim h48827 (fun q0 => (False.elim (q0 u120))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u139))) (fun r3 => (False.elim (r3 u114))))))))));
    let u146 : (¬ p4594) := (Or.elim h7309 (fun q0 => (False.elim (u140 q0))) (fun r0 => r0));
    let u147 : (¬ p4751) := (Or.elim h7721 (fun q0 => (False.elim (u141 q0))) (fun r0 => r0));
    let u148 : (¬ p5259) := (Or.elim h8951 (fun q0 => (False.elim (u144 q0))) (fun r0 => r0));
    let u149 : (¬ p4743) := (Or.elim h7704 (fun q0 => (False.elim (u145 q0))) (fun r0 => r0));
    let u150 : p4597 := (Or.elim h66348 (fun q0 => q0) (fun r0 => (False.elim (u146 r0))));
    let u151 : p4748 := (Or.elim h66376 (fun q0 => (False.elim (u147 q0))) (fun r0 => r0));
    let u152 : p5256 := (Or.elim h66453 (fun q0 => (False.elim (u148 q0))) (fun r0 => r0));
    let u153 : p4739 := (Or.elim h66375 (fun q0 => q0) (fun r0 => (False.elim (u149 r0))));
    let u154 : p2352 := (Or.elim h7315 (fun q0 => q0) (fun r0 => (False.elim (r0 u150))));
    let u155 : p3364 := (Or.elim h7713 (fun q0 => q0) (fun r0 => (False.elim (r0 u151))));
    let u156 : p4343 := (Or.elim h7714 (fun q0 => q0) (fun r0 => (False.elim (r0 u151))));
    let u157 : p2810 := (Or.elim h7715 (fun q0 => q0) (fun r0 => (False.elim (r0 u151))));
    let u158 : p3820 := (Or.elim h8943 (fun q0 => q0) (fun r0 => (False.elim (r0 u152))));
    let u159 : p3694 := (Or.elim h7698 (fun q0 => q0) (fun r0 => (False.elim (r0 u153))));
    let u160 : p3055 := (Or.elim h6408 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u155))) (fun r1 => (False.elim (r1 u28))))));
    let u161 : (¬ p3585) := (Or.elim h52009 (fun q0 => (False.elim (q0 u27))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u156))) (fun r4 => (False.elim (r4 u117))))))))))));
    let u162 : (¬ p2727) := (Or.elim h50005 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u33))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u157))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u28))) (fun r3 => (False.elim (r3 u32))))))))));
    let u163 : (¬ p2651) := (Or.elim h3749 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u157))) (fun r1 => (False.elim (r1 u12))))));
    let u164 : (¬ p4444) := (Or.elim h46195 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u96))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u159))) (fun r2 => r2))))));
    let u165 : (¬ p2598) := (Or.elim h9095 (fun q0 => q0) (fun r0 => (False.elim (r0 u160))));
    let u166 : (¬ p5213) := (Or.elim h8853 (fun q0 => (False.elim (u161 q0))) (fun r0 => r0));
    let u167 : (¬ p4812) := (Or.elim h7863 (fun q0 => (False.elim (u162 q0))) (fun r0 => r0));
    let u168 : (¬ p2661) := (Or.elim h3449 (fun q0 => (False.elim (u163 q0))) (fun r0 => r0));
    let u169 : (¬ p5115) := (Or.elim h8646 (fun q0 => (False.elim (u164 q0))) (fun r0 => r0));
    let u170 : (¬ p4728) := (Or.elim h7670 (fun q0 => (False.elim (u165 q0))) (fun r0 => r0));
    let u171 : p5215 := (Or.elim h66448 (fun q0 => q0) (fun r0 => (False.elim (u166 r0))));
    let u172 : p4809 := (Or.elim h66386 (fun q0 => q0) (fun r0 => (False.elim (u167 r0))));
    let u173 : p2654 := (Or.elim h66378 (fun q0 => q0) (fun r0 => (False.elim (u168 r0))));
    let u174 : p5120 := (Or.elim h66438 (fun q0 => (False.elim (u169 q0))) (fun r0 => r0));
    let u175 : p4726 := (Or.elim h66373 (fun q0 => (False.elim (u170 q0))) (fun r0 => r0));
    let u176 : p3541 := (Or.elim h8858 (fun q0 => q0) (fun r0 => (False.elim (r0 u171))));
    let u177 : p3367 := (Or.elim h8859 (fun q0 => q0) (fun r0 => (False.elim (r0 u171))));
    let u178 : p4116 := (Or.elim h7856 (fun q0 => q0) (fun r0 => (False.elim (r0 u172))));
    let u179 : p4111 := (Or.elim h7857 (fun q0 => q0) (fun r0 => (False.elim (r0 u172))));
    let u180 : (¬ p2499) := (Or.elim h65966 (fun q0 => (False.elim (q0 u172))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u93))) (fun r3 => (False.elim (r3 u17))))))))));
    let u181 : p2655 := (Or.elim h3433 (fun q0 => (False.elim (q0 u173))) (fun r0 => r0));
    let u182 : p3266 := (Or.elim h8652 (fun q0 => q0) (fun r0 => (False.elim (r0 u174))));
    let u183 : p5122 := (Or.elim h8653 (fun q0 => (False.elim (q0 u174))) (fun r0 => r0));
    let u184 : p5123 := (Or.elim h8654 (fun q0 => (False.elim (q0 u174))) (fun r0 => r0));
    let u185 : p3759 := (Or.elim h7663 (fun q0 => q0) (fun r0 => (False.elim (r0 u175))));
    let u186 : (¬ p3742) := (Or.elim h51415 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u179))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u108))) (fun r3 => (False.elim (r3 u113))))))))));
    let u187 : (¬ p2496) := (Or.elim h3127 (fun q0 => q0) (fun r0 => (False.elim (u180 r0))));
    let u188 : (¬ p2928) := (Or.elim h6412 (fun q0 => (False.elim (u180 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u134))))));
    let u189 : (¬ p4649) := (Or.elim h7447 (fun q0 => (False.elim (u186 q0))) (fun r0 => r0));
    let u190 : p2503 := (Or.elim h66362 (fun q0 => (False.elim (u187 q0))) (fun r0 => r0));
    let u191 : (¬ p2925) := (Or.elim h3978 (fun q0 => q0) (fun r0 => (False.elim (u188 r0))));
    let u192 : p4651 := (Or.elim h66356 (fun q0 => q0) (fun r0 => (False.elim (u189 r0))));
    let u193 : p2493 := (Or.elim h3141 (fun q0 => q0) (fun r0 => (False.elim (r0 u190))));
    let u194 : p2932 := (Or.elim h66405 (fun q0 => q0) (fun r0 => (False.elim (u191 r0))));
    let u195 : p2437 := (Or.elim h7453 (fun q0 => q0) (fun r0 => (False.elim (r0 u192))));
    let u196 : p4652 := (Or.elim h7454 (fun q0 => (False.elim (q0 u192))) (fun r0 => r0));
    let u197 : p4653 := (Or.elim h7455 (fun q0 => (False.elim (q0 u192))) (fun r0 => r0));
    let u198 : (¬ p2579) := (Or.elim h53224 (fun q0 => (False.elim (q0 u193))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u181))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u178))) (fun r4 => (False.elim (r4 u117))))))))))));
    let u199 : p2934 := (Or.elim h3991 (fun q0 => (False.elim (q0 u194))) (fun r0 => r0));
    let u200 : (¬ p3540) := (Or.elim h64741 (fun q0 => (False.elim (q0 u195))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u181))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u117))))))))));
    let u201 : (¬ p3876) := (Or.elim h62601 (fun q0 => (False.elim (q0 u195))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u109))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u155))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u117))))))))));
    let u202 : (¬ p2576) := (Or.elim h3279 (fun q0 => q0) (fun r0 => (False.elim (u198 r0))));
    let u203 : p3687 := (Or.elim h6633 (fun q0 => (False.elim (q0 u199))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u176))) (fun r1 => r1))));
    let u204 : (¬ p5196) := (Or.elim h8816 (fun q0 => (False.elim (u200 q0))) (fun r0 => r0));
    let u205 : (¬ p5081) := (Or.elim h8552 (fun q0 => (False.elim (u201 q0))) (fun r0 => r0));
    let u206 : p2583 := (Or.elim h66370 (fun q0 => (False.elim (u202 q0))) (fun r0 => r0));
    let u207 : p5200 := (Or.elim h66446 (fun q0 => (False.elim (u204 q0))) (fun r0 => r0));
    let u208 : p5084 := (Or.elim h66431 (fun q0 => (False.elim (u205 q0))) (fun r0 => r0));
    let u209 : p2573 := (Or.elim h3293 (fun q0 => q0) (fun r0 => (False.elim (r0 u206))));
    let u210 : p5201 := (Or.elim h8821 (fun q0 => (False.elim (q0 u207))) (fun r0 => r0));
    let u211 : p3389 := (Or.elim h8822 (fun q0 => q0) (fun r0 => (False.elim (r0 u207))));
    let u212 : p5085 := (Or.elim h8557 (fun q0 => (False.elim (q0 u208))) (fun r0 => r0));
    let u213 : (¬ p2417) := (Or.elim h46172 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u177))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u211))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u185))) (fun r3 => (False.elim (r3 u48))))))))));
    let u214 : (¬ p2911) := (Or.elim h46116 (fun q0 => (False.elim (q0 u120))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u177))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u211))) (fun r3 => (False.elim (r3 u185))))))))));
    let u215 : p2707 := (Or.elim h21328 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u177))) (fun r1 => (False.elim (r1 u212))))));
    let u216 : (¬ p3588) := (Or.elim h20121 (fun q0 => (False.elim (q0 u177))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u212))))));
    let u217 : (¬ p4639) := (Or.elim h7418 (fun q0 => (False.elim (u213 q0))) (fun r0 => r0));
    let u218 : (¬ p4923) := (Or.elim h8144 (fun q0 => (False.elim (u214 q0))) (fun r0 => r0));
    let u219 : (¬ p4792) := (Or.elim h7823 (fun q0 => (False.elim (u216 q0))) (fun r0 => r0));
    let u220 : p4634 := (Or.elim h66354 (fun q0 => q0) (fun r0 => (False.elim (u217 r0))));
    let u221 : p4921 := (Or.elim h66404 (fun q0 => (False.elim (u218 q0))) (fun r0 => r0));
    let u222 : p4795 := (Or.elim h66384 (fun q0 => (False.elim (u219 q0))) (fun r0 => r0));
    let u223 : p4637 := (Or.elim h7413 (fun q0 => (False.elim (q0 u220))) (fun r0 => r0));
    let u224 : p3644 := (Or.elim h8138 (fun q0 => q0) (fun r0 => (False.elim (r0 u221))));
    let u225 : p3576 := (Or.elim h7827 (fun q0 => q0) (fun r0 => (False.elim (r0 u222))));
    let u226 : (¬ p3548) := (Or.elim h58648 (fun q0 => (False.elim (q0 u135))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u209))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u101))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u177))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u143))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u225))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u185))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u114))) (fun r8 => (False.elim (r8 u32))))))))))))))))))));
    let u227 : (¬ p5304) := (Or.elim h9038 (fun q0 => (False.elim (u226 q0))) (fun r0 => r0));
    let u228 : p5306 := (Or.elim h66458 (fun q0 => (False.elim (u227 q0))) (fun r0 => r0));
    let u229 : p3527 := (Or.elim h9044 (fun q0 => q0) (fun r0 => (False.elim (r0 u228))));
    let u230 : (¬ p3659) := (Or.elim h49902 (fun q0 => (False.elim (q0 u143))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u229))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u203))) (fun r3 => (False.elim (r3 u32))))))))));
    let u231 : (¬ p4799) := (Or.elim h7840 (fun q0 => (False.elim (u230 q0))) (fun r0 => r0));
    let u232 : p4803 := (Or.elim h66385 (fun q0 => q0) (fun r0 => (False.elim (u231 r0))));
    let u233 : p2717 := (Or.elim h7846 (fun q0 => q0) (fun r0 => (False.elim (r0 u232))));
    let u234 : (¬ p3551) := (Or.elim h49693 (fun q0 => (False.elim (q0 u215))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u233))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u158))) (fun r3 => (False.elim (r3 u32))))))))));
    let u235 : (¬ p4586) := (Or.elim h7292 (fun q0 => (False.elim (u234 q0))) (fun r0 => r0));
    let u236 : p4589 := (Or.elim h66347 (fun q0 => q0) (fun r0 => (False.elim (u235 r0))));
    let u237 : p2341 := (Or.elim h7298 (fun q0 => q0) (fun r0 => (False.elim (r0 u236))));
    let u238 : (¬ p3346) := (Or.elim h52653 (fun q0 => (False.elim (q0 u237))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u224))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u223))) (fun r3 => (False.elim (r3 u210))))))))));
    let u239 : (¬ p5180) := (Or.elim h8776 (fun q0 => (False.elim (u238 q0))) (fun r0 => r0));
    let u240 : p5185 := (Or.elim h66444 (fun q0 => (False.elim (u239 q0))) (fun r0 => r0));
    let u241 : p3355 := (Or.elim h8782 (fun q0 => q0) (fun r0 => (False.elim (r0 u240))));
    let u242 : (¬ p3189) := (Or.elim h66742 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u229))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u224))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u197))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u196))) (fun r4 => (False.elim (r4 u179))))))))))));
    let u243 : (¬ p5077) := (Or.elim h8540 (fun q0 => (False.elim (u242 q0))) (fun r0 => r0));
    let u244 : p5073 := (Or.elim h66430 (fun q0 => q0) (fun r0 => (False.elim (u243 r0))));
    let u245 : p4360 := (Or.elim h8534 (fun q0 => q0) (fun r0 => (False.elim (r0 u244))));
    let u246 : (¬ p3564) := (Or.elim h57122 (fun q0 => (False.elim (q0 u209))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u28))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u177))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u185))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u142))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u133))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u245))) (fun r8 => (False.elim (r8 u32))))))))))))))))))));
    let u247 : (¬ p5323) := (Or.elim h9108 (fun q0 => (False.elim (u246 q0))) (fun r0 => r0));
    let u248 : p5320 := (Or.elim h66460 (fun q0 => q0) (fun r0 => (False.elim (u247 r0))));
    let u249 : p3746 := (Or.elim h9100 (fun q0 => q0) (fun r0 => (False.elim (r0 u248))));
    let u250 : p4137 := (Or.elim h9102 (fun q0 => q0) (fun r0 => (False.elim (r0 u248))));
    let u251 : (¬ p4191) := (Or.elim h44831 (fun q0 => (False.elim (q0 u154))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u182))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u250))) (fun r2 => r2))))));
    let u252 : (¬ p3246) := (Or.elim h41334 (fun q0 => (False.elim (q0 u135))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u250))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u116))) (fun r3 => (False.elim (r3 u114))))))))));
    let u253 : (¬ p5246) := (Or.elim h8928 (fun q0 => (False.elim (u251 q0))) (fun r0 => r0));
    let u254 : (¬ p5103) := (Or.elim h8615 (fun q0 => (False.elim (u252 q0))) (fun r0 => r0));
    let u255 : p5251 := (Or.elim h66452 (fun q0 => (False.elim (u253 q0))) (fun r0 => r0));
    let u256 : p5101 := (Or.elim h66436 (fun q0 => q0) (fun r0 => (False.elim (u254 r0))));
    let u257 : p3461 := (Or.elim h8934 (fun q0 => q0) (fun r0 => (False.elim (r0 u255))));
    let u258 : p3690 := (Or.elim h8609 (fun q0 => q0) (fun r0 => (False.elim (r0 u256))));
    let u259 : (¬ p4425) := (Or.elim h42566 (fun q0 => (False.elim (q0 u135))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u257))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u249))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u115))))))))));
    let u260 : (¬ p3941) := (Or.elim h41331 (fun q0 => (False.elim (q0 u233))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u258))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u138))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u100))) (fun r4 => (False.elim (r4 u183))))))))))));
    let u261 : (¬ p5125) := (Or.elim h8664 (fun q0 => (False.elim (u259 q0))) (fun r0 => r0));
    let u262 : (¬ p5561) := (Or.elim h9727 (fun q0 => (False.elim (u260 q0))) (fun r0 => r0));
    let u263 : p5130 := (Or.elim h66439 (fun q0 => (False.elim (u261 q0))) (fun r0 => r0));
    let u264 : p5555 := (Or.elim h66484 (fun q0 => q0) (fun r0 => (False.elim (u262 r0))));
    let u265 : p3276 := (Or.elim h8670 (fun q0 => q0) (fun r0 => (False.elim (r0 u263))));
    let u266 : p5558 := (Or.elim h9721 (fun q0 => (False.elim (q0 u264))) (fun r0 => r0));
    let u267 : (¬ p5568) := (Or.elim h53296 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u265))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u241))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u28))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u177))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u185))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u136))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u245))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u32))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u184))) (fun r9 => r9))))))))))))))))))));
    let u268 : (¬ p3969) := (Or.elim h41327 (fun q0 => (False.elim (q0 u120))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u102))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u114))) (fun r3 => (False.elim (r3 u266))))))))));
    let u269 : (¬ p5567) := (Or.elim h9791 (fun q0 => q0) (fun r0 => (False.elim (u267 r0))));
    let u270 : (¬ p5571) := (Or.elim h9797 (fun q0 => (False.elim (u268 q0))) (fun r0 => r0));
    (Or.elim h66485 (fun q0 => (False.elim (u269 q0))) (fun r0 => (False.elim (u270 r0)))))

theorem step66744 (p2132 p2135 p2138 p2142 p2747 p2810 p2811 p2946 p2963 p3365 p4315 p4500 p4619 p4703 p4704 p4714 p4785 p4903 p5048 p5050 p5051 : Prop)
    (h7591 : (¬ p4703) ∨ p4704)
    (h7804 : p2811 ∨ (¬ p4785))
    (h7805 : p3365 ∨ (¬ p4785))
    (h66743 : (¬ p4500) ∨ (¬ p2138) ∨ (¬ p4903) ∨ (¬ p4619) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p4714) ∨ (¬ p4703) ∨ (¬ p4785) ∨ (¬ p2747))
    (h20425 : (¬ p2811) ∨ (¬ p2946) ∨ (¬ p4315))
    (h2408 : (¬ p2135) ∨ p2138)
    (h8456 : p4315 ∨ (¬ p5048))
    (h66325 : p2135 ∨ p2142)
    (h66427 : p5048 ∨ p5050)
    (h2422 : p2132 ∨ (¬ p2142))
    (h8460 : (¬ p5050) ∨ p5051)
    (h48008 : (¬ p2132) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4704) ∨ (¬ p5051))
    : (¬ p4785) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p4714) ∨ (¬ p4703) ∨ (¬ p4903) ∨ (¬ p2810) ∨ (¬ p2747) ∨ (¬ p4619) ∨ (¬ p4500) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4785 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4714 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4703 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4903 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4500 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4704 := (Or.elim h7591 (fun q0 => (False.elim (q0 u4))) (fun r0 => r0));
    let u11 : p2811 := (Or.elim h7804 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u12 : p3365 := (Or.elim h7805 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u13 : (¬ p2138) := (Or.elim h66743 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u7))))))))))))))))))));
    let u14 : (¬ p4315) := (Or.elim h20425 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    let u15 : (¬ p2135) := (Or.elim h2408 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u16 : (¬ p5048) := (Or.elim h8456 (fun q0 => (False.elim (u14 q0))) (fun r0 => r0));
    let u17 : p2142 := (Or.elim h66325 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    let u18 : p5050 := (Or.elim h66427 (fun q0 => (False.elim (u16 q0))) (fun r0 => r0));
    let u19 : p2132 := (Or.elim h2422 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    let u20 : p5051 := (Or.elim h8460 (fun q0 => (False.elim (q0 u18))) (fun r0 => r0));
    (Or.elim h48008 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (False.elim (r3 u20)))))))))))

theorem step66749 (p2406 p2437 p2440 p2441 p2553 p2925 p2927 p2932 p2934 p3016 p3238 p3527 p3644 p4627 p4630 p4643 p4645 p4646 : Prop)
    (h28361 : (¬ p2927) ∨ (¬ p3527) ∨ (¬ p3644))
    (h3977 : (¬ p2925) ∨ p2927)
    (h66405 : p2932 ∨ p2925)
    (h3991 : (¬ p2932) ∨ p2934)
    (h3014 : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2441))
    (h46048 : (¬ p2406) ∨ (¬ p2440) ∨ (¬ p2553) ∨ (¬ p3016))
    (h7427 : p2441 ∨ (¬ p4643))
    (h7401 : p2406 ∨ (¬ p4630))
    (h66355 : p4643 ∨ p4645)
    (h66353 : p4627 ∨ p4630)
    (h7436 : (¬ p4645) ∨ p4646)
    (h7395 : p3238 ∨ (¬ p4627))
    (h48170 : (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p4646))
    : (¬ p2440) ∨ (¬ p3016) ∨ (¬ p2553) ∨ (¬ p3527) ∨ (¬ p2437) ∨ (¬ p3644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2927) := (Or.elim h28361 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u5))))));
    let u7 : (¬ p2925) := (Or.elim h3977 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u8 : p2932 := (Or.elim h66405 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u9 : p2934 := (Or.elim h3991 (fun q0 => (False.elim (q0 u8))) (fun r0 => r0));
    let u10 : (¬ p2441) := (Or.elim h3014 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => r1))));
    let u11 : (¬ p2406) := (Or.elim h46048 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1))))))));
    let u12 : (¬ p4643) := (Or.elim h7427 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    let u13 : (¬ p4630) := (Or.elim h7401 (fun q0 => (False.elim (u11 q0))) (fun r0 => r0));
    let u14 : p4645 := (Or.elim h66355 (fun q0 => (False.elim (u12 q0))) (fun r0 => r0));
    let u15 : p4627 := (Or.elim h66353 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u16 : p4646 := (Or.elim h7436 (fun q0 => (False.elim (q0 u14))) (fun r0 => r0));
    let u17 : p3238 := (Or.elim h7395 (fun q0 => q0) (fun r0 => (False.elim (r0 u15))));
    (Or.elim h48170 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u17))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u16)))))))))))

theorem step66750 (p3030 p3032 p3036 p3038 p3527 p3548 p3553 p4111 p4652 : Prop)
    (h9053 : (¬ p3527) ∨ (¬ p3548))
    (h29105 : (¬ p3032) ∨ p3548 ∨ (¬ p3553))
    (h52473 : (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4111) ∨ (¬ p4652))
    (h4184 : (¬ p3030) ∨ p3032)
    (h4198 : (¬ p3036) ∨ p3038)
    (h66416 : p3036 ∨ p3030)
    : (¬ p3553) ∨ (¬ p4111) ∨ (¬ p4652) ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3548) := (Or.elim h9053 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    let u5 : (¬ p3032) := (Or.elim h29105 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u0))))));
    let u6 : (¬ p3038) := (Or.elim h52473 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2))))))))));
    let u7 : (¬ p3030) := (Or.elim h4184 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u8 : (¬ p3036) := (Or.elim h4198 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h66416 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u7 r0)))))

theorem step66760 (p2241 p2244 p2247 p2251 p2685 p2737 p2747 p2748 p2761 p2996 p3266 p3365 p3434 p3506 p3585 p3588 p3848 p3873 p3947 p3954 p4025 p4118 p4191 p4278 p4324 p4360 p4381 p4444 p4477 p4653 p4655 p4659 p4661 p4732 p4749 p4776 p4777 p4780 p4822 p4827 p5115 p5120 p5227 p5232 p5281 p5284 p5287 : Prop)
    (h7681 : p3954 ∨ (¬ p4732))
    (h7679 : p3873 ∨ (¬ p4732))
    (h3620 : (¬ p2747) ∨ p2748)
    (h3622 : p2737 ∨ (¬ p2747))
    (h51535 : (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4749))
    (h28879 : (¬ p2685) ∨ (¬ p2748) ∨ (¬ p2996))
    (h46273 : (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4324))
    (h2639 : p2241 ∨ (¬ p2251))
    (h7794 : p2685 ∨ (¬ p4780))
    (h8893 : p4324 ∨ (¬ p5227))
    (h66336 : p2244 ∨ p2251)
    (h66382 : p4776 ∨ p4780)
    (h66450 : p5227 ∨ p5232)
    (h2625 : (¬ p2244) ∨ p2247)
    (h7787 : (¬ p4776) ∨ p4777)
    (h8899 : p3434 ∨ (¬ p5232))
    (h43941 : (¬ p2247) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4444))
    (h59241 : (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p3947) ∨ (¬ p4777))
    (h41192 : (¬ p2761) ∨ (¬ p3434) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4477))
    (h8646 : p4444 ∨ (¬ p5115))
    (h7464 : p3947 ∨ (¬ p4655))
    (h7908 : p2761 ∨ (¬ p4827))
    (h66438 : p5115 ∨ p5120)
    (h66357 : p4655 ∨ p4659)
    (h66390 : p4827 ∨ p4822)
    (h8652 : p3266 ∨ (¬ p5120))
    (h7469 : (¬ p4659) ∨ p4661)
    (h7902 : p4381 ∨ (¬ p4822))
    (h43940 : (¬ p2247) ∨ (¬ p3266) ∨ (¬ p3848) ∨ (¬ p5284))
    (h48368 : (¬ p3506) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4653) ∨ (¬ p4661))
    (h9002 : (¬ p5281) ∨ p5284)
    (h9008 : p3506 ∨ (¬ p5287))
    (h66456 : p5281 ∨ p5287)
    : (¬ p2747) ∨ (¬ p4191) ∨ (¬ p3848) ∨ (¬ p4118) ∨ (¬ p2996) ∨ (¬ p4360) ∨ (¬ p4025) ∨ (¬ p4278) ∨ (¬ p3365) ∨ (¬ p4653) ∨ (¬ p4749) ∨ (¬ p4477) ∨ (¬ p3585) ∨ (¬ p4732) ∨ (¬ p3588) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2747 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4732 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))));
    let u15 : p3954 := (Or.elim h7681 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u16 : p3873 := (Or.elim h7679 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u17 : p2748 := (Or.elim h3620 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u18 : p2737 := (Or.elim h3622 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u19 : (¬ p2241) := (Or.elim h51535 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u17))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u15))) (fun r3 => (False.elim (r3 u10))))))))));
    let u20 : (¬ p2685) := (Or.elim h28879 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u17))) (fun r1 => (False.elim (r1 u4))))));
    let u21 : (¬ p4324) := (Or.elim h46273 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u16))) (fun r3 => r3))))))));
    let u22 : (¬ p2251) := (Or.elim h2639 (fun q0 => (False.elim (u19 q0))) (fun r0 => r0));
    let u23 : (¬ p4780) := (Or.elim h7794 (fun q0 => (False.elim (u20 q0))) (fun r0 => r0));
    let u24 : (¬ p5227) := (Or.elim h8893 (fun q0 => (False.elim (u21 q0))) (fun r0 => r0));
    let u25 : p2244 := (Or.elim h66336 (fun q0 => q0) (fun r0 => (False.elim (u22 r0))));
    let u26 : p4776 := (Or.elim h66382 (fun q0 => q0) (fun r0 => (False.elim (u23 r0))));
    let u27 : p5232 := (Or.elim h66450 (fun q0 => (False.elim (u24 q0))) (fun r0 => r0));
    let u28 : p2247 := (Or.elim h2625 (fun q0 => (False.elim (q0 u25))) (fun r0 => r0));
    let u29 : p4777 := (Or.elim h7787 (fun q0 => (False.elim (q0 u26))) (fun r0 => r0));
    let u30 : p3434 := (Or.elim h8899 (fun q0 => q0) (fun r0 => (False.elim (r0 u27))));
    let u31 : (¬ p4444) := (Or.elim h43941 (fun q0 => (False.elim (q0 u28))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => r2))))));
    let u32 : (¬ p3947) := (Or.elim h59241 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u16))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u29))))))))))));
    let u33 : (¬ p2761) := (Or.elim h41192 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u30))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u11))))))))));
    let u34 : (¬ p5115) := (Or.elim h8646 (fun q0 => (False.elim (u31 q0))) (fun r0 => r0));
    let u35 : (¬ p4655) := (Or.elim h7464 (fun q0 => (False.elim (u32 q0))) (fun r0 => r0));
    let u36 : (¬ p4827) := (Or.elim h7908 (fun q0 => (False.elim (u33 q0))) (fun r0 => r0));
    let u37 : p5120 := (Or.elim h66438 (fun q0 => (False.elim (u34 q0))) (fun r0 => r0));
    let u38 : p4659 := (Or.elim h66357 (fun q0 => (False.elim (u35 q0))) (fun r0 => r0));
    let u39 : p4822 := (Or.elim h66390 (fun q0 => (False.elim (u36 q0))) (fun r0 => r0));
    let u40 : p3266 := (Or.elim h8652 (fun q0 => q0) (fun r0 => (False.elim (r0 u37))));
    let u41 : p4661 := (Or.elim h7469 (fun q0 => (False.elim (q0 u38))) (fun r0 => r0));
    let u42 : p4381 := (Or.elim h7902 (fun q0 => q0) (fun r0 => (False.elim (r0 u39))));
    let u43 : (¬ p5284) := (Or.elim h43940 (fun q0 => (False.elim (q0 u28))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u40))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    let u44 : (¬ p3506) := (Or.elim h48368 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u42))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (False.elim (r3 u41))))))))));
    let u45 : (¬ p5281) := (Or.elim h9002 (fun q0 => q0) (fun r0 => (False.elim (u43 r0))));
    let u46 : (¬ p5287) := (Or.elim h9008 (fun q0 => (False.elim (u44 q0))) (fun r0 => r0));
    (Or.elim h66456 (fun q0 => (False.elim (u45 q0))) (fun r0 => (False.elim (u46 r0)))))

theorem step66765 (p2247 p2925 p2927 p2932 p2934 p3527 p3644 p3742 p4111 p4809 p4812 p4814 : Prop)
    (h28361 : (¬ p2927) ∨ (¬ p3527) ∨ (¬ p3644))
    (h3977 : (¬ p2925) ∨ p2927)
    (h66405 : p2932 ∨ p2925)
    (h3991 : (¬ p2932) ∨ p2934)
    (h43271 : (¬ p2247) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4111))
    (h62842 : (¬ p2934) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4814))
    (h7857 : p4111 ∨ (¬ p4809))
    (h7865 : (¬ p4812) ∨ p4814)
    (h66386 : p4809 ∨ p4812)
    : (¬ p3742) ∨ (¬ p2247) ∨ (¬ p3644) ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3742 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2927) := (Or.elim h28361 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2))))));
    let u5 : (¬ p2925) := (Or.elim h3977 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u6 : p2932 := (Or.elim h66405 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u7 : p2934 := (Or.elim h3991 (fun q0 => (False.elim (q0 u6))) (fun r0 => r0));
    let u8 : (¬ p4111) := (Or.elim h43271 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => r2))))));
    let u9 : (¬ p4814) := (Or.elim h62842 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => r3))))))));
    let u10 : (¬ p4809) := (Or.elim h7857 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : (¬ p4812) := (Or.elim h7865 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h66386 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u11 r0)))))

theorem step66767 (p2341 p2437 p2473 p2476 p2480 p2481 p2936 p3389 p3527 p3540 p3960 p4256 p4383 p4586 p4589 p5196 p5200 p5203 : Prop)
    (h9914 : (¬ p3389) ∨ (¬ p3540))
    (h54756 : (¬ p2476) ∨ (¬ p2936) ∨ (¬ p3389) ∨ (¬ p3527) ∨ (¬ p4383))
    (h8816 : p3540 ∨ (¬ p5196))
    (h3079 : (¬ p2473) ∨ p2476)
    (h66446 : p5196 ∨ p5200)
    (h66359 : p2480 ∨ p2473)
    (h8824 : (¬ p5200) ∨ p5203)
    (h3091 : (¬ p2480) ∨ p2481)
    (h41713 : (¬ p2341) ∨ (¬ p2437) ∨ (¬ p4256) ∨ (¬ p4383) ∨ (¬ p5203))
    (h57274 : (¬ p2437) ∨ (¬ p2481) ∨ (¬ p2936) ∨ (¬ p3527) ∨ (¬ p3960) ∨ (¬ p4256))
    (h7298 : p2341 ∨ (¬ p4589))
    (h7291 : p3960 ∨ (¬ p4586))
    (h66347 : p4589 ∨ p4586)
    : (¬ p3389) ∨ (¬ p4256) ∨ (¬ p2437) ∨ (¬ p2936) ∨ (¬ p4383) ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2936 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3540) := (Or.elim h9914 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u7 : (¬ p2476) := (Or.elim h54756 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4))))))))));
    let u8 : (¬ p5196) := (Or.elim h8816 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    let u9 : (¬ p2473) := (Or.elim h3079 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u10 : p5200 := (Or.elim h66446 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    let u11 : p2480 := (Or.elim h66359 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u12 : p5203 := (Or.elim h8824 (fun q0 => (False.elim (q0 u10))) (fun r0 => r0));
    let u13 : p2481 := (Or.elim h3091 (fun q0 => (False.elim (q0 u11))) (fun r0 => r0));
    let u14 : (¬ p2341) := (Or.elim h41713 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u12))))))))));
    let u15 : (¬ p3960) := (Or.elim h57274 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    let u16 : (¬ p4589) := (Or.elim h7298 (fun q0 => (False.elim (u14 q0))) (fun r0 => r0));
    let u17 : (¬ p4586) := (Or.elim h7291 (fun q0 => (False.elim (u15 q0))) (fun r0 => r0));
    (Or.elim h66347 (fun q0 => (False.elim (u16 q0))) (fun r0 => (False.elim (u17 r0)))))

theorem step66768 (p2249 p2437 p2654 p2655 p2661 p2662 p2727 p3540 : Prop)
    (h6371 : (¬ p2437) ∨ (¬ p2662) ∨ (¬ p3540))
    (h48667 : (¬ p2249) ∨ (¬ p2437) ∨ (¬ p2655) ∨ (¬ p2727) ∨ (¬ p3540))
    (h3447 : (¬ p2661) ∨ p2662)
    (h3433 : (¬ p2654) ∨ p2655)
    (h66378 : p2654 ∨ p2661)
    : (¬ p3540) ∨ (¬ p2437) ∨ (¬ p2727) ∨ (¬ p2249) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3540 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2662) := (Or.elim h6371 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u0))))));
    let u5 : (¬ p2655) := (Or.elim h48667 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0))))))))));
    let u6 : (¬ p2661) := (Or.elim h3447 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : (¬ p2654) := (Or.elim h3433 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h66378 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step66770 (p2230 p3362 p3365 p3684 p3759 p4726 p4728 p4752 : Prop)
    (h19839 : (¬ p2230) ∨ (¬ p3684) ∨ (¬ p3759))
    (h41082 : (¬ p2230) ∨ (¬ p3362) ∨ (¬ p3365) ∨ (¬ p3684) ∨ (¬ p4752))
    (h7663 : p3759 ∨ (¬ p4726))
    (h7669 : p3362 ∨ (¬ p4728))
    (h66373 : p4728 ∨ p4726)
    : (¬ p3684) ∨ (¬ p2230) ∨ (¬ p4752) ∨ (¬ p3365) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3684 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3759) := (Or.elim h19839 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => r1))));
    let u5 : (¬ p3362) := (Or.elim h41082 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2))))))))));
    let u6 : (¬ p4726) := (Or.elim h7663 (fun q0 => (False.elim (u4 q0))) (fun r0 => r0));
    let u7 : (¬ p4728) := (Or.elim h7669 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    (Or.elim h66373 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step66771 (p2437 p2573 p3016 p3083 p3097 p3573 p3574 p3581 p4186 p4710 p4971 p4974 p5875 p5876 : Prop)
    (h8280 : p3016 ∨ (¬ p4974))
    (h36597 : p3016 ∨ (¬ p3083) ∨ (¬ p3573))
    (h66415 : p4974 ∨ p4971)
    (h32074 : p3573 ∨ (¬ p3581) ∨ (¬ p4186))
    (h8274 : p3574 ∨ (¬ p4971))
    (h12242 : p3581 ∨ p5875)
    (h46891 : (¬ p2437) ∨ (¬ p2573) ∨ (¬ p3097) ∨ (¬ p3574) ∨ (¬ p4710))
    (h66533 : (¬ p5876) ∨ (¬ p5875))
    (h12246 : p4710 ∨ p5876)
    : p3016 ∨ (¬ p3097) ∨ (¬ p2573) ∨ (¬ p3083) ∨ (¬ p4186) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4974) := (Or.elim h8280 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u7 : (¬ p3573) := (Or.elim h36597 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => r1))));
    let u8 : p4971 := (Or.elim h66415 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    let u9 : (¬ p3581) := (Or.elim h32074 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u4))))));
    let u10 : p3574 := (Or.elim h8274 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u11 : p5875 := (Or.elim h12242 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u12 : (¬ p4710) := (Or.elim h46891 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => r3))))))));
    let u13 : (¬ p5876) := (Or.elim h66533 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    (Or.elim h12246 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u13 r0)))))

theorem step66773 (p2138 p3055 p3367 p3425 p3471 p4136 p4235 p4344 p4893 p4896 p5256 p5259 : Prop)
    (h8945 : p3425 ∨ (¬ p5256))
    (h19003 : (¬ p2138) ∨ p3425 ∨ (¬ p4136))
    (h66453 : p5259 ∨ p5256)
    (h8066 : p4136 ∨ (¬ p4893))
    (h8951 : p3471 ∨ (¬ p5259))
    (h66400 : p4896 ∨ p4893)
    (h46228 : (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3471) ∨ (¬ p4235) ∨ (¬ p4344))
    (h8072 : p4344 ∨ (¬ p4896))
    : p3425 ∨ (¬ p2138) ∨ (¬ p4235) ∨ (¬ p3367) ∨ (¬ p3055) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : p2138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5256) := (Or.elim h8945 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u6 : (¬ p4136) := (Or.elim h19003 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => r1))));
    let u7 : p5259 := (Or.elim h66453 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u8 : (¬ p4893) := (Or.elim h8066 (fun q0 => (False.elim (u6 q0))) (fun r0 => r0));
    let u9 : p3471 := (Or.elim h8951 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u10 : p4896 := (Or.elim h66400 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u11 : (¬ p4344) := (Or.elim h46228 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h8072 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u10)))))

theorem step66777 (p2191 p2192 p3369 p3555 p3646 p3989 p4173 p4347 p4505 p4506 p4511 p4515 p4520 : Prop)
    (h7073 : p3989 ∨ (¬ p4505))
    (h7072 : (¬ p4505) ∨ p4506)
    (h7107 : p3555 ∨ (¬ p4520))
    (h7105 : p3369 ∨ (¬ p4520))
    (h45034 : (¬ p2191) ∨ (¬ p2192) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p4347) ∨ (¬ p4506))
    (h44977 : (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4347))
    (h7096 : p2192 ∨ (¬ p4515))
    (h7090 : p4173 ∨ (¬ p4511))
    (h66332 : p4511 ∨ p4515)
    : (¬ p4347) ∨ (¬ p4505) ∨ (¬ p4520) ∨ (¬ p2191) ∨ (¬ p3646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4347 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4520 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3989 := (Or.elim h7073 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p4506 := (Or.elim h7072 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u7 : p3555 := (Or.elim h7107 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u8 : p3369 := (Or.elim h7105 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u9 : (¬ p2192) := (Or.elim h45034 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u6))))))))))));
    let u10 : (¬ p4173) := (Or.elim h44977 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u0))))))));
    let u11 : (¬ p4515) := (Or.elim h7096 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u12 : (¬ p4511) := (Or.elim h7090 (fun q0 => (False.elim (u10 q0))) (fun r0 => r0));
    (Or.elim h66332 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u11 r0)))))

end ElevenRUP
