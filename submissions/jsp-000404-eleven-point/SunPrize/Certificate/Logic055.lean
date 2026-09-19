import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step103587 (p2088 p2220 p2284 p2946 p3136 p3146 p5048 : Prop)
    (h73892 : p5048 ∨ p3136)
    (h70412 : (¬ p2946) ∨ (¬ p5048) ∨ (¬ p2220) ∨ (¬ p2088) ∨ (¬ p2284) ∨ (¬ p3146))
    : (¬ p3146) ∨ (¬ p2088) ∨ (¬ p2220) ∨ p3136 ∨ (¬ p2284) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5048 := (Or.elim h73892 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70412 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step103596 (p2088 p2363 p2563 p2696 p2737 p2747 p3365 p4602 p4714 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73302 : p2747 ∨ (¬ p2737))
    (h73662 : p4602 ∨ (¬ p2363))
    (h73720 : p4714 ∨ p2563)
    (h70006 : (¬ p2747) ∨ (¬ p3365) ∨ (¬ p4714) ∨ (¬ p2088) ∨ (¬ p4602))
    : p2696 ∨ (¬ p2737) ∨ (¬ p2363) ∨ p2563 ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u8 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70006 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step103600 (p2122 p2230 p2363 p2440 p2459 p2528 p2553 p2588 p2608 p2819 p4203 p4358 p4401 p4433 p4667 p4732 p4753 p4846 : Prop)
    (h73732 : p4732 ∨ p2608)
    (h73698 : p4667 ∨ (¬ p2459))
    (h73564 : p4358 ∨ p2819)
    (h73282 : p2588 ∨ p2553)
    (h70560 : (¬ p2122) ∨ (¬ p4401) ∨ (¬ p4846) ∨ (¬ p4433) ∨ (¬ p4203) ∨ (¬ p2588) ∨ (¬ p2363) ∨ (¬ p4753) ∨ (¬ p2230) ∨ (¬ p4358) ∨ (¬ p2440) ∨ (¬ p2528) ∨ (¬ p4667) ∨ (¬ p4732))
    : p2608 ∨ (¬ p2122) ∨ (¬ p4401) ∨ (¬ p2459) ∨ (¬ p4433) ∨ p2819 ∨ (¬ p4203) ∨ p2553 ∨ (¬ p2230) ∨ (¬ p4753) ∨ (¬ p2363) ∨ (¬ p4846) ∨ (¬ p2440) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u15 : p4667 := (Or.elim h73698 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u16 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u17 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h70560 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u17))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u16))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u12))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u13))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u15))) (fun r12 => (False.elim (r12 u14)))))))))))))))))))))))))))))

theorem step103602 (p2132 p2138 p2210 p2608 p4732 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73732 : p4732 ∨ p2608)
    (h70173 : (¬ p4732) ∨ (¬ p2138) ∨ (¬ p2210))
    : p2132 ∨ p2608 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70173 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step103603 (p2274 p2307 p2363 p2608 p2737 p2747 p4557 p4602 p4732 : Prop)
    (h73732 : p4732 ∨ p2608)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73302 : p2747 ∨ (¬ p2737))
    (h73636 : p4557 ∨ (¬ p2274))
    (h71235 : (¬ p4602) ∨ (¬ p4732) ∨ (¬ p2747) ∨ (¬ p2307) ∨ (¬ p4557))
    : p2608 ∨ (¬ p2307) ∨ (¬ p2363) ∨ (¬ p2737) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u7 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u8 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h71235 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step103605 (p2156 p2220 p2274 p2608 p2737 p2747 p3146 p3646 p4530 p4557 p4732 : Prop)
    (h73302 : p2747 ∨ (¬ p2737))
    (h73636 : p4557 ∨ (¬ p2274))
    (h73620 : p4530 ∨ (¬ p2220))
    (h73436 : p3646 ∨ p2156)
    (h73732 : p4732 ∨ p2608)
    (h71227 : (¬ p4530) ∨ (¬ p3146) ∨ (¬ p4732) ∨ (¬ p2747) ∨ (¬ p4557) ∨ (¬ p3646))
    : (¬ p2737) ∨ (¬ p2274) ∨ (¬ p3146) ∨ (¬ p2220) ∨ p2156 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u8 : p4530 := (Or.elim h73620 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71227 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u9)))))))))))))

theorem step103607 (p2295 p2363 p3256 p3568 p4347 p4405 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73416 : p3568 ∨ p2295)
    (h71098 : (¬ p3256) ∨ (¬ p4347) ∨ (¬ p3568) ∨ (¬ p4405))
    : (¬ p3256) ∨ p2363 ∨ (¬ p4405) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71098 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step103610 (p2122 p2274 p2363 p2440 p2459 p3146 p3692 p3822 p4347 p4557 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73560 : p4347 ∨ p2363)
    (h73448 : p3692 ∨ p3146)
    (h73636 : p4557 ∨ (¬ p2274))
    (h70985 : (¬ p4557) ∨ (¬ p3692) ∨ (¬ p3822) ∨ (¬ p2459) ∨ (¬ p4347) ∨ (¬ p2440))
    : p2122 ∨ p2363 ∨ (¬ p2459) ∨ p3146 ∨ (¬ p2440) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h70985 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step103615 (p2352 p2363 p3146 p3956 p3958 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73500 : p3956 ∨ p2352)
    (h70400 : (¬ p4347) ∨ (¬ p3958) ∨ (¬ p3146) ∨ (¬ p3956))
    : p2363 ∨ (¬ p3146) ∨ p2352 ∨ (¬ p3958) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70400 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103617 (p2352 p2363 p2573 p2579 p2651 p2657 p3083 p4256 p4347 p4594 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73274 : p2579 ∨ p2573)
    (h73288 : p2657 ∨ p2651)
    (h73542 : p4256 ∨ p3083)
    (h73656 : p4594 ∨ p2352)
    (h70641 : (¬ p4347) ∨ (¬ p4256) ∨ (¬ p2579) ∨ (¬ p4594) ∨ (¬ p2657))
    : p2363 ∨ p2573 ∨ p2651 ∨ p3083 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4594 := (Or.elim h73656 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70641 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step103618 (p2230 p2440 p2542 p2589 p2727 p4812 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73772 : p4812 ∨ (¬ p2727))
    (h73284 : p2589 ∨ p2230)
    (h69868 : (¬ p4812) ∨ (¬ p2542) ∨ (¬ p2589))
    : p2440 ∨ (¬ p2727) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4812 := (Or.elim h73772 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69868 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u5)))))))

theorem step103619 (p2132 p2138 p2230 p2440 p2542 p2589 p2630 p2696 p4748 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h73740 : p4748 ∨ p2630)
    (h69864 : (¬ p2696) ∨ (¬ p2138) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p4748))
    : p2132 ∨ p2440 ∨ p2230 ∨ p2630 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4748 := (Or.elim h73740 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69864 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step103621 (p2274 p2440 p2563 p2630 p2696 p2737 p2747 p3365 p4557 p4703 p4716 p4748 : Prop)
    (h73302 : p2747 ∨ (¬ p2737))
    (h73636 : p4557 ∨ (¬ p2274))
    (h73714 : p4703 ∨ p2440)
    (h73722 : p4716 ∨ (¬ p2563))
    (h73390 : p3365 ∨ p2696)
    (h73740 : p4748 ∨ p2630)
    (h70455 : (¬ p4703) ∨ (¬ p4748) ∨ (¬ p4557) ∨ (¬ p3365) ∨ (¬ p4716) ∨ (¬ p2747))
    : (¬ p2737) ∨ (¬ p2274) ∨ p2440 ∨ (¬ p2563) ∨ p2696 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u8 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4748 := (Or.elim h73740 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70455 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step103622 (p2427 p2440 p2630 p2881 p2946 p2952 p4703 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73714 : p4703 ∨ p2440)
    (h70148 : (¬ p4703) ∨ (¬ p2630) ∨ (¬ p2952) ∨ (¬ p2427) ∨ (¬ p2881))
    : (¬ p2427) ∨ (¬ p2881) ∨ (¬ p2630) ∨ p2946 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70148 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step103623 (p2440 p2651 p2727 p2901 p2996 p4703 : Prop)
    (h73714 : p4703 ∨ p2440)
    (h70102 : (¬ p4703) ∨ (¬ p2651) ∨ (¬ p2996) ∨ (¬ p2727) ∨ p2901)
    : (¬ p2996) ∨ (¬ p2651) ∨ (¬ p2727) ∨ p2901 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70102 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step103627 (p2241 p2493 p2499 p2630 p2797 p2810 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73316 : p2810 ∨ p2630)
    (h70959 : (¬ p2810) ∨ (¬ p2241) ∨ (¬ p2499) ∨ (¬ p2797))
    : (¬ p2797) ∨ (¬ p2241) ∨ p2493 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70959 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step103629 (p2241 p2608 p2630 p2651 p2750 p2810 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73316 : p2810 ∨ p2630)
    (h69840 : (¬ p3954) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2810) ∨ (¬ p2651))
    : (¬ p2241) ∨ p2608 ∨ (¬ p2750) ∨ p2630 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69840 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103633 (p2246 p2249 p2727 p2751 p2870 p2891 p3136 p3413 p4244 p4315 p4392 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73550 : p4315 ∨ p3136)
    (h69906 : (¬ p2727) ∨ (¬ p4315) ∨ (¬ p4392) ∨ (¬ p3413) ∨ (¬ p2891) ∨ (¬ p4244) ∨ (¬ p2249) ∨ (¬ p2246) ∨ (¬ p2751))
    : (¬ p2246) ∨ p2870 ∨ (¬ p3413) ∨ (¬ p4392) ∨ p3136 ∨ (¬ p2891) ∨ (¬ p2727) ∨ (¬ p2249) ∨ (¬ p2751) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69906 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step103634 (p2156 p2192 p2891 p2992 p3051 p3136 p3486 p4173 p4956 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h73850 : p4956 ∨ p2992)
    (h73398 : p3486 ∨ p2891)
    (h70296 : (¬ p3136) ∨ (¬ p3051) ∨ (¬ p4956) ∨ (¬ p4173) ∨ (¬ p2156) ∨ (¬ p3486))
    : (¬ p3051) ∨ (¬ p2156) ∨ p2192 ∨ p2992 ∨ (¬ p3136) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4956 := (Or.elim h73850 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70296 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u8)))))))))))))

theorem step103635 (p2156 p2192 p2274 p2630 p2992 p3097 p3136 p4173 p4487 p4956 : Prop)
    (h73850 : p4956 ∨ p2992)
    (h73352 : p3097 ∨ p2274)
    (h73528 : p4173 ∨ p2192)
    (h73596 : p4487 ∨ (¬ p2156))
    (h70297 : p3136 ∨ (¬ p4956) ∨ (¬ p4173) ∨ (¬ p3097) ∨ (¬ p4487) ∨ (¬ p2630))
    : p2992 ∨ p2274 ∨ p3136 ∨ (¬ p2630) ∨ p2192 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4956 := (Or.elim h73850 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p4487 := (Or.elim h73596 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h70297 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step103641 (p2230 p2274 p2295 p2363 p2427 p2459 p2528 p2589 p2685 p2696 p2761 p2797 p3156 p3346 p3497 p3550 p3568 p3657 p3875 p3920 p4171 p4235 p4347 p4348 p4368 p4381 p4438 p4694 p4702 p4729 p4826 p4905 p4973 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73710 : p4694 ∨ (¬ p2528))
    (h73400 : p3497 ∨ p3156)
    (h73416 : p3568 ∨ p2295)
    (h73574 : p4381 ∨ p2761)
    (h73284 : p2589 ∨ p2230)
    (h73536 : p4235 ∨ p2427)
    (h73562 : p4348 ∨ p2459)
    (h71077 : (¬ p4694) ∨ (¬ p4826) ∨ (¬ p4381) ∨ (¬ p3346) ∨ (¬ p4347) ∨ (¬ p4171) ∨ (¬ p2685) ∨ (¬ p2797) ∨ (¬ p2696) ∨ (¬ p4729) ∨ (¬ p2589) ∨ (¬ p4368) ∨ (¬ p3497) ∨ (¬ p4438) ∨ (¬ p3875) ∨ (¬ p3550) ∨ (¬ p4905) ∨ (¬ p4348) ∨ (¬ p3657) ∨ (¬ p2274) ∨ (¬ p4702) ∨ (¬ p4235) ∨ (¬ p4973) ∨ (¬ p3568) ∨ (¬ p3920))
    : p2363 ∨ (¬ p2528) ∨ (¬ p3920) ∨ (¬ p4368) ∨ p3156 ∨ (¬ p4171) ∨ (¬ p2696) ∨ (¬ p4729) ∨ p2295 ∨ (¬ p2797) ∨ (¬ p4826) ∨ (¬ p2685) ∨ p2761 ∨ (¬ p4438) ∨ (¬ p3875) ∨ (¬ p3550) ∨ (¬ p4905) ∨ (¬ p3346) ∨ p2230 ∨ (¬ p2274) ∨ (¬ p4702) ∨ p2427 ∨ (¬ p4973) ∨ p2459 ∨ (¬ p3657) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))))));
    let u25 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u26 : p4694 := (Or.elim h73710 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u27 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u28 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u29 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    let u30 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u18 r0))));
    let u31 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u21 r0))));
    let u32 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u23 r0))));
    (Or.elim h71077 (fun q0 => (False.elim (q0 u26))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u29))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u17))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u25))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u30))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u3))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u27))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u13))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u14))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u15))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u16))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u32))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u24))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u19))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u20))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u31))) (fun r21 => (Or.elim r21 (fun q22 => (False.elim (q22 u22))) (fun r22 => (Or.elim r22 (fun q23 => (False.elim (q23 u28))) (fun r23 => (False.elim (r23 u2)))))))))))))))))))))))))))))))))))))))))))))))))))

theorem step103642 (p2132 p2166 p2696 p2737 p2743 p2753 p3156 p3365 p3497 p5052 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73298 : p2743 ∨ p2737)
    (h73390 : p3365 ∨ p2696)
    (h71063 : (¬ p2132) ∨ (¬ p2743) ∨ (¬ p3365) ∨ (¬ p2166) ∨ (¬ p5052) ∨ (¬ p2753) ∨ (¬ p3497))
    : (¬ p2753) ∨ (¬ p2132) ∨ (¬ p5052) ∨ p3156 ∨ p2737 ∨ (¬ p2166) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71063 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u7)))))))))))))))

theorem step103646 (p2459 p2528 p2534 p3146 p3212 p4348 p4539 p4607 p4905 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73562 : p4348 ∨ p2459)
    (h70230 : (¬ p3146) ∨ (¬ p3212) ∨ (¬ p4607) ∨ (¬ p4539) ∨ (¬ p2534) ∨ (¬ p4905) ∨ (¬ p4348))
    : (¬ p3212) ∨ (¬ p4905) ∨ (¬ p4539) ∨ (¬ p4607) ∨ p2528 ∨ (¬ p3146) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h70230 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u8)))))))))))))))

theorem step103664 (p2156 p2284 p3051 p3246 p3556 p3690 p4562 : Prop)
    (h73638 : p4562 ∨ p2284)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h70299 : (¬ p3556) ∨ (¬ p4562) ∨ (¬ p3690) ∨ (¬ p2156))
    : p2284 ∨ p3246 ∨ (¬ p2156) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4562 := (Or.elim h73638 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70299 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step103665 (p2331 p2641 p2727 p3379 p3452 p4755 p4809 p4975 : Prop)
    (h73744 : p4755 ∨ p2641)
    (h73394 : p3452 ∨ p3379)
    (h73770 : p4809 ∨ p2727)
    (h70037 : (¬ p4755) ∨ (¬ p3452) ∨ (¬ p4809) ∨ (¬ p4975) ∨ (¬ p2331))
    : p2641 ∨ p3379 ∨ (¬ p2331) ∨ (¬ p4975) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4755 := (Or.elim h73744 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70037 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step103666 (p2406 p2427 p2440 p2641 p2727 p2922 p2928 p4555 p4643 p4703 p4809 : Prop)
    (h73684 : p4643 ∨ p2427)
    (h73714 : p4703 ∨ p2440)
    (h73770 : p4809 ∨ p2727)
    (h73320 : p2928 ∨ p2922)
    (h70023 : (¬ p2928) ∨ (¬ p4643) ∨ (¬ p2406) ∨ (¬ p4703) ∨ (¬ p2641) ∨ (¬ p4555) ∨ (¬ p4809))
    : (¬ p2641) ∨ (¬ p2406) ∨ p2427 ∨ p2440 ∨ p2727 ∨ (¬ p4555) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4643 := (Or.elim h73684 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h70023 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u9)))))))))))))))

theorem step103674 (p2246 p2427 p2563 p2727 p2891 p2946 p2956 p4111 p4235 p4704 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73334 : p2956 ∨ (¬ p2946))
    (h73046 : p4704)
    (h73536 : p4235 ∨ p2427)
    (h69907 : (¬ p2956) ∨ (¬ p4111) ∨ (¬ p4704) ∨ (¬ p2891) ∨ (¬ p4235) ∨ (¬ p2246) ∨ (¬ p2563))
    : (¬ p2246) ∨ p2727 ∨ (¬ p2563) ∨ (¬ p2891) ∨ (¬ p2946) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2956 := (Or.elim h73334 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u8 : p4704 := h73046;
    let u9 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h69907 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step103678 (p2230 p2274 p2331 p2373 p2459 p2589 p2630 p2651 p2662 p2727 p2810 p2963 p3166 p4111 p4557 p4665 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73636 : p4557 ∨ (¬ p2274))
    (h73284 : p2589 ∨ p2230)
    (h73696 : p4665 ∨ p2459)
    (h73316 : p2810 ∨ p2630)
    (h73338 : p2963 ∨ p2331)
    (h69801 : (¬ p2810) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p4665) ∨ (¬ p4557) ∨ (¬ p2373) ∨ (¬ p2662) ∨ (¬ p2589) ∨ (¬ p4111))
    : (¬ p3166) ∨ p2727 ∨ (¬ p2274) ∨ p2230 ∨ (¬ p2373) ∨ p2459 ∨ p2630 ∨ (¬ p2651) ∨ (¬ p2662) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u12 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p4665 := (Or.elim h73696 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u14 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u15 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h69801 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step103686 (p2255 p2341 p2807 p2996 p3030 p3527 p3548 p4104 : Prop)
    (h73342 : p3030 ∨ (¬ p2996))
    (h73404 : p3548 ∨ p3527)
    (h70486 : (¬ p3030) ∨ (¬ p3548) ∨ (¬ p2341) ∨ (¬ p2807) ∨ (¬ p4104) ∨ (¬ p2255))
    : (¬ p2996) ∨ (¬ p2341) ∨ (¬ p4104) ∨ (¬ p2807) ∨ p3527 ∨ (¬ p2255) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3030 := (Or.elim h73342 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70486 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step103691 (p2440 p2542 p2829 p2839 p2850 p3583 p4390 p4717 p4750 p4880 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73806 : p4880 ∨ p2850)
    (h73270 : p2542 ∨ p2440)
    (h70648 : (¬ p4880) ∨ (¬ p3583) ∨ (¬ p2829) ∨ (¬ p4390) ∨ (¬ p2542) ∨ (¬ p4750) ∨ (¬ p4717))
    : (¬ p2829) ∨ p2839 ∨ (¬ p4390) ∨ p2850 ∨ p2440 ∨ (¬ p4750) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4880 := (Or.elim h73806 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70648 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step103692 (p2696 p2992 p3136 p3365 p4315 p4734 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73390 : p3365 ∨ p2696)
    (h72735 : p4734)
    (h71145 : (¬ p4315) ∨ (¬ p3365) ∨ (¬ p2992) ∨ (¬ p4734))
    : p3136 ∨ (¬ p2992) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4734 := h72735;
    (Or.elim h71145 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103694 (p2241 p2247 p2307 p2313 p2331 p2509 p2528 p2553 p2668 p2696 p2797 p2901 p3093 p3591 p4579 p4694 p4718 p4733 p4788 p4840 p4906 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73760 : p4788 ∨ (¬ p2696))
    (h73710 : p4694 ∨ (¬ p2528))
    (h73226 : p2247 ∨ p2241)
    (h73648 : p4579 ∨ p2331)
    (h73238 : p2313 ∨ p2307)
    (h73786 : p4840 ∨ p2797)
    (h71203 : (¬ p2313) ∨ (¬ p4718) ∨ (¬ p4906) ∨ (¬ p2901) ∨ (¬ p2247) ∨ (¬ p4579) ∨ (¬ p4840) ∨ (¬ p2668) ∨ (¬ p4733) ∨ (¬ p2509) ∨ (¬ p4694) ∨ (¬ p4788) ∨ (¬ p3591) ∨ (¬ p2553))
    : p3093 ∨ (¬ p2509) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2528) ∨ (¬ p2901) ∨ p2241 ∨ (¬ p4718) ∨ p2331 ∨ (¬ p4906) ∨ (¬ p4733) ∨ p2307 ∨ (¬ p2553) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u15 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u16 : p4694 := (Or.elim h73710 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u17 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u18 : p4579 := (Or.elim h73648 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u19 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u20 : p4840 := (Or.elim h73786 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    (Or.elim h71203 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u17))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u18))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u20))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u16))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u15))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u14))) (fun r12 => (False.elim (r12 u12)))))))))))))))))))))))))))))

theorem step103701 (p2255 p2406 p2440 p2542 p2651 p3238 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73374 : p3238 ∨ p2406)
    (h70376 : (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2255) ∨ (¬ p3238))
    : (¬ p2651) ∨ (¬ p2255) ∨ p2440 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70376 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103713 (p2528 p3016 p3256 p3574 p4598 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h70819 : p2528 ∨ (¬ p3256) ∨ (¬ p4598) ∨ (¬ p3574))
    : (¬ p3256) ∨ p2528 ∨ p3016 ∨ (¬ p4598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70819 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103718 (p2668 p3256 p3323 p4118 p4341 : Prop)
    (h73519 : (¬ p3256) ∨ (¬ p4118))
    (h69774 : p3323 ∨ (¬ p4341) ∨ (¬ p2668) ∨ p4118)
    : (¬ p3256) ∨ (¬ p2668) ∨ (¬ p4341) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4118) := (Or.elim h73519 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h69774 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u4 r2)))))))))

theorem step103721 (p2274 p2373 p2553 p3093 p3097 p3591 p3660 p3880 p4338 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73352 : p3097 ∨ p2274)
    (h73490 : p3880 ∨ p2373)
    (h71120 : (¬ p3880) ∨ (¬ p4338) ∨ (¬ p3097) ∨ (¬ p3660) ∨ (¬ p3591) ∨ (¬ p2553))
    : p3093 ∨ (¬ p2553) ∨ (¬ p4338) ∨ p2274 ∨ p2373 ∨ (¬ p3660) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71120 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step103724 (p2220 p2373 p2850 p3684 p3880 p4730 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73442 : p3684 ∨ p2850)
    (h70403 : (¬ p3880) ∨ (¬ p3684) ∨ (¬ p4730) ∨ (¬ p2220))
    : (¬ p2220) ∨ p2373 ∨ (¬ p4730) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70403 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step103729 (p2264 p2341 p2528 p2911 p3246 p3363 p3367 p3389 p3461 p3540 p3551 p3553 p3585 p3690 p4140 p4191 p4327 p4692 p4712 p4923 p5197 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73408 : p3551 ∨ p2341)
    (h73708 : p4692 ∨ p2528)
    (h73410 : p3553 ∨ p2264)
    (h73428 : p3585 ∨ p3367)
    (h73402 : p3540 ∨ p3389)
    (h73832 : p4923 ∨ (¬ p2911))
    (h73446 : p3690 ∨ p3246)
    (h70489 : (¬ p4923) ∨ (¬ p3540) ∨ (¬ p5197) ∨ (¬ p4327) ∨ (¬ p3363) ∨ (¬ p4692) ∨ (¬ p4191) ∨ (¬ p4712) ∨ (¬ p4140) ∨ (¬ p3585) ∨ (¬ p3690) ∨ (¬ p3553) ∨ (¬ p3551))
    : p3461 ∨ p2341 ∨ p2528 ∨ (¬ p3363) ∨ p2264 ∨ (¬ p4327) ∨ p3367 ∨ p3389 ∨ (¬ p5197) ∨ (¬ p4712) ∨ (¬ p2911) ∨ (¬ p4140) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4327 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u14 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u15 : p4692 := (Or.elim h73708 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u16 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u17 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u18 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u19 : p4923 := (Or.elim h73832 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    let u20 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    (Or.elim h70489 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u18))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u15))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u17))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u20))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u16))) (fun r11 => (False.elim (r11 u14)))))))))))))))))))))))))))

theorem step103731 (p2264 p2437 p2630 p2685 p2737 p2743 p2810 p3425 p3553 p3572 p3742 p4777 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73316 : p2810 ∨ p2630)
    (h73410 : p3553 ∨ p2264)
    (h73420 : p3572 ∨ p2685)
    (h73452 : p3742 ∨ p2437)
    (h70272 : (¬ p3553) ∨ (¬ p4777) ∨ (¬ p3572) ∨ (¬ p3742) ∨ (¬ p2810) ∨ (¬ p3425) ∨ (¬ p2743))
    : p2737 ∨ p2630 ∨ p2264 ∨ p2685 ∨ (¬ p3425) ∨ p2437 ∨ (¬ p4777) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70272 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u7)))))))))))))))

theorem step103734 (p2241 p2247 p2264 p2437 p2651 p2657 p2996 p3553 p4649 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73288 : p2657 ∨ p2651)
    (h73688 : p4649 ∨ p2437)
    (h73410 : p3553 ∨ p2264)
    (h71211 : (¬ p3553) ∨ (¬ p4649) ∨ (¬ p2996) ∨ (¬ p2657) ∨ (¬ p2247))
    : p2241 ∨ (¬ p2996) ∨ p2651 ∨ p2437 ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4649 := (Or.elim h73688 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71211 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step103740 (p2177 p2264 p2651 p3166 p3172 p4547 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73630 : p4547 ∨ p2264)
    (h72617 : (¬ p4547) ∨ (¬ p2177) ∨ (¬ p2651) ∨ (¬ p3172))
    : p3166 ∨ (¬ p2177) ∨ (¬ p2651) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4547 := (Or.elim h73630 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72617 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103744 (p2264 p2685 p2911 p3005 p3166 p3172 p3572 p3877 p4236 p4547 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73488 : p3877 ∨ p3005)
    (h73419 : (¬ p2685) ∨ (¬ p3572))
    (h73630 : p4547 ∨ p2264)
    (h70852 : (¬ p2911) ∨ p3572 ∨ (¬ p3172) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4547))
    : (¬ p4236) ∨ p3166 ∨ (¬ p2911) ∨ p3005 ∨ (¬ p2685) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : (¬ p3572) := (Or.elim h73419 (fun q0 => (False.elim (q0 u4))) (fun r0 => r0));
    let u9 : p4547 := (Or.elim h73630 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70852 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u9)))))))))))))

theorem step103747 (p2440 p2630 p2651 p2657 p2839 p4236 p4751 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73742 : p4751 ∨ (¬ p2630))
    (h70855 : (¬ p2657) ∨ (¬ p2839) ∨ (¬ p4751) ∨ (¬ p2440) ∨ (¬ p4236))
    : (¬ p2839) ∨ p2651 ∨ (¬ p2630) ∨ (¬ p2440) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4751 := (Or.elim h73742 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h70855 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103748 (p2132 p2598 p2696 p2751 p2839 p2860 p3016 p3055 p3574 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73350 : p3055 ∨ p2598)
    (h70948 : (¬ p3055) ∨ (¬ p2839) ∨ (¬ p2132) ∨ p2860 ∨ (¬ p2751) ∨ (¬ p3574) ∨ (¬ p2696))
    : (¬ p2839) ∨ p3016 ∨ (¬ p2132) ∨ p2860 ∨ (¬ p2696) ∨ p2598 ∨ (¬ p2751) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70948 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step103751 (p2274 p2331 p2437 p2651 p2963 p3742 p4554 : Prop)
    (h73337 : (¬ p2331) ∨ (¬ p2963))
    (h73452 : p3742 ∨ p2437)
    (h73634 : p4554 ∨ p2274)
    (h70046 : (¬ p4554) ∨ (¬ p3742) ∨ p2651 ∨ p2963)
    : (¬ p2331) ∨ p2437 ∨ p2274 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2963) := (Or.elim h73337 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4554 := (Or.elim h73634 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70046 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u4 r2)))))))))

theorem step103752 (p2331 p2437 p2563 p2651 p3742 p4204 p4714 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73720 : p4714 ∨ p2563)
    (h69982 : (¬ p4714) ∨ (¬ p4204) ∨ (¬ p3742) ∨ p2651 ∨ (¬ p2331))
    : (¬ p2331) ∨ p2437 ∨ p2651 ∨ (¬ p4204) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69982 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step103753 (p2210 p2440 p2493 p3016 p3156 p3379 p3497 p3574 p4699 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73421 : (¬ p3016) ∨ (¬ p3574))
    (h73712 : p4699 ∨ (¬ p2440))
    (h70569 : (¬ p4699) ∨ (¬ p3497) ∨ (¬ p2210) ∨ (¬ p2493) ∨ p3574 ∨ (¬ p3379))
    : p3156 ∨ (¬ p2210) ∨ (¬ p3016) ∨ (¬ p2440) ∨ (¬ p3379) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : (¬ p3574) := (Or.elim h73421 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u8 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h70569 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step103765 (p2241 p2573 p2579 p2750 p3016 p3379 p3541 p5189 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73948 : p5189 ∨ p3379)
    (h70692 : (¬ p5189) ∨ (¬ p2241) ∨ (¬ p3541) ∨ (¬ p3016) ∨ (¬ p2579) ∨ (¬ p2750))
    : (¬ p2241) ∨ (¬ p3541) ∨ (¬ p3016) ∨ (¬ p2750) ∨ p2573 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p5189 := (Or.elim h73948 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70692 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step103775 (p2295 p2553 p2588 p2651 p2657 p2807 p4571 p4976 : Prop)
    (h73644 : p4571 ∨ (¬ p2295))
    (h73282 : p2588 ∨ p2553)
    (h73288 : p2657 ∨ p2651)
    (h69827 : (¬ p4571) ∨ (¬ p2657) ∨ (¬ p2588) ∨ (¬ p4976) ∨ (¬ p2807))
    : (¬ p2295) ∨ p2553 ∨ (¬ p2807) ∨ p2651 ∨ (¬ p4976) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4571 := (Or.elim h73644 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69827 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step103776 (p2331 p2573 p2651 p2661 : Prop)
    (h73292 : p2661 ∨ (¬ p2651))
    (h69778 : p2331 ∨ (¬ p2573) ∨ (¬ p2661))
    : p2331 ∨ (¬ p2573) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2661 := (Or.elim h73292 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h69778 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step103777 (p2493 p2503 p2590 p3016 p3136 p3574 p3879 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73422 : p3574 ∨ p3016)
    (h73264 : p2503 ∨ (¬ p2493))
    (h69852 : (¬ p2503) ∨ p3016 ∨ (¬ p3574) ∨ (¬ p2590) ∨ (¬ p3879) ∨ (¬ p4315))
    : p3136 ∨ p3016 ∨ (¬ p3879) ∨ (¬ p2590) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2503 := (Or.elim h73264 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h69852 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step103778 (p2331 p2563 p2651 p2901 p2946 p2952 p4320 p4555 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73552 : p4320 ∨ p2901)
    (h70087 : (¬ p2952) ∨ (¬ p2331) ∨ (¬ p2563) ∨ (¬ p2651) ∨ (¬ p4555) ∨ (¬ p4320))
    : p2946 ∨ p2901 ∨ (¬ p2563) ∨ (¬ p2651) ∨ (¬ p4555) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70087 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step103779 (p2249 p2891 p2901 p2946 p2952 p3486 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73330 : p2952 ∨ p2946)
    (h73397 : (¬ p2891) ∨ (¬ p3486))
    (h69908 : (¬ p4320) ∨ (¬ p2952) ∨ p3486 ∨ (¬ p2249))
    : p2901 ∨ p2946 ∨ (¬ p2249) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : (¬ p3486) := (Or.elim h73397 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    (Or.elim h69908 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step103781 (p2352 p2383 p2493 p2499 p5194 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h70382 : p2352 ∨ (¬ p2499) ∨ (¬ p5194) ∨ (¬ p2383))
    : p2493 ∨ (¬ p2383) ∨ p2352 ∨ (¬ p5194) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h70382 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step103783 (p2331 p2668 p2807 p3414 p4405 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h70246 : (¬ p2331) ∨ (¬ p4405) ∨ (¬ p3414) ∨ (¬ p2668))
    : (¬ p2331) ∨ (¬ p2668) ∨ (¬ p4405) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70246 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step103785 (p2177 p2299 p2553 p2588 p2608 p3016 p3367 p3574 p3585 p3954 p4753 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73428 : p3585 ∨ p3367)
    (h73282 : p2588 ∨ p2553)
    (h73234 : p2299 ∨ p2177)
    (h73422 : p3574 ∨ p3016)
    (h70566 : (¬ p3574) ∨ (¬ p3954) ∨ (¬ p3585) ∨ (¬ p2588) ∨ (¬ p4753) ∨ (¬ p2299))
    : p2608 ∨ p3367 ∨ p2553 ∨ p2177 ∨ p3016 ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70566 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u9)))))))))))))

theorem step103786 (p2608 p2727 p2737 p2740 p3379 p3954 p4111 : Prop)
    (h73296 : p2740 ∨ p2737)
    (h73498 : p3954 ∨ p2608)
    (h73517 : (¬ p2727) ∨ (¬ p4111))
    (h71178 : (¬ p2740) ∨ (¬ p3954) ∨ (¬ p3379) ∨ p4111)
    : p2737 ∨ p2608 ∨ (¬ p3379) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2740 := (Or.elim h73296 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : (¬ p4111) := (Or.elim h73517 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    (Or.elim h71178 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u6 r2)))))))))

theorem step103787 (p2241 p2608 p2696 p3365 p3873 p3954 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73498 : p3954 ∨ p2608)
    (h70423 : (¬ p2241) ∨ (¬ p3365) ∨ (¬ p3954) ∨ (¬ p3873))
    : (¬ p2241) ∨ p2696 ∨ (¬ p3873) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70423 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step103792 (p2241 p2247 p2696 p2737 p2740 : Prop)
    (h73296 : p2740 ∨ p2737)
    (h73226 : p2247 ∨ p2241)
    (h70311 : (¬ p2696) ∨ (¬ p2740) ∨ (¬ p2247))
    : p2737 ∨ p2241 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2740 := (Or.elim h73296 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70311 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u4)))))))

theorem step103810 (p2459 p2528 p2534 p2922 p2928 p3379 p3452 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73268 : p2534 ∨ p2528)
    (h73394 : p3452 ∨ p3379)
    (h71169 : (¬ p2459) ∨ (¬ p2534) ∨ (¬ p3452) ∨ (¬ p2928))
    : p2922 ∨ p2528 ∨ (¬ p2459) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71169 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103816 (p2230 p2241 p2251 p2363 p2440 p2459 p2532 p2563 p2589 p2651 p2657 p2950 p3063 p3073 p3093 p3319 p3461 p4191 p4198 p4714 p5019 p5046 p5118 p5119 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73288 : p2657 ∨ p2651)
    (h73230 : p2251 ∨ (¬ p2241))
    (h73878 : p5019 ∨ (¬ p3093))
    (h73720 : p4714 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h71007 : (¬ p5019) ∨ (¬ p5119) ∨ (¬ p5118) ∨ (¬ p4191) ∨ (¬ p2459) ∨ (¬ p3319) ∨ (¬ p3073) ∨ (¬ p3063) ∨ (¬ p2532) ∨ (¬ p5046) ∨ (¬ p4198) ∨ (¬ p4714) ∨ (¬ p2363) ∨ (¬ p2950) ∨ (¬ p2589) ∨ (¬ p2440) ∨ (¬ p2251) ∨ (¬ p2657))
    : p3461 ∨ (¬ p5118) ∨ (¬ p2363) ∨ p2651 ∨ (¬ p2950) ∨ (¬ p5119) ∨ (¬ p2459) ∨ (¬ p3063) ∨ (¬ p2241) ∨ (¬ p3093) ∨ (¬ p3319) ∨ p2563 ∨ (¬ p5046) ∨ (¬ p4198) ∨ p2230 ∨ (¬ p2440) ∨ (¬ p2532) ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))));
    let u18 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u19 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u20 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u21 : p5019 := (Or.elim h73878 (fun q0 => q0) (fun r0 => (False.elim (r0 u9))));
    let u22 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u23 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    (Or.elim h71007 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u18))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u17))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u16))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u13))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u22))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u2))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u4))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u23))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u15))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u20))) (fun r16 => (False.elim (r16 u19)))))))))))))))))))))))))))))))))))))

theorem step103819 (p2528 p2534 p2911 p3363 p3367 p3389 p3540 p3585 p4921 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73830 : p4921 ∨ p2911)
    (h73428 : p3585 ∨ p3367)
    (h73402 : p3540 ∨ p3389)
    (h70491 : (¬ p3540) ∨ (¬ p3363) ∨ (¬ p4921) ∨ (¬ p2534) ∨ (¬ p3585))
    : p2528 ∨ p2911 ∨ p3367 ∨ (¬ p3363) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4921 := (Or.elim h73830 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70491 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step103830 (p2241 p2247 p2608 p2662 p2742 p2911 p3136 p3389 p3475 p3487 p3540 p3590 p3644 p4315 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73550 : p4315 ∨ p3136)
    (h73402 : p3540 ∨ p3389)
    (h73434 : p3644 ∨ p2911)
    (h70858 : (¬ p4315) ∨ (¬ p3487) ∨ (¬ p2247) ∨ (¬ p2662) ∨ (¬ p3590) ∨ (¬ p3475) ∨ (¬ p2742) ∨ (¬ p2608) ∨ (¬ p3644) ∨ (¬ p3540))
    : p2241 ∨ p3136 ∨ (¬ p2608) ∨ (¬ p3475) ∨ p3389 ∨ (¬ p3487) ∨ (¬ p3590) ∨ (¬ p2742) ∨ p2911 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3136) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h70858 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (False.elim (r8 u12)))))))))))))))))))))

theorem step103835 (p2255 p2651 p2727 p2922 p2928 p2996 p4809 : Prop)
    (h73770 : p4809 ∨ p2727)
    (h73320 : p2928 ∨ p2922)
    (h70404 : (¬ p4809) ∨ (¬ p2651) ∨ (¬ p2928) ∨ (¬ p2255) ∨ p2996)
    : p2727 ∨ (¬ p2255) ∨ (¬ p2651) ∨ p2922 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70404 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u4 r3)))))))))))

theorem step103838 (p2210 p2241 p2251 p2946 : Prop)
    (h73230 : p2251 ∨ (¬ p2241))
    (h70136 : (¬ p2251) ∨ p2210 ∨ (¬ p2946))
    : p2210 ∨ (¬ p2241) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h70136 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step103839 (p2098 p2104 p2341 p2717 p4589 p4799 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h73654 : p4589 ∨ (¬ p2341))
    (h73766 : p4799 ∨ p2717)
    (h70438 : (¬ p4589) ∨ (¬ p4799) ∨ (¬ p2104))
    : p2098 ∨ (¬ p2341) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4589 := (Or.elim h73654 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u5 : p4799 := (Or.elim h73766 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70438 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (False.elim (r1 u3)))))))

theorem step103843 (p2509 p2655 p2656 p2992 p3083 p3136 p3402 p4343 p4704 : Prop)
    (h73046 : p4704)
    (h72611 : (¬ p3083) ∨ (¬ p2509) ∨ (¬ p2656) ∨ (¬ p4704) ∨ (¬ p2655) ∨ (¬ p3402) ∨ (¬ p2992) ∨ (¬ p4343) ∨ (¬ p3136))
    : (¬ p3402) ∨ (¬ p2992) ∨ (¬ p3136) ∨ (¬ p2509) ∨ (¬ p2655) ∨ (¬ p3083) ∨ (¬ p2656) ∨ (¬ p4343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3402 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4704 := h73046;
    (Or.elim h72611 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step103846 (p2295 p2553 p3093 p3568 p3591 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73416 : p3568 ∨ p2295)
    (h71197 : (¬ p3568) ∨ (¬ p3591) ∨ (¬ p2553))
    : p3093 ∨ p2295 ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71197 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step103849 (p2295 p2427 p2553 p2901 p3568 p4702 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h71166 : p2901 ∨ (¬ p4702) ∨ (¬ p2427) ∨ (¬ p3568) ∨ (¬ p2553))
    : p2295 ∨ p2901 ∨ (¬ p4702) ∨ (¬ p2427) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71166 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103850 (p2264 p2284 p2331 p2427 p2440 p2630 p4140 p4562 p4703 : Prop)
    (h73714 : p4703 ∨ p2440)
    (h73638 : p4562 ∨ p2284)
    (h70475 : (¬ p4703) ∨ (¬ p2331) ∨ (¬ p2630) ∨ (¬ p4562) ∨ (¬ p4140) ∨ (¬ p2264) ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p2264) ∨ p2440 ∨ (¬ p4140) ∨ (¬ p2630) ∨ p2284 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4562 := (Or.elim h73638 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70475 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step103854 (p2528 p2534 p2911 p3363 p3389 p3422 p3540 p3644 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73434 : p3644 ∨ p2911)
    (h73268 : p2534 ∨ p2528)
    (h69893 : (¬ p3540) ∨ (¬ p2534) ∨ (¬ p3422) ∨ (¬ p3363) ∨ (¬ p3644))
    : p3389 ∨ (¬ p3422) ∨ p2911 ∨ (¬ p3363) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69893 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step103858 (p2230 p2406 p2589 p2598 p3425 p4726 p5259 : Prop)
    (h73728 : p4726 ∨ p2598)
    (h73284 : p2589 ∨ p2230)
    (h73982 : p5259 ∨ p3425)
    (h69886 : (¬ p4726) ∨ (¬ p5259) ∨ (¬ p2589) ∨ (¬ p2406))
    : p2598 ∨ (¬ p2406) ∨ p2230 ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2598) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4726 := (Or.elim h73728 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p5259 := (Or.elim h73982 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69886 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step103864 (p2341 p2363 p2383 p2459 p4347 p4348 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73561 : (¬ p2459) ∨ (¬ p4348))
    (h69781 : p4348 ∨ (¬ p2341) ∨ (¬ p2383) ∨ (¬ p4347))
    : p2363 ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : (¬ p4348) := (Or.elim h73561 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h69781 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103869 (p2156 p2307 p2313 p2553 p2563 p3660 p4484 p4533 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73594 : p4484 ∨ p2156)
    (h71119 : (¬ p4484) ∨ (¬ p2563) ∨ (¬ p3660) ∨ (¬ p4533) ∨ (¬ p2313) ∨ (¬ p2553))
    : p2307 ∨ p2156 ∨ (¬ p2553) ∨ (¬ p4533) ∨ (¬ p3660) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4484 := (Or.elim h73594 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71119 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step103870 (p2363 p2373 p2563 p3146 p3696 p3697 p4110 p4347 p4533 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73516 : p4110 ∨ p2563)
    (h70994 : (¬ p2373) ∨ (¬ p4533) ∨ (¬ p3696) ∨ (¬ p3697) ∨ (¬ p4110) ∨ (¬ p3146) ∨ (¬ p4347))
    : p2363 ∨ (¬ p3696) ∨ p2563 ∨ (¬ p4533) ∨ (¬ p2373) ∨ (¬ p3697) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70994 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u7)))))))))))))))

theorem step103874 (p2210 p2241 p2253 p2651 p2741 p3412 p3555 p4377 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h70865 : (¬ p3555) ∨ (¬ p3412) ∨ (¬ p2241) ∨ (¬ p2253) ∨ (¬ p4377) ∨ (¬ p2651) ∨ (¬ p2741))
    : p2210 ∨ (¬ p3412) ∨ (¬ p4377) ∨ (¬ p2741) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h70865 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step103876 (p2210 p2696 p2737 p2743 p3555 p4377 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73412 : p3555 ∨ p2210)
    (h70722 : (¬ p2743) ∨ (¬ p4377) ∨ (¬ p3555) ∨ (¬ p2696))
    : p2737 ∨ p2210 ∨ (¬ p2696) ∨ (¬ p4377) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70722 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step103883 (p2192 p2745 p2860 p2992 p3136 p4173 p4956 p5050 : Prop)
    (h73850 : p4956 ∨ p2992)
    (h73528 : p4173 ∨ p2192)
    (h73894 : p5050 ∨ (¬ p3136))
    (h70262 : (¬ p4956) ∨ (¬ p5050) ∨ (¬ p2745) ∨ (¬ p2860) ∨ (¬ p4173))
    : p2992 ∨ (¬ p2860) ∨ p2192 ∨ (¬ p3136) ∨ (¬ p2745) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4956 := (Or.elim h73850 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p5050 := (Or.elim h73894 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h70262 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step103889 (p2230 p2274 p2437 p2440 p2553 p2589 p3097 p4718 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73284 : p2589 ∨ p2230)
    (h70358 : (¬ p2553) ∨ (¬ p3097) ∨ (¬ p4718) ∨ (¬ p2589) ∨ (¬ p2440) ∨ (¬ p2437))
    : (¬ p2553) ∨ p2274 ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p4718) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70358 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step103891 (p2437 p2440 p2553 p2563 p4714 : Prop)
    (h73720 : p4714 ∨ p2563)
    (h70356 : (¬ p4714) ∨ (¬ p2553) ∨ (¬ p2440) ∨ (¬ p2437))
    : (¬ p2440) ∨ (¬ p2553) ∨ (¬ p2437) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70356 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step103895 (p2241 p2437 p2440 p2553 p2641 p2727 p4699 p4709 : Prop)
    (h73718 : p4709 ∨ (¬ p2553))
    (h73712 : p4699 ∨ (¬ p2440))
    (h70574 : (¬ p4709) ∨ (¬ p2641) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p2437) ∨ (¬ p4699))
    : (¬ p2241) ∨ (¬ p2553) ∨ (¬ p2440) ∨ (¬ p2727) ∨ (¬ p2641) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4709 := (Or.elim h73718 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h70574 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step103898 (p2307 p2313 p2363 p2437 p2630 p2696 p2881 p3016 p3093 p3136 p3146 p3156 p3256 p3570 p3591 p3692 p3919 p3988 p4118 p4347 p4518 p4556 p4595 p4596 p4733 p4902 p5015 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73559 : (¬ p2363) ∨ (¬ p4347))
    (h73448 : p3692 ∨ p3146)
    (h73418 : p3570 ∨ p2881)
    (h73238 : p2313 ∨ p2307)
    (h73520 : p4118 ∨ p3256)
    (h72613 : (¬ p4118) ∨ (¬ p2437) ∨ p4347 ∨ (¬ p4596) ∨ (¬ p4595) ∨ (¬ p3692) ∨ (¬ p4733) ∨ (¬ p3016) ∨ (¬ p5015) ∨ (¬ p4902) ∨ (¬ p3156) ∨ (¬ p3919) ∨ (¬ p3570) ∨ (¬ p4556) ∨ (¬ p3988) ∨ (¬ p2696) ∨ (¬ p3591) ∨ (¬ p2313) ∨ (¬ p2630) ∨ (¬ p3136) ∨ (¬ p4518))
    : (¬ p5015) ∨ p3093 ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2363) ∨ (¬ p4518) ∨ (¬ p4596) ∨ (¬ p3016) ∨ (¬ p4595) ∨ (¬ p2696) ∨ (¬ p4902) ∨ (¬ p3156) ∨ p3146 ∨ (¬ p4556) ∨ p2881 ∨ (¬ p3136) ∨ (¬ p4733) ∨ (¬ p3919) ∨ p2307 ∨ (¬ p3988) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5015 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4595 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))));
    let u21 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u22 : (¬ p4347) := (Or.elim h73559 (fun q0 => (False.elim (q0 u4))) (fun r0 => r0));
    let u23 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    let u24 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    let u25 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u18 r0))));
    let u26 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u20 r0))));
    (Or.elim h72613 (fun q0 => (False.elim (q0 u26))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u22 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u23))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u16))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u17))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u24))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u13))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u19))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u9))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u21))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u25))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u3))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u15))) (fun r19 => (False.elim (r19 u5)))))))))))))))))))))))))))))))))))))))))))

theorem step103899 (p2177 p2249 p2437 p2470 p2476 p2727 p3083 p4276 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h69977 : (¬ p2437) ∨ (¬ p2727) ∨ (¬ p2249) ∨ (¬ p2476) ∨ p3083 ∨ (¬ p4276) ∨ (¬ p2177))
    : (¬ p2437) ∨ (¬ p2177) ∨ (¬ p2249) ∨ (¬ p2727) ∨ p3083 ∨ (¬ p4276) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h69977 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step103903 (p2437 p2608 p2630 p2745 p3389 p3540 p4651 : Prop)
    (h73690 : p4651 ∨ (¬ p2437))
    (h73402 : p3540 ∨ p3389)
    (h70875 : (¬ p4651) ∨ (¬ p2745) ∨ (¬ p2608) ∨ (¬ p2630) ∨ (¬ p3540))
    : (¬ p2437) ∨ (¬ p2608) ∨ p3389 ∨ (¬ p2745) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4651 := (Or.elim h73690 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70875 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step103905 (p2241 p2251 p2437 p2440 p2630 p2727 p2829 p3475 p4651 p4699 p4751 p4812 : Prop)
    (h73690 : p4651 ∨ (¬ p2437))
    (h73772 : p4812 ∨ (¬ p2727))
    (h73712 : p4699 ∨ (¬ p2440))
    (h73230 : p2251 ∨ (¬ p2241))
    (h73742 : p4751 ∨ (¬ p2630))
    (h70578 : (¬ p2251) ∨ (¬ p4751) ∨ (¬ p4812) ∨ (¬ p3475) ∨ (¬ p4651) ∨ (¬ p4699) ∨ (¬ p2829))
    : (¬ p2829) ∨ (¬ p2437) ∨ (¬ p2727) ∨ (¬ p2440) ∨ (¬ p2241) ∨ (¬ p2630) ∨ (¬ p3475) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4651 := (Or.elim h73690 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u8 : p4812 := (Or.elim h73772 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u9 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u10 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u11 : p4751 := (Or.elim h73742 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h70578 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step103906 (p2132 p2274 p2437 p2440 p2528 p2598 p2727 p3367 p3389 p4554 p4646 p4651 p4692 p4699 p4728 p4812 p5213 : Prop)
    (h73634 : p4554 ∨ p2274)
    (h73960 : p5213 ∨ p3367)
    (h73708 : p4692 ∨ p2528)
    (h73690 : p4651 ∨ (¬ p2437))
    (h73712 : p4699 ∨ (¬ p2440))
    (h73772 : p4812 ∨ (¬ p2727))
    (h73730 : p4728 ∨ (¬ p2598))
    (h70503 : (¬ p4692) ∨ (¬ p4699) ∨ (¬ p4812) ∨ (¬ p2132) ∨ (¬ p4651) ∨ (¬ p4646) ∨ (¬ p3389) ∨ (¬ p5213) ∨ (¬ p4554) ∨ (¬ p4728))
    : p2274 ∨ p3367 ∨ p2528 ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p4646) ∨ (¬ p2727) ∨ (¬ p3389) ∨ (¬ p2132) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4554 := (Or.elim h73634 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p5213 := (Or.elim h73960 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p4692 := (Or.elim h73708 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u13 : p4651 := (Or.elim h73690 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u14 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u15 : p4812 := (Or.elim h73772 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u16 : p4728 := (Or.elim h73730 (fun q0 => q0) (fun r0 => (False.elim (r0 u9))));
    (Or.elim h70503 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u16)))))))))))))))))))))

theorem step103914 (p2396 p2417 p3063 p3093 p3631 p3817 p4278 p4405 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h73546 : p4278 ∨ p2417)
    (h70355 : (¬ p2396) ∨ (¬ p3063) ∨ (¬ p3817) ∨ (¬ p4278) ∨ (¬ p3093) ∨ (¬ p4405))
    : (¬ p3063) ∨ p3631 ∨ (¬ p3093) ∨ p2417 ∨ (¬ p2396) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70355 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step103927 (p2241 p2251 p2449 p2608 p2727 p2761 p2992 p2996 p3030 p3954 : Prop)
    (h73342 : p3030 ∨ (¬ p2996))
    (h73498 : p3954 ∨ p2608)
    (h73230 : p2251 ∨ (¬ p2241))
    (h70089 : (¬ p3954) ∨ (¬ p2449) ∨ (¬ p2992) ∨ (¬ p2251) ∨ (¬ p3030) ∨ (¬ p2727) ∨ (¬ p2761))
    : (¬ p2996) ∨ p2608 ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p2992) ∨ (¬ p2761) ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3030 := (Or.elim h73342 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h70089 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step103933 (p2449 p2608 p2630 p2696 p2761 p2807 p3136 p3589 p4788 p4917 : Prop)
    (h73760 : p4788 ∨ (¬ p2696))
    (h70095 : (¬ p4788) ∨ (¬ p2807) ∨ (¬ p2608) ∨ (¬ p3589) ∨ (¬ p2449) ∨ (¬ p3136) ∨ (¬ p2630) ∨ (¬ p2761) ∨ (¬ p4917))
    : (¬ p2761) ∨ (¬ p2449) ∨ (¬ p3589) ∨ (¬ p2608) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p4917) ∨ (¬ p2630) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h70095 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step103938 (p2088 p2177 p2230 p2264 p2274 p2284 p2363 p2427 p2440 p2563 p2589 p2651 p2657 p2737 p2819 p2881 p2946 p2952 p3156 p3497 p3952 p4032 p4235 p4500 p4533 p4557 p4602 p4714 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73288 : p2657 ∨ p2651)
    (h73330 : p2952 ∨ p2946)
    (h73536 : p4235 ∨ p2427)
    (h73602 : p4500 ∨ p2177)
    (h73720 : p4714 ∨ p2563)
    (h73496 : p3952 ∨ p2284)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73636 : p4557 ∨ (¬ p2274))
    (h73400 : p3497 ∨ p3156)
    (h70701 : (¬ p2737) ∨ (¬ p2440) ∨ (¬ p2819) ∨ (¬ p4032) ∨ (¬ p2088) ∨ (¬ p3497) ∨ (¬ p4500) ∨ (¬ p4235) ∨ (¬ p4533) ∨ (¬ p2589) ∨ (¬ p4602) ∨ (¬ p4714) ∨ (¬ p3952) ∨ (¬ p2881) ∨ (¬ p4557) ∨ (¬ p2657) ∨ (¬ p2952) ∨ (¬ p2264))
    : (¬ p2737) ∨ (¬ p2819) ∨ (¬ p4032) ∨ p2230 ∨ p2651 ∨ p2946 ∨ (¬ p2440) ∨ (¬ p2264) ∨ (¬ p2881) ∨ p2427 ∨ p2177 ∨ p2563 ∨ p2284 ∨ (¬ p2363) ∨ (¬ p2088) ∨ (¬ p4533) ∨ (¬ p2274) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))));
    let u18 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u19 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u20 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u21 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u22 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u23 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u24 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    let u25 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u26 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    let u27 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u17 r0))));
    (Or.elim h70701 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u27))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u22))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u21))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u15))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u18))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u25))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u23))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u24))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u8))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u26))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u19))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u20))) (fun r16 => (False.elim (r16 u7)))))))))))))))))))))))))))))))))))))

theorem step103948 (p2156 p2192 p2255 p2264 p2274 p2284 p2312 p2440 p2449 p2553 p2573 p2588 p2630 p2881 p2891 p3246 p3486 p3690 p3921 p3986 p4402 p4554 p4655 p4699 p4751 p4903 p5043 : Prop)
    (h73692 : p4655 ∨ p2449)
    (h73742 : p4751 ∨ (¬ p2630))
    (h73282 : p2588 ∨ p2553)
    (h73712 : p4699 ∨ (¬ p2440))
    (h73820 : p4903 ∨ (¬ p2881))
    (h73398 : p3486 ∨ p2891)
    (h73634 : p4554 ∨ p2274)
    (h73446 : p3690 ∨ p3246)
    (h70333 : (¬ p4655) ∨ (¬ p2255) ∨ (¬ p2588) ∨ (¬ p3921) ∨ (¬ p2573) ∨ (¬ p4699) ∨ (¬ p2264) ∨ (¬ p2284) ∨ (¬ p3986) ∨ (¬ p2312) ∨ (¬ p5043) ∨ (¬ p2192) ∨ (¬ p4554) ∨ (¬ p3690) ∨ (¬ p4402) ∨ (¬ p4903) ∨ (¬ p2156) ∨ (¬ p4751) ∨ (¬ p3486))
    : p2449 ∨ (¬ p2264) ∨ (¬ p2630) ∨ p2553 ∨ (¬ p3921) ∨ (¬ p2255) ∨ (¬ p2440) ∨ (¬ p2881) ∨ (¬ p3986) ∨ (¬ p2284) ∨ (¬ p4402) ∨ (¬ p5043) ∨ (¬ p2312) ∨ (¬ p2192) ∨ (¬ p2573) ∨ p2891 ∨ (¬ p2156) ∨ p2274 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))));
    let u19 : p4655 := (Or.elim h73692 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u20 : p4751 := (Or.elim h73742 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u21 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u22 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u23 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u24 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u15 r0))));
    let u25 : p4554 := (Or.elim h73634 (fun q0 => q0) (fun r0 => (False.elim (u17 r0))));
    let u26 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u18 r0))));
    (Or.elim h70333 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u21))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u22))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u13))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u25))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u26))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u10))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u23))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u16))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u20))) (fun r17 => (False.elim (r17 u24)))))))))))))))))))))))))))))))))))))))

theorem step103953 (p2449 p2727 p3631 p3947 p4111 p4652 p5361 : Prop)
    (h74014 : p5361 ∨ (¬ p3631))
    (h73494 : p3947 ∨ p2449)
    (h73518 : p4111 ∨ p2727)
    (h69769 : (¬ p5361) ∨ (¬ p4652) ∨ (¬ p4111) ∨ (¬ p3947))
    : (¬ p3631) ∨ p2449 ∨ p2727 ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5361 := (Or.elim h74014 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69769 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103955 (p2437 p2440 p2449 p2542 p3246 p3947 p4644 p4649 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73688 : p4649 ∨ p2437)
    (h73270 : p2542 ∨ p2440)
    (h70108 : (¬ p4649) ∨ (¬ p4644) ∨ (¬ p2542) ∨ (¬ p3246) ∨ (¬ p3947))
    : p2449 ∨ (¬ p3246) ∨ p2437 ∨ p2440 ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4649 := (Or.elim h73688 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70108 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step103978 (p2156 p2264 p2440 p2630 p2881 p2891 p3246 p3486 p4487 p4551 p4699 p4751 p4903 p5101 : Prop)
    (h73596 : p4487 ∨ (¬ p2156))
    (h73712 : p4699 ∨ (¬ p2440))
    (h73398 : p3486 ∨ p2891)
    (h73632 : p4551 ∨ (¬ p2264))
    (h73820 : p4903 ∨ (¬ p2881))
    (h73918 : p5101 ∨ p3246)
    (h73742 : p4751 ∨ (¬ p2630))
    (h70335 : (¬ p4699) ∨ (¬ p4551) ∨ (¬ p5101) ∨ (¬ p4903) ∨ (¬ p4487) ∨ (¬ p4751) ∨ (¬ p3486))
    : (¬ p2156) ∨ (¬ p2440) ∨ p2891 ∨ (¬ p2264) ∨ (¬ p2881) ∨ p3246 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4487 := (Or.elim h73596 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u9 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4551 := (Or.elim h73632 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u11 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u12 : p5101 := (Or.elim h73918 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p4751 := (Or.elim h73742 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    (Or.elim h70335 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (False.elim (r5 u9)))))))))))))))

theorem step103983 (p2156 p2274 p2630 p2881 p2891 p3246 p3486 p3690 p4487 p4557 p4751 p4903 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73820 : p4903 ∨ (¬ p2881))
    (h73398 : p3486 ∨ p2891)
    (h73596 : p4487 ∨ (¬ p2156))
    (h73742 : p4751 ∨ (¬ p2630))
    (h73636 : p4557 ∨ (¬ p2274))
    (h70295 : (¬ p4557) ∨ (¬ p3690) ∨ (¬ p4903) ∨ (¬ p4487) ∨ (¬ p4751) ∨ (¬ p3486))
    : p3246 ∨ (¬ p2881) ∨ p2891 ∨ (¬ p2156) ∨ (¬ p2630) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u8 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4487 := (Or.elim h73596 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u10 : p4751 := (Or.elim h73742 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u11 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h70295 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (False.elim (r4 u8)))))))))))))

theorem step103988 (p2264 p2284 p2396 p2685 p2696 p2881 p2946 p2956 p3246 p3690 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73334 : p2956 ∨ (¬ p2946))
    (h69922 : (¬ p2956) ∨ (¬ p2685) ∨ (¬ p2264) ∨ (¬ p2696) ∨ (¬ p3690) ∨ (¬ p2396) ∨ (¬ p2284) ∨ (¬ p2881))
    : p3246 ∨ (¬ p2264) ∨ (¬ p2881) ∨ (¬ p2685) ∨ (¬ p2284) ∨ (¬ p2396) ∨ (¬ p2696) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2956 := (Or.elim h73334 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    (Or.elim h69922 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step103995 (p2230 p2264 p2440 p2630 p2685 p2696 p2860 p2891 p2996 p3027 p3051 p3246 p3486 p3556 p3690 p4666 p4751 p4814 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73340 : p3027 ∨ p2996)
    (h73414 : p3556 ∨ p3051)
    (h73398 : p3486 ∨ p2891)
    (h73742 : p4751 ∨ (¬ p2630))
    (h70316 : (¬ p2696) ∨ (¬ p3027) ∨ (¬ p4814) ∨ (¬ p2685) ∨ (¬ p2230) ∨ (¬ p2860) ∨ (¬ p3556) ∨ (¬ p2440) ∨ (¬ p2264) ∨ (¬ p4666) ∨ (¬ p3690) ∨ (¬ p4751) ∨ (¬ p3486))
    : p3246 ∨ (¬ p2264) ∨ (¬ p4666) ∨ (¬ p2440) ∨ (¬ p4814) ∨ (¬ p2860) ∨ (¬ p2685) ∨ p2996 ∨ p3051 ∨ (¬ p2230) ∨ p2891 ∨ (¬ p2696) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u14 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u15 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u16 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u17 : p4751 := (Or.elim h73742 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    (Or.elim h70316 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u15))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u13))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u17))) (fun r11 => (False.elim (r11 u16)))))))))))))))))))))))))))

theorem step104004 (p2331 p2901 p2946 p4320 p4555 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h70593 : (¬ p2331) ∨ (¬ p4320) ∨ (¬ p4555) ∨ p2946)
    : (¬ p2331) ∨ p2901 ∨ (¬ p4555) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70593 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step104005 (p2295 p2331 p2963 p3166 p3172 p3568 p4405 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73355 : (¬ p3166) ∨ (¬ p3172))
    (h73416 : p3568 ∨ p2295)
    (h69971 : p3172 ∨ (¬ p2963) ∨ (¬ p4405) ∨ (¬ p3568))
    : p2331 ∨ (¬ p3166) ∨ (¬ p4405) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : (¬ p3172) := (Or.elim h73355 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69971 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step104007 (p2166 p2246 p2946 p3136 p3156 p3497 p4315 p4365 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73550 : p4315 ∨ p3136)
    (h71126 : (¬ p4315) ∨ (¬ p2946) ∨ (¬ p3497) ∨ (¬ p4365) ∨ (¬ p2166) ∨ (¬ p2246))
    : (¬ p4365) ∨ (¬ p2246) ∨ (¬ p2946) ∨ p3156 ∨ (¬ p2166) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71126 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step104020 (p2797 p2946 p3105 p3136 p3986 p4385 p4790 p5043 p5048 : Prop)
    (h73576 : p4385 ∨ p3105)
    (h73892 : p5048 ∨ p3136)
    (h70393 : (¬ p5048) ∨ (¬ p4385) ∨ (¬ p2946) ∨ (¬ p4790) ∨ (¬ p2797) ∨ (¬ p3986) ∨ (¬ p5043))
    : p3105 ∨ (¬ p5043) ∨ (¬ p3986) ∨ (¬ p4790) ∨ p3136 ∨ (¬ p2797) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3105) := (fun h => hn (Or.inl h));
    let u1 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4385 := (Or.elim h73576 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p5048 := (Or.elim h73892 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70393 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step104021 (p2860 p3105 p3323 p3758 p4385 p4560 : Prop)
    (h73576 : p4385 ∨ p3105)
    (h73455 : (¬ p2860) ∨ (¬ p3758))
    (h72955 : p4560)
    (h70727 : (¬ p4385) ∨ p3758 ∨ (¬ p3323) ∨ (¬ p4560))
    : (¬ p3323) ∨ p3105 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4385 := (Or.elim h73576 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p3758) := (Or.elim h73455 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u5 : p4560 := h72955;
    (Or.elim h70727 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step104025 (p2274 p3125 p3266 p4322 p4620 p5042 : Prop)
    (h73888 : p5042 ∨ p3125)
    (h70796 : (¬ p5042) ∨ (¬ p4322) ∨ (¬ p3266) ∨ (¬ p4620) ∨ (¬ p2274))
    : (¬ p4322) ∨ (¬ p3266) ∨ (¬ p2274) ∨ (¬ p4620) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5042 := (Or.elim h73888 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70796 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step104029 (p2177 p2331 p2528 p2651 p2963 p3166 p3172 p4502 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73337 : (¬ p2331) ∨ (¬ p2963))
    (h73604 : p4502 ∨ (¬ p2177))
    (h70047 : p2651 ∨ (¬ p3172) ∨ p2963 ∨ (¬ p2528) ∨ (¬ p4502))
    : p3166 ∨ (¬ p2331) ∨ p2651 ∨ (¬ p2177) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : (¬ p2963) := (Or.elim h73337 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u7 : p4502 := (Or.elim h73604 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h70047 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step104032 (p2295 p2307 p2313 p3166 p3172 p3568 p4194 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73416 : p3568 ∨ p2295)
    (h73237 : (¬ p2307) ∨ (¬ p2313))
    (h71167 : (¬ p3172) ∨ p2313 ∨ (¬ p4194) ∨ (¬ p3568))
    : p3166 ∨ p2295 ∨ (¬ p2307) ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : (¬ p2313) := (Or.elim h73237 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h71167 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step104042 (p2696 p2737 p2740 p3166 p3189 p4360 p4788 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73296 : p2740 ∨ p2737)
    (h73760 : p4788 ∨ (¬ p2696))
    (h70484 : (¬ p4788) ∨ (¬ p2740) ∨ (¬ p4360) ∨ (¬ p3166))
    : p3189 ∨ (¬ p3166) ∨ p2737 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2740 := (Or.elim h73296 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h70484 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step104050 (p2363 p2396 p2881 p3146 p4107 p4347 p4559 p4903 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73820 : p4903 ∨ (¬ p2881))
    (h73514 : p4107 ∨ p2396)
    (h69776 : (¬ p4903) ∨ (¬ p4107) ∨ (¬ p4559) ∨ (¬ p3146) ∨ (¬ p4347))
    : p2363 ∨ (¬ p2881) ∨ (¬ p3146) ∨ p2396 ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69776 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step104053 (p2122 p2166 p2210 p2363 p2396 p2774 p2780 p2972 p3822 p4107 p4363 p4433 p4669 p4736 : Prop)
    (h73568 : p4363 ∨ p2972)
    (h73514 : p4107 ∨ p2396)
    (h73472 : p3822 ∨ p2122)
    (h73308 : p2780 ∨ p2774)
    (h70971 : (¬ p2166) ∨ (¬ p4363) ∨ (¬ p4107) ∨ (¬ p2780) ∨ (¬ p2210) ∨ (¬ p2363) ∨ (¬ p3822) ∨ (¬ p4669) ∨ (¬ p4736) ∨ (¬ p4433))
    : p2972 ∨ p2396 ∨ (¬ p2166) ∨ (¬ p4433) ∨ p2122 ∨ (¬ p2363) ∨ (¬ p2210) ∨ p2774 ∨ (¬ p4736) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4363 := (Or.elim h73568 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h70971 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step104055 (p2274 p2295 p2383 p2396 p2668 p3097 p3568 p4107 p4666 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73514 : p4107 ∨ p2396)
    (h73352 : p3097 ∨ p2274)
    (h71187 : (¬ p4107) ∨ (¬ p4666) ∨ (¬ p3097) ∨ (¬ p2383) ∨ (¬ p2668) ∨ (¬ p3568))
    : p2295 ∨ (¬ p2668) ∨ p2396 ∨ p2274 ∨ (¬ p2383) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71187 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step104056 (p2241 p2251 p2396 p2440 p2563 p2651 p2661 p2881 p4107 p4555 p4666 p4703 : Prop)
    (h73714 : p4703 ∨ p2440)
    (h73292 : p2661 ∨ (¬ p2651))
    (h73514 : p4107 ∨ p2396)
    (h73230 : p2251 ∨ (¬ p2241))
    (h70341 : (¬ p4703) ∨ (¬ p2251) ∨ (¬ p2661) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p4555) ∨ (¬ p2881) ∨ (¬ p2563))
    : p2440 ∨ (¬ p2651) ∨ p2396 ∨ (¬ p4555) ∨ (¬ p4666) ∨ (¬ p2563) ∨ (¬ p2881) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2661 := (Or.elim h73292 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u10 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    (Or.elim h70341 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step104060 (p2651 p2654 p2807 p3389 p3540 : Prop)
    (h73286 : p2654 ∨ p2651)
    (h73402 : p3540 ∨ p3389)
    (h70218 : (¬ p2654) ∨ (¬ p3540) ∨ (¬ p2807))
    : p2651 ∨ p3389 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2654 := (Or.elim h73286 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70218 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u2)))))))

theorem step104063 (p2264 p2659 p2911 p3389 p3540 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h70603 : p2911 ∨ (¬ p3540) ∨ (¬ p2659) ∨ (¬ p2264))
    : p2911 ∨ (¬ p2264) ∨ (¬ p2659) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70603 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step104065 (p2230 p2363 p2440 p2608 p2696 p2737 p2740 p3016 p3201 p3422 p3574 p3876 p4537 p4602 p4735 p4785 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73624 : p4537 ∨ (¬ p2230))
    (h73296 : p2740 ∨ p2737)
    (h73758 : p4785 ∨ p2696)
    (h73422 : p3574 ∨ p3016)
    (h73734 : p4735 ∨ (¬ p2608))
    (h73662 : p4602 ∨ (¬ p2363))
    (h70208 : (¬ p2440) ∨ (¬ p4735) ∨ (¬ p2740) ∨ (¬ p4602) ∨ (¬ p3876) ∨ (¬ p4537) ∨ (¬ p4785) ∨ (¬ p3422) ∨ (¬ p3574))
    : p3201 ∨ (¬ p2230) ∨ (¬ p2440) ∨ p2737 ∨ p2696 ∨ p3016 ∨ (¬ p2608) ∨ (¬ p2363) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4537 := (Or.elim h73624 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u11 : p2740 := (Or.elim h73296 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p4785 := (Or.elim h73758 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u14 : p4735 := (Or.elim h73734 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u15 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    (Or.elim h70208 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u15))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u13)))))))))))))))))))

theorem step104070 (p2264 p2341 p4551 p4586 : Prop)
    (h73632 : p4551 ∨ (¬ p2264))
    (h73652 : p4586 ∨ p2341)
    (h70809 : (¬ p4551) ∨ (¬ p4586))
    : (¬ p2264) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr h));
    let u2 : p4551 := (Or.elim h73632 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u3 : p4586 := (Or.elim h73652 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70809 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (r0 u3)))))

theorem step104076 (p2264 p2341 p2881 p4551 p4586 : Prop)
    (h73652 : p4586 ∨ p2341)
    (h73632 : p4551 ∨ (¬ p2264))
    (h70719 : (¬ p2881) ∨ (¬ p4551) ∨ (¬ p4586))
    : p2341 ∨ (¬ p2264) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4586 := (Or.elim h73652 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4551 := (Or.elim h73632 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h70719 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u3)))))))

theorem step104082 (p2177 p2341 p2553 p2581 p4586 : Prop)
    (h73652 : p4586 ∨ p2341)
    (h70700 : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2581) ∨ (¬ p4586))
    : p2341 ∨ (¬ p2553) ∨ (¬ p2581) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4586 := (Or.elim h73652 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h70700 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step104091 (p2274 p2553 p2881 p2911 p3570 p4554 p4560 p4718 p4973 : Prop)
    (h72955 : p4560)
    (h73418 : p3570 ∨ p2881)
    (h73634 : p4554 ∨ p2274)
    (h70425 : (¬ p4554) ∨ (¬ p3570) ∨ (¬ p2911) ∨ (¬ p2553) ∨ (¬ p4973) ∨ (¬ p4718) ∨ (¬ p4560))
    : (¬ p2553) ∨ (¬ p2911) ∨ (¬ p4973) ∨ (¬ p4718) ∨ p2881 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4560 := h72955;
    let u7 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p4554 := (Or.elim h73634 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70425 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step104092 (p2177 p2553 p2881 p3570 p4204 p4560 p4718 p4973 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h72955 : p4560)
    (h70391 : (¬ p2177) ∨ (¬ p4560) ∨ (¬ p4973) ∨ (¬ p4204) ∨ (¬ p3570) ∨ (¬ p4718) ∨ (¬ p2553))
    : (¬ p2553) ∨ (¬ p4204) ∨ (¬ p2177) ∨ p2881 ∨ (¬ p4973) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4560 := h72955;
    (Or.elim h70391 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step104093 (p2363 p2459 p2881 p3570 p4347 p4348 p4556 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73562 : p4348 ∨ p2459)
    (h73559 : (¬ p2363) ∨ (¬ p4347))
    (h69888 : (¬ p4348) ∨ p4347 ∨ (¬ p3570) ∨ (¬ p4556))
    : p2881 ∨ (¬ p4556) ∨ p2459 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : (¬ p4347) := (Or.elim h73559 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    (Or.elim h69888 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step104094 (p2177 p2241 p2244 p2284 p2299 p2608 p2744 p2881 p2946 p3073 p3125 p3527 p3570 p4261 p4330 p4914 p5307 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73544 : p4261 ∨ p3073)
    (h73418 : p3570 ∨ p2881)
    (h73224 : p2244 ∨ p2241)
    (h70480 : (¬ p2244) ∨ (¬ p4261) ∨ (¬ p3527) ∨ (¬ p5307) ∨ (¬ p2608) ∨ (¬ p3125) ∨ (¬ p4914) ∨ (¬ p4330) ∨ (¬ p3570) ∨ (¬ p2299) ∨ (¬ p2946) ∨ (¬ p2744) ∨ (¬ p2284))
    : (¬ p5307) ∨ (¬ p3527) ∨ (¬ p2946) ∨ p2177 ∨ (¬ p2744) ∨ p3073 ∨ p2881 ∨ (¬ p2608) ∨ p2241 ∨ (¬ p3125) ∨ (¬ p4914) ∨ (¬ p4330) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u14 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u15 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u16 : p2244 := (Or.elim h73224 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h70480 (fun q0 => (False.elim (q0 u16))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u15))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u13))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u2))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u4))) (fun r11 => (False.elim (r11 u12)))))))))))))))))))))))))))

theorem step104095 (p2177 p2427 p2563 p2881 p3570 p4235 p4283 p4539 p4988 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73418 : p3570 ∨ p2881)
    (h69985 : (¬ p4235) ∨ (¬ p4988) ∨ (¬ p4283) ∨ (¬ p4539) ∨ (¬ p3570) ∨ (¬ p2563) ∨ (¬ p2177))
    : (¬ p4988) ∨ (¬ p4283) ∨ (¬ p2177) ∨ p2427 ∨ (¬ p4539) ∨ p2881 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4988 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h69985 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step104100 (p2563 p2881 p2911 p3570 p4110 p4558 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73516 : p4110 ∨ p2563)
    (h71006 : (¬ p3570) ∨ (¬ p2911) ∨ (¬ p4558) ∨ (¬ p4110))
    : (¬ p2911) ∨ (¬ p4558) ∨ p2881 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71006 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step104101 (p2437 p2881 p2911 p3246 p3389 p3570 p4750 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h70026 : (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4750) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p2437))
    : (¬ p3246) ∨ (¬ p2911) ∨ (¬ p2437) ∨ p2881 ∨ (¬ p3389) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70026 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step104103 (p2427 p2717 p2881 p3659 p4533 p4882 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h69955 : (¬ p3659) ∨ (¬ p4533) ∨ (¬ p2881) ∨ (¬ p4882) ∨ (¬ p2427))
    : (¬ p2427) ∨ (¬ p2881) ∨ p2717 ∨ (¬ p4882) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69955 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step104113 (p2177 p2299 p2807 p3166 p3414 p4361 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73392 : p3414 ∨ p2807)
    (h69807 : (¬ p3414) ∨ (¬ p3166) ∨ (¬ p4361) ∨ (¬ p2299))
    : (¬ p3166) ∨ (¬ p4361) ∨ p2177 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69807 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step104124 (p2230 p2589 p2850 p3367 p3684 p4734 : Prop)
    (h73441 : (¬ p2850) ∨ (¬ p3684))
    (h73284 : p2589 ∨ p2230)
    (h72735 : p4734)
    (h71099 : p3684 ∨ (¬ p3367) ∨ (¬ p2589) ∨ (¬ p4734))
    : (¬ p2850) ∨ (¬ p3367) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3684) := (Or.elim h73441 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4734 := h72735;
    (Or.elim h71099 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step104127 (p2137 p2220 p2241 p2246 p2247 p2274 p2440 p2563 p2696 p2737 p2748 p2749 p2839 p2881 p2911 p2946 p2952 p3051 p3097 p3136 p3146 p3365 p3570 p3644 p3873 p3985 p4204 p4236 p4315 p4560 p4646 p4668 p4669 p4699 p4716 p4734 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73434 : p3644 ∨ p2911)
    (h72735 : p4734)
    (h73550 : p4315 ∨ p3136)
    (h73352 : p3097 ∨ p2274)
    (h73712 : p4699 ∨ (¬ p2440))
    (h73722 : p4716 ∨ (¬ p2563))
    (h73418 : p3570 ∨ p2881)
    (h73226 : p2247 ∨ p2241)
    (h73390 : p3365 ∨ p2696)
    (h72955 : p4560)
    (h72629 : (¬ p3985) ∨ (¬ p4204) ∨ (¬ p4669) ∨ (¬ p4646) ∨ (¬ p4734) ∨ (¬ p4668) ∨ (¬ p2220) ∨ (¬ p2952) ∨ (¬ p2839) ∨ (¬ p3146) ∨ (¬ p3570) ∨ (¬ p3097) ∨ (¬ p4699) ∨ (¬ p4716) ∨ (¬ p3051) ∨ (¬ p2247) ∨ (¬ p4315) ∨ (¬ p2137) ∨ (¬ p2737) ∨ (¬ p2748) ∨ (¬ p3873) ∨ (¬ p2246) ∨ (¬ p3365) ∨ (¬ p2749) ∨ (¬ p4236) ∨ (¬ p4560) ∨ (¬ p3644))
    : (¬ p2839) ∨ p2946 ∨ p2911 ∨ (¬ p4646) ∨ (¬ p4668) ∨ (¬ p4669) ∨ (¬ p2220) ∨ (¬ p3051) ∨ p3136 ∨ (¬ p4204) ∨ p2274 ∨ (¬ p2440) ∨ (¬ p2563) ∨ p2881 ∨ (¬ p3146) ∨ (¬ p3873) ∨ (¬ p3985) ∨ (¬ p2137) ∨ (¬ p2748) ∨ p2241 ∨ (¬ p2246) ∨ (¬ p2737) ∨ (¬ p2749) ∨ (¬ p4236) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))))));
    let u25 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u26 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u27 : p4734 := h72735;
    let u28 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u29 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u30 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    let u31 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u32 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u33 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u19 r0))));
    let u34 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u24 r0))));
    let u35 : p4560 := h72955;
    (Or.elim h72629 (fun q0 => (False.elim (q0 u16))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u27))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u25))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u14))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u32))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u29))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u30))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u31))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u7))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u33))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u28))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u17))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u21))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u18))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u15))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u20))) (fun r21 => (Or.elim r21 (fun q22 => (False.elim (q22 u34))) (fun r22 => (Or.elim r22 (fun q23 => (False.elim (q23 u22))) (fun r23 => (Or.elim r23 (fun q24 => (False.elim (q24 u23))) (fun r24 => (Or.elim r24 (fun q25 => (False.elim (q25 u35))) (fun r25 => (False.elim (r25 u26)))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem step104133 (p2137 p2274 p2563 p2608 p2881 p3005 p3136 p3698 p3877 p4315 p4629 p4702 p4960 : Prop)
    (h73549 : (¬ p3136) ∨ (¬ p4315))
    (h73488 : p3877 ∨ p3005)
    (h72676 : (¬ p3877) ∨ (¬ p2608) ∨ (¬ p3698) ∨ (¬ p4960) ∨ (¬ p4702) ∨ (¬ p4629) ∨ (¬ p2137) ∨ p2881 ∨ p4315 ∨ (¬ p2274) ∨ (¬ p2563))
    : (¬ p2137) ∨ (¬ p3136) ∨ p3005 ∨ (¬ p4960) ∨ (¬ p4702) ∨ (¬ p4629) ∨ p2881 ∨ (¬ p2563) ∨ (¬ p2608) ∨ (¬ p2274) ∨ (¬ p3698) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p4315) := (Or.elim h73549 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u12 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72676 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u11 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step104142 (p2088 p2177 p2241 p2244 p2264 p2284 p2299 p2608 p2744 p2807 p2881 p2946 p3125 p3414 p3570 p3857 p4330 p4551 p4914 : Prop)
    (h73632 : p4551 ∨ (¬ p2264))
    (h73234 : p2299 ∨ p2177)
    (h73224 : p2244 ∨ p2241)
    (h73418 : p3570 ∨ p2881)
    (h73480 : p3857 ∨ p2088)
    (h73391 : (¬ p2807) ∨ (¬ p3414))
    (h70482 : (¬ p2244) ∨ (¬ p2608) ∨ (¬ p3857) ∨ (¬ p3125) ∨ (¬ p4914) ∨ (¬ p4330) ∨ (¬ p3570) ∨ (¬ p2299) ∨ (¬ p2946) ∨ p3414 ∨ (¬ p2744) ∨ (¬ p2284) ∨ (¬ p4551))
    : (¬ p2946) ∨ (¬ p3125) ∨ (¬ p2264) ∨ (¬ p2608) ∨ p2177 ∨ p2241 ∨ (¬ p2744) ∨ (¬ p4914) ∨ p2881 ∨ (¬ p4330) ∨ p2088 ∨ (¬ p2807) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p4551 := (Or.elim h73632 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u14 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u15 : p2244 := (Or.elim h73224 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u16 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u17 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u18 : (¬ p3414) := (Or.elim h73391 (fun q0 => (False.elim (q0 u11))) (fun r0 => r0));
    (Or.elim h70482 (fun q0 => (False.elim (q0 u15))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u17))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u16))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u14))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u18 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u6))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u12))) (fun r11 => (False.elim (r11 u13)))))))))))))))))))))))))))

theorem step104151 (p2187 p2363 p3125 p3256 p3989 p4602 : Prop)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73502 : p3989 ∨ p2187)
    (h70922 : p3256 ∨ (¬ p3125) ∨ (¬ p4602) ∨ (¬ p3989))
    : (¬ p3125) ∨ p3256 ∨ (¬ p2363) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70922 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step104165 (p2177 p2241 p2246 p2247 p2274 p2331 p2363 p2406 p2449 p2563 p2578 p2598 p2608 p2667 p2727 p2744 p2901 p2960 p3055 p3166 p3238 p3366 p3904 p3947 p4109 p4119 p4320 p4402 p4418 p4424 p4500 p4533 p4629 p4669 p4700 p4702 p4716 p4753 p4786 p4960 p4972 p5053 : Prop)
    (h73722 : p4716 ∨ (¬ p2563))
    (h73494 : p3947 ∨ p2449)
    (h73226 : p2247 ∨ p2241)
    (h73374 : p3238 ∨ p2406)
    (h73350 : p3055 ∨ p2598)
    (h73602 : p4500 ∨ p2177)
    (h73552 : p4320 ∨ p2901)
    (h70899 : (¬ p4320) ∨ (¬ p4402) ∨ (¬ p3055) ∨ (¬ p4424) ∨ (¬ p4418) ∨ (¬ p2331) ∨ (¬ p2667) ∨ (¬ p2960) ∨ (¬ p2247) ∨ (¬ p2246) ∨ (¬ p2727) ∨ (¬ p5053) ∨ (¬ p3166) ∨ (¬ p3947) ∨ (¬ p4960) ∨ (¬ p4702) ∨ (¬ p4700) ∨ (¬ p4119) ∨ (¬ p2363) ∨ (¬ p4669) ∨ (¬ p4972) ∨ (¬ p2744) ∨ (¬ p4629) ∨ (¬ p3238) ∨ (¬ p2608) ∨ (¬ p3366) ∨ (¬ p4753) ∨ (¬ p4500) ∨ (¬ p4533) ∨ (¬ p4109) ∨ (¬ p3904) ∨ (¬ p2578) ∨ (¬ p2274) ∨ (¬ p4786) ∨ (¬ p4716))
    : (¬ p2246) ∨ (¬ p4418) ∨ (¬ p2563) ∨ (¬ p4786) ∨ (¬ p4402) ∨ p2449 ∨ (¬ p2667) ∨ (¬ p2331) ∨ (¬ p2960) ∨ (¬ p2274) ∨ (¬ p2578) ∨ (¬ p5053) ∨ (¬ p2727) ∨ p2241 ∨ (¬ p3166) ∨ (¬ p4702) ∨ (¬ p4424) ∨ (¬ p4960) ∨ (¬ p4700) ∨ (¬ p4669) ∨ (¬ p4972) ∨ (¬ p2744) ∨ (¬ p2363) ∨ p2406 ∨ p2598 ∨ (¬ p4629) ∨ (¬ p3366) ∨ p2177 ∨ (¬ p4533) ∨ p2901 ∨ (¬ p4753) ∨ (¬ p4119) ∨ (¬ p2608) ∨ (¬ p3904) ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))));
    let u25 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))));
    let u26 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))));
    let u27 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))));
    let u28 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))));
    let u29 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))));
    let u30 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))));
    let u31 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))));
    let u32 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))));
    let u33 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))));
    let u34 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))))))))))))))));
    let u35 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u36 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u37 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u38 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u23 r0))));
    let u39 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u24 r0))));
    let u40 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u27 r0))));
    let u41 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u29 r0))));
    (Or.elim h70899 (fun q0 => (False.elim (q0 u41))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u39))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u16))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u37))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u12))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u14))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u36))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u17))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u15))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u18))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u31))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u22))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u19))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u20))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u21))) (fun r21 => (Or.elim r21 (fun q22 => (False.elim (q22 u25))) (fun r22 => (Or.elim r22 (fun q23 => (False.elim (q23 u38))) (fun r23 => (Or.elim r23 (fun q24 => (False.elim (q24 u32))) (fun r24 => (Or.elim r24 (fun q25 => (False.elim (q25 u26))) (fun r25 => (Or.elim r25 (fun q26 => (False.elim (q26 u30))) (fun r26 => (Or.elim r26 (fun q27 => (False.elim (q27 u40))) (fun r27 => (Or.elim r27 (fun q28 => (False.elim (q28 u28))) (fun r28 => (Or.elim r28 (fun q29 => (False.elim (q29 u34))) (fun r29 => (Or.elim r29 (fun q30 => (False.elim (q30 u33))) (fun r30 => (Or.elim r30 (fun q31 => (False.elim (q31 u10))) (fun r31 => (Or.elim r31 (fun q32 => (False.elim (q32 u9))) (fun r32 => (Or.elim r32 (fun q33 => (False.elim (q33 u3))) (fun r33 => (False.elim (r33 u35)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem step104171 (p2459 p2598 p2901 p2946 p3055 p3146 p3246 p3641 p3657 p3692 p3874 p3950 p4129 p4348 p4434 p4438 p4786 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73448 : p3692 ∨ p3146)
    (h73350 : p3055 ∨ p2598)
    (h73562 : p4348 ∨ p2459)
    (h71183 : (¬ p3874) ∨ (¬ p3246) ∨ (¬ p4129) ∨ (¬ p3055) ∨ (¬ p3692) ∨ (¬ p2946) ∨ (¬ p3950) ∨ (¬ p4348) ∨ (¬ p3657) ∨ (¬ p4434) ∨ (¬ p2901) ∨ (¬ p4786) ∨ (¬ p4438))
    : (¬ p4129) ∨ p3641 ∨ (¬ p2901) ∨ p3146 ∨ (¬ p4438) ∨ (¬ p3246) ∨ p2598 ∨ p2459 ∨ (¬ p3657) ∨ (¬ p4434) ∨ (¬ p3950) ∨ (¬ p2946) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4129 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u14 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u15 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u16 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71183 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u15))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u16))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u2))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u12))) (fun r11 => (False.elim (r11 u4)))))))))))))))))))))))))))

theorem step104173 (p2241 p2598 p2737 p3055 p3379 p3452 p4749 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73350 : p3055 ∨ p2598)
    (h70678 : (¬ p3452) ∨ (¬ p2737) ∨ (¬ p4749) ∨ (¬ p3055) ∨ (¬ p2241))
    : (¬ p2737) ∨ (¬ p2241) ∨ p3379 ∨ p2598 ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70678 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step104177 (p2230 p2352 p2440 p2589 p2850 p3422 p3584 p3956 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73284 : p2589 ∨ p2230)
    (h73500 : p3956 ∨ p2352)
    (h70918 : (¬ p2850) ∨ (¬ p2589) ∨ (¬ p2440) ∨ (¬ p3956) ∨ (¬ p3584))
    : p3422 ∨ (¬ p2850) ∨ (¬ p2440) ∨ p2230 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70918 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step104179 (p2427 p2850 p2901 p3904 p4109 p4320 p4700 p4753 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h70890 : (¬ p2850) ∨ (¬ p4320) ∨ (¬ p4700) ∨ (¬ p4753) ∨ (¬ p4109) ∨ (¬ p3904) ∨ (¬ p2427))
    : (¬ p2850) ∨ (¬ p4700) ∨ p2901 ∨ (¬ p2427) ∨ (¬ p4109) ∨ (¬ p4753) ∨ (¬ p3904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70890 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step104189 (p2901 p3246 p3631 p3690 p3817 p4957 : Prop)
    (h73445 : (¬ p3246) ∨ (¬ p3690))
    (h73468 : p3817 ∨ p3631)
    (h70051 : p3690 ∨ (¬ p3817) ∨ (¬ p4957) ∨ (¬ p2901))
    : (¬ p3246) ∨ p3631 ∨ (¬ p4957) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3690) := (Or.elim h73445 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70051 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step104194 (p2307 p2313 p2500 p3309 p3379 p3549 : Prop)
    (h73405 : (¬ p3309) ∨ (¬ p3549))
    (h73238 : p2313 ∨ p2307)
    (h71027 : p3549 ∨ (¬ p2500) ∨ (¬ p3379) ∨ (¬ p2313))
    : (¬ p3309) ∨ p2307 ∨ (¬ p3379) ∨ (¬ p2500) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2500 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3549) := (Or.elim h73405 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71027 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step104196 (p2230 p2241 p2247 p2440 p2744 p3379 p4079 p4257 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h70205 : (¬ p2247) ∨ (¬ p3379) ∨ (¬ p4079) ∨ (¬ p2440) ∨ (¬ p4257) ∨ (¬ p2744) ∨ (¬ p2230))
    : (¬ p2230) ∨ (¬ p3379) ∨ (¬ p4257) ∨ (¬ p4079) ∨ (¬ p2440) ∨ (¬ p2744) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h70205 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step104200 (p2352 p2406 p2440 p2542 p2553 p2922 p3238 p3389 p3564 p4079 p4137 p4620 p4710 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73270 : p2542 ∨ p2440)
    (h73374 : p3238 ∨ p2406)
    (h70807 : (¬ p4137) ∨ (¬ p3238) ∨ (¬ p4079) ∨ (¬ p2922) ∨ (¬ p2542) ∨ (¬ p4620) ∨ (¬ p3389) ∨ (¬ p2352) ∨ (¬ p2553) ∨ (¬ p4710))
    : (¬ p2553) ∨ p3564 ∨ p2440 ∨ (¬ p2922) ∨ (¬ p4620) ∨ p2406 ∨ (¬ p3389) ∨ (¬ p4079) ∨ (¬ p2352) ∨ (¬ p4710) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70807 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step104202 (p2187 p2248 p2274 p2307 p2373 p2459 p2493 p2499 p2528 p2553 p2578 p2901 p2922 p2928 p2946 p2958 p2992 p3051 p3166 p3176 p3309 p3370 p3379 p3452 p3556 p3989 p4433 p4506 p4554 p4667 p4702 p4771 p4973 : Prop)
    (h73698 : p4667 ∨ (¬ p2459))
    (h73502 : p3989 ∨ p2187)
    (h73360 : p3176 ∨ (¬ p3166))
    (h73413 : (¬ p3051) ∨ (¬ p3556))
    (h73634 : p4554 ∨ p2274)
    (h73320 : p2928 ∨ p2922)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h71163 : (¬ p4667) ∨ (¬ p2373) ∨ (¬ p4433) ∨ (¬ p3989) ∨ (¬ p4506) ∨ (¬ p4554) ∨ p3556 ∨ (¬ p2901) ∨ (¬ p3176) ∨ (¬ p2528) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p4702) ∨ (¬ p2928) ∨ (¬ p2992) ∨ (¬ p2499) ∨ (¬ p2946) ∨ (¬ p2958) ∨ (¬ p2578) ∨ (¬ p3309) ∨ (¬ p2307) ∨ (¬ p4771) ∨ (¬ p2248) ∨ (¬ p4973) ∨ (¬ p2553))
    : (¬ p3309) ∨ (¬ p2528) ∨ (¬ p4433) ∨ (¬ p2459) ∨ (¬ p4506) ∨ p2187 ∨ (¬ p4771) ∨ (¬ p2901) ∨ (¬ p3166) ∨ (¬ p3051) ∨ (¬ p2373) ∨ p2274 ∨ (¬ p4702) ∨ (¬ p2578) ∨ p2922 ∨ p2493 ∨ (¬ p3370) ∨ p3379 ∨ (¬ p2946) ∨ (¬ p2958) ∨ (¬ p2307) ∨ (¬ p2992) ∨ (¬ p2248) ∨ (¬ p4973) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))))));
    let u25 : p4667 := (Or.elim h73698 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u26 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u27 : p3176 := (Or.elim h73360 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u28 : (¬ p3556) := (Or.elim h73413 (fun q0 => (False.elim (q0 u9))) (fun r0 => r0));
    let u29 : p4554 := (Or.elim h73634 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u30 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    let u31 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u15 r0))));
    let u32 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u17 r0))));
    (Or.elim h71163 (fun q0 => (False.elim (q0 u25))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u26))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u29))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u28 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u27))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u16))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u32))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u12))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u30))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u21))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u31))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u18))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u19))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u13))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u0))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u20))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u6))) (fun r21 => (Or.elim r21 (fun q22 => (False.elim (q22 u22))) (fun r22 => (Or.elim r22 (fun q23 => (False.elim (q23 u23))) (fun r23 => (False.elim (r23 u24)))))))))))))))))))))))))))))))))))))))))))))))))))

theorem step104209 (p2177 p2608 p2881 p3449 p3527 p3860 p5142 p5304 : Prop)
    (h73992 : p5304 ∨ p3527)
    (h73482 : p3860 ∨ p3449)
    (h70600 : (¬ p5304) ∨ (¬ p3860) ∨ (¬ p2608) ∨ (¬ p5142) ∨ (¬ p2177) ∨ (¬ p2881))
    : p3527 ∨ p3449 ∨ (¬ p2177) ∨ (¬ p2881) ∨ (¬ p2608) ∨ (¬ p5142) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5142 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5304 := (Or.elim h73992 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70600 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step104225 (p2241 p2247 p2264 p2437 p2608 p2685 p2839 p2911 p3005 p3389 p3540 p3553 p3572 p3583 p3644 p3660 p3877 p3920 p3954 p4186 p4649 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73688 : p4649 ∨ p2437)
    (h73424 : p3583 ∨ p2839)
    (h73226 : p2247 ∨ p2241)
    (h73498 : p3954 ∨ p2608)
    (h73410 : p3553 ∨ p2264)
    (h73419 : (¬ p2685) ∨ (¬ p3572))
    (h73434 : p3644 ∨ p2911)
    (h73402 : p3540 ∨ p3389)
    (h70853 : (¬ p4649) ∨ (¬ p3583) ∨ (¬ p2247) ∨ (¬ p3954) ∨ (¬ p3644) ∨ (¬ p4186) ∨ p3572 ∨ (¬ p3877) ∨ (¬ p3920) ∨ (¬ p3660) ∨ (¬ p3540) ∨ (¬ p3553))
    : p3005 ∨ p2437 ∨ (¬ p4186) ∨ (¬ p3660) ∨ p2839 ∨ p2241 ∨ p2608 ∨ p2264 ∨ (¬ p2685) ∨ p2911 ∨ p3389 ∨ (¬ p3920) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p4649 := (Or.elim h73688 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u14 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u15 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u16 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u17 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u18 : (¬ p3572) := (Or.elim h73419 (fun q0 => (False.elim (q0 u8))) (fun r0 => r0));
    let u19 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u20 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h70853 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u16))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u19))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u18 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u20))) (fun r10 => (False.elim (r10 u17)))))))))))))))))))))))))

theorem step104230 (p2331 p2608 p2641 p2744 p2946 p2952 p2963 p4153 p4154 : Prop)
    (h73525 : (¬ p2641) ∨ (¬ p4154))
    (h73338 : p2963 ∨ p2331)
    (h73330 : p2952 ∨ p2946)
    (h70595 : p4154 ∨ (¬ p2744) ∨ (¬ p2608) ∨ (¬ p4153) ∨ (¬ p2963) ∨ (¬ p2952))
    : (¬ p2641) ∨ p2331 ∨ p2946 ∨ (¬ p4153) ∨ (¬ p2744) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4154) := (Or.elim h73525 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u7 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70595 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u8)))))))))))))

theorem step104254 (p2156 p2241 p2247 p2396 p2437 p2440 p2493 p2505 p2651 p2657 p2933 p2992 p3016 p3019 p3256 p3544 p3662 p3879 p4107 p4116 p4319 p4521 p4610 p4646 p4651 p4697 p4953 p4996 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73288 : p2657 ∨ p2651)
    (h73690 : p4651 ∨ (¬ p2437))
    (h73440 : p3662 ∨ p2992)
    (h73514 : p4107 ∨ p2396)
    (h70360 : (¬ p4996) ∨ (¬ p3256) ∨ (¬ p4697) ∨ (¬ p4953) ∨ (¬ p4319) ∨ (¬ p3662) ∨ (¬ p3544) ∨ (¬ p2247) ∨ (¬ p4107) ∨ (¬ p2493) ∨ (¬ p2505) ∨ (¬ p2156) ∨ (¬ p3016) ∨ (¬ p3019) ∨ (¬ p4610) ∨ (¬ p2657) ∨ (¬ p4521) ∨ (¬ p4646) ∨ (¬ p2440) ∨ (¬ p3879) ∨ (¬ p4651) ∨ (¬ p4116) ∨ (¬ p2933))
    : p2241 ∨ p2651 ∨ (¬ p3016) ∨ (¬ p4521) ∨ (¬ p2437) ∨ (¬ p2493) ∨ (¬ p4116) ∨ (¬ p2933) ∨ (¬ p4996) ∨ (¬ p4953) ∨ (¬ p3019) ∨ p2992 ∨ (¬ p4319) ∨ (¬ p2156) ∨ (¬ p3256) ∨ (¬ p4697) ∨ (¬ p3879) ∨ (¬ p4610) ∨ p2396 ∨ (¬ p4646) ∨ (¬ p2505) ∨ (¬ p2440) ∨ (¬ p3544) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))));
    let u23 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u24 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u25 : p4651 := (Or.elim h73690 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u26 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u27 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u18 r0))));
    (Or.elim h70360 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u26))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u22))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u23))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u27))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u20))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u13))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u2))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u10))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u17))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u24))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u3))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u19))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u21))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u16))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u25))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u6))) (fun r21 => (False.elim (r21 u7)))))))))))))))))))))))))))))))))))))))))))))))

theorem step104279 (p2341 p2608 p3527 p3551 p4793 p5306 : Prop)
    (h73994 : p5306 ∨ (¬ p3527))
    (h73408 : p3551 ∨ p2341)
    (h70601 : (¬ p5306) ∨ (¬ p4793) ∨ (¬ p2608) ∨ (¬ p3551))
    : (¬ p3527) ∨ (¬ p2608) ∨ (¬ p4793) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4793 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5306 := (Or.elim h73994 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70601 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step104288 (p2341 p2437 p2659 p2911 p3551 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h70620 : (¬ p2911) ∨ (¬ p2437) ∨ (¬ p2659) ∨ (¬ p3551))
    : p2341 ∨ (¬ p2911) ∨ (¬ p2437) ∨ (¬ p2659) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h70620 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step104289 (p2210 p2341 p2427 p2608 p3369 p3370 p3379 p3389 p3452 p3540 p3551 p3555 p4108 p5206 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73402 : p3540 ∨ p3389)
    (h73394 : p3452 ∨ p3379)
    (h73408 : p3551 ∨ p2341)
    (h70851 : (¬ p2608) ∨ (¬ p3555) ∨ (¬ p3370) ∨ (¬ p5206) ∨ (¬ p3369) ∨ (¬ p3452) ∨ (¬ p4108) ∨ (¬ p2427) ∨ (¬ p3540) ∨ (¬ p3551))
    : p2210 ∨ (¬ p4108) ∨ (¬ p2608) ∨ p3389 ∨ (¬ p5206) ∨ (¬ p3369) ∨ (¬ p3370) ∨ p3379 ∨ (¬ p2427) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h70851 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u13)))))))))))))))))))))

theorem step104290 (p2459 p2737 p2743 p2870 p2881 p2891 p3570 p4244 p4348 p5052 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73298 : p2743 ∨ p2737)
    (h73562 : p4348 ∨ p2459)
    (h73418 : p3570 ∨ p2881)
    (h70182 : (¬ p4244) ∨ (¬ p5052) ∨ (¬ p2743) ∨ (¬ p2891) ∨ (¬ p3570) ∨ (¬ p4348))
    : p2870 ∨ p2737 ∨ (¬ p2891) ∨ p2459 ∨ (¬ p5052) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70182 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (False.elim (r4 u8)))))))))))))

theorem step104295 (p2177 p2187 p2274 p2295 p2307 p2331 p2363 p2383 p2396 p2406 p2417 p2427 p2459 p2744 p2881 p3097 p3426 p3537 p3741 p3950 p3989 p4242 p4260 p4336 p4347 p4348 p4401 p4436 p4518 p4717 p4718 p4753 p4805 p4972 p5370 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73538 : p4242 ∨ p3537)
    (h73502 : p3989 ∨ p2187)
    (h73562 : p4348 ∨ p2459)
    (h73560 : p4347 ∨ p2363)
    (h70141 : (¬ p2406) ∨ (¬ p4242) ∨ (¬ p4436) ∨ (¬ p4518) ∨ (¬ p3426) ∨ (¬ p5370) ∨ (¬ p4753) ∨ (¬ p2744) ∨ (¬ p4972) ∨ (¬ p4805) ∨ (¬ p4401) ∨ (¬ p2307) ∨ (¬ p2383) ∨ (¬ p4347) ∨ (¬ p3950) ∨ (¬ p4348) ∨ (¬ p2331) ∨ (¬ p2417) ∨ (¬ p2427) ∨ (¬ p3741) ∨ (¬ p4718) ∨ (¬ p4717) ∨ (¬ p2295) ∨ (¬ p2881) ∨ (¬ p3989) ∨ (¬ p2177) ∨ (¬ p4336) ∨ (¬ p2396) ∨ (¬ p4260) ∨ (¬ p3097))
    : (¬ p4260) ∨ (¬ p2406) ∨ (¬ p2396) ∨ (¬ p4518) ∨ (¬ p4436) ∨ (¬ p5370) ∨ (¬ p4753) ∨ (¬ p2744) ∨ (¬ p4972) ∨ (¬ p4805) ∨ (¬ p4401) ∨ p2274 ∨ p3537 ∨ (¬ p2383) ∨ p2187 ∨ p2459 ∨ (¬ p2331) ∨ (¬ p2307) ∨ (¬ p3950) ∨ (¬ p3741) ∨ p2363 ∨ (¬ p4717) ∨ (¬ p4718) ∨ (¬ p2177) ∨ (¬ p2881) ∨ (¬ p2295) ∨ (¬ p2427) ∨ (¬ p2417) ∨ (¬ p3426) ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4436 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4805 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))));
    let u25 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))));
    let u26 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))));
    let u27 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))));
    let u28 : p3426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))));
    let u29 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))))))))))))))));
    let u30 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u31 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    let u32 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    let u33 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u15 r0))));
    let u34 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u20 r0))));
    (Or.elim h70141 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u31))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u28))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u17))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u13))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u34))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u18))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u33))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u16))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u27))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u26))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u19))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u22))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u21))) (fun r21 => (Or.elim r21 (fun q22 => (False.elim (q22 u25))) (fun r22 => (Or.elim r22 (fun q23 => (False.elim (q23 u24))) (fun r23 => (Or.elim r23 (fun q24 => (False.elim (q24 u32))) (fun r24 => (Or.elim r24 (fun q25 => (False.elim (q25 u23))) (fun r25 => (Or.elim r25 (fun q26 => (False.elim (q26 u29))) (fun r26 => (Or.elim r26 (fun q27 => (False.elim (q27 u2))) (fun r27 => (Or.elim r27 (fun q28 => (False.elim (q28 u0))) (fun r28 => (False.elim (r28 u30)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem step104349 (p2396 p2427 p2563 p3434 p3658 p4324 p4555 p4643 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h73684 : p4643 ∨ p2427)
    (h69913 : (¬ p4643) ∨ (¬ p4324) ∨ (¬ p2396) ∨ (¬ p3658) ∨ (¬ p2563) ∨ (¬ p4555))
    : p3434 ∨ (¬ p2396) ∨ (¬ p4555) ∨ (¬ p3658) ∨ p2427 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4643 := (Or.elim h73684 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69913 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step104355 (p2241 p2251 p2331 p2528 p2641 p2911 p3389 p3399 p4116 p4154 p4778 p4923 p4975 p5214 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73832 : p4923 ∨ (¬ p2911))
    (h73230 : p2251 ∨ (¬ p2241))
    (h70031 : p3399 ∨ (¬ p2251) ∨ (¬ p4154) ∨ (¬ p4778) ∨ (¬ p5214) ∨ (¬ p4116) ∨ (¬ p4923) ∨ (¬ p3389) ∨ (¬ p4975) ∨ (¬ p2331) ∨ (¬ p2528))
    : p3399 ∨ (¬ p2528) ∨ (¬ p2331) ∨ (¬ p5214) ∨ (¬ p4975) ∨ (¬ p4116) ∨ (¬ p4778) ∨ p2641 ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p4923 := (Or.elim h73832 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u13 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    (Or.elim h70031 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u1)))))))))))))))))))))))

theorem step104356 (p2241 p2251 p2331 p2741 p3379 p3452 p4116 p4975 : Prop)
    (h73230 : p2251 ∨ (¬ p2241))
    (h73394 : p3452 ∨ p3379)
    (h70036 : (¬ p2741) ∨ (¬ p2251) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4975) ∨ (¬ p2331))
    : (¬ p2241) ∨ p3379 ∨ (¬ p4116) ∨ (¬ p2741) ∨ (¬ p2331) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70036 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step104358 (p2241 p2741 p2807 p3379 p3452 p4116 p4376 p4652 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h69818 : (¬ p3452) ∨ (¬ p4376) ∨ (¬ p2741) ∨ (¬ p4116) ∨ (¬ p2241) ∨ (¬ p4652) ∨ (¬ p2807))
    : (¬ p4116) ∨ (¬ p2741) ∨ p3379 ∨ (¬ p4652) ∨ (¬ p4376) ∨ (¬ p2807) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69818 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step104360 (p2156 p2230 p2274 p2363 p2440 p2665 p2668 p3016 p3097 p3324 p3574 p3646 p4198 p4347 p4375 p4390 p4537 p4753 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73352 : p3097 ∨ p2274)
    (h73624 : p4537 ∨ (¬ p2230))
    (h73436 : p3646 ∨ p2156)
    (h73560 : p4347 ∨ p2363)
    (h73386 : p3324 ∨ p2668)
    (h70198 : (¬ p2440) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4198) ∨ (¬ p4347) ∨ (¬ p2665) ∨ (¬ p3324) ∨ (¬ p4753) ∨ (¬ p4375) ∨ (¬ p4390) ∨ (¬ p4537) ∨ (¬ p3574))
    : (¬ p4375) ∨ p3016 ∨ p2274 ∨ (¬ p4753) ∨ (¬ p2230) ∨ p2156 ∨ (¬ p4198) ∨ (¬ p4390) ∨ p2363 ∨ (¬ p2665) ∨ (¬ p2440) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4375 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u14 : p4537 := (Or.elim h73624 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u15 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u16 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u17 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h70198 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u16))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u17))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u14))) (fun r10 => (False.elim (r10 u12)))))))))))))))))))))))))

theorem step104363 (p2427 p2707 p2839 p3588 p3959 p4169 p4882 : Prop)
    (h73430 : p3588 ∨ p2707)
    (h69957 : (¬ p2839) ∨ (¬ p3959) ∨ (¬ p3588) ∨ (¬ p4169) ∨ (¬ p4882) ∨ (¬ p2427))
    : p2707 ∨ (¬ p2839) ∨ (¬ p4882) ∨ (¬ p4169) ∨ (¬ p3959) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3588 := (Or.elim h73430 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h69957 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step104365 (p2177 p2341 p2437 p2470 p2481 p2482 p2553 p2608 p2707 p2807 p2911 p3367 p3585 p3658 p3742 p4500 p4586 p4707 p4732 p4753 p4792 p4921 : Prop)
    (h73732 : p4732 ∨ p2608)
    (h73762 : p4792 ∨ p2707)
    (h73428 : p3585 ∨ p3367)
    (h73716 : p4707 ∨ p2553)
    (h73652 : p4586 ∨ p2341)
    (h73452 : p3742 ∨ p2437)
    (h73602 : p4500 ∨ p2177)
    (h73830 : p4921 ∨ p2911)
    (h70568 : (¬ p4732) ∨ (¬ p3658) ∨ (¬ p3585) ∨ (¬ p4707) ∨ (¬ p2807) ∨ (¬ p2470) ∨ (¬ p2482) ∨ (¬ p2481) ∨ (¬ p4792) ∨ (¬ p4586) ∨ (¬ p4921) ∨ (¬ p3742) ∨ (¬ p4753) ∨ (¬ p4500))
    : p2608 ∨ (¬ p2470) ∨ p2707 ∨ p3367 ∨ p2553 ∨ (¬ p2807) ∨ (¬ p3658) ∨ p2341 ∨ p2437 ∨ (¬ p2482) ∨ p2177 ∨ (¬ p2481) ∨ (¬ p4753) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2482 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2481 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u15 : p4792 := (Or.elim h73762 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u16 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u17 : p4707 := (Or.elim h73716 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u18 : p4586 := (Or.elim h73652 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u19 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u20 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u21 : p4921 := (Or.elim h73830 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    (Or.elim h70568 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u16))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u17))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u15))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u18))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u21))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u19))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u12))) (fun r12 => (False.elim (r12 u20)))))))))))))))))))))))))))))

theorem step104373 (p2284 p2563 p2630 p2641 p2696 p2810 p2881 p2891 p2911 p3136 p3361 p3579 p4117 p4241 p4555 p4704 : Prop)
    (h73046 : p4704)
    (h73316 : p2810 ∨ p2630)
    (h69905 : (¬ p3136) ∨ (¬ p3579) ∨ (¬ p2810) ∨ (¬ p4704) ∨ (¬ p4241) ∨ (¬ p2891) ∨ (¬ p2641) ∨ (¬ p2696) ∨ (¬ p4117) ∨ (¬ p3361) ∨ (¬ p2911) ∨ (¬ p2284) ∨ (¬ p2881) ∨ (¬ p2563) ∨ (¬ p4555))
    : (¬ p2284) ∨ (¬ p2881) ∨ (¬ p4555) ∨ (¬ p3361) ∨ (¬ p4117) ∨ (¬ p2911) ∨ (¬ p2563) ∨ (¬ p2891) ∨ p2630 ∨ (¬ p4241) ∨ (¬ p2641) ∨ (¬ p3579) ∨ (¬ p3136) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : p4704 := h73046;
    let u15 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h69905 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u5))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u0))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u1))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u6))) (fun r13 => (False.elim (r13 u2)))))))))))))))))))))))))))))))

theorem step104376 (p2210 p2331 p2651 p2963 p3379 p3412 p3555 p4448 p4972 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73338 : p2963 ∨ p2331)
    (h70815 : (¬ p3555) ∨ (¬ p3379) ∨ (¬ p4448) ∨ (¬ p3412) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p4972))
    : p2210 ∨ p2331 ∨ (¬ p3379) ∨ (¬ p3412) ∨ (¬ p4448) ∨ (¬ p4972) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4448 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70815 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step104378 (p2177 p2248 p2481 p2518 p2608 p2665 p2807 p2881 p2946 p2958 p3016 p3083 p3093 p3146 p3156 p3201 p3266 p3319 p3367 p3570 p3582 p3585 p3587 p3591 p3658 p3741 p3945 p3954 p3979 p4026 p4115 p4203 p4238 p4256 p4276 p4279 p4444 p4502 p4556 p4717 p4753 p5119 p5203 : Prop)
    (h73604 : p4502 ∨ (¬ p2177))
    (h73580 : p4444 ∨ p3266)
    (h73428 : p3585 ∨ p3367)
    (h73542 : p4256 ∨ p3083)
    (h73504 : p4026 ∨ p3319)
    (h73418 : p3570 ∨ p2881)
    (h73432 : p3591 ∨ p3093)
    (h73498 : p3954 ∨ p2608)
    (h70564 : (¬ p4502) ∨ (¬ p3979) ∨ (¬ p4026) ∨ (¬ p5119) ∨ (¬ p4444) ∨ (¬ p4256) ∨ (¬ p3146) ∨ (¬ p3591) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p3201) ∨ (¬ p3582) ∨ (¬ p3570) ∨ (¬ p3945) ∨ (¬ p3587) ∨ (¬ p2807) ∨ (¬ p3156) ∨ (¬ p2481) ∨ (¬ p3741) ∨ (¬ p2518) ∨ (¬ p5203) ∨ (¬ p4279) ∨ (¬ p4238) ∨ (¬ p4115) ∨ (¬ p4556) ∨ (¬ p4203) ∨ (¬ p4276) ∨ (¬ p3016) ∨ (¬ p2248) ∨ (¬ p4753) ∨ (¬ p2946) ∨ (¬ p2958) ∨ (¬ p2665) ∨ (¬ p4717) ∨ (¬ p3954))
    : (¬ p2481) ∨ (¬ p2518) ∨ (¬ p4753) ∨ (¬ p2177) ∨ (¬ p2946) ∨ (¬ p3016) ∨ p3266 ∨ (¬ p5119) ∨ p3367 ∨ p3083 ∨ (¬ p3201) ∨ (¬ p3582) ∨ (¬ p3658) ∨ (¬ p3146) ∨ (¬ p3587) ∨ (¬ p3945) ∨ (¬ p3156) ∨ (¬ p3979) ∨ (¬ p2807) ∨ p3319 ∨ (¬ p5203) ∨ p2881 ∨ (¬ p4279) ∨ (¬ p3741) ∨ (¬ p4238) ∨ (¬ p4203) ∨ (¬ p4276) ∨ (¬ p4115) ∨ (¬ p4556) ∨ p3093 ∨ (¬ p2248) ∨ (¬ p2958) ∨ (¬ p2665) ∨ (¬ p4717) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2481 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3587 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p5203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))));
    let u25 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))));
    let u26 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))));
    let u27 : p4115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))));
    let u28 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))));
    let u29 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))));
    let u30 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))));
    let u31 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))));
    let u32 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))));
    let u33 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))));
    let u34 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))))))))))))))));
    let u35 : p4502 := (Or.elim h73604 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u36 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u37 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u38 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u39 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u19 r0))));
    let u40 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u21 r0))));
    let u41 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u29 r0))));
    let u42 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u34 r0))));
    (Or.elim h70564 (fun q0 => (False.elim (q0 u35))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u17))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u39))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u36))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u38))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u41))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u37))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u40))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u15))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u14))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u18))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u16))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u0))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u23))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u1))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u20))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u22))) (fun r21 => (Or.elim r21 (fun q22 => (False.elim (q22 u24))) (fun r22 => (Or.elim r22 (fun q23 => (False.elim (q23 u27))) (fun r23 => (Or.elim r23 (fun q24 => (False.elim (q24 u28))) (fun r24 => (Or.elim r24 (fun q25 => (False.elim (q25 u25))) (fun r25 => (Or.elim r25 (fun q26 => (False.elim (q26 u26))) (fun r26 => (Or.elim r26 (fun q27 => (False.elim (q27 u5))) (fun r27 => (Or.elim r27 (fun q28 => (False.elim (q28 u30))) (fun r28 => (Or.elim r28 (fun q29 => (False.elim (q29 u2))) (fun r29 => (Or.elim r29 (fun q30 => (False.elim (q30 u4))) (fun r30 => (Or.elim r30 (fun q31 => (False.elim (q31 u31))) (fun r31 => (Or.elim r31 (fun q32 => (False.elim (q32 u32))) (fun r32 => (Or.elim r32 (fun q33 => (False.elim (q33 u33))) (fun r33 => (False.elim (r33 u42)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem step104402 (p2493 p2911 p3527 p3548 p4708 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h70035 : (¬ p3548) ∨ (¬ p2493) ∨ (¬ p2911) ∨ (¬ p4708))
    : p3527 ∨ (¬ p2911) ∨ (¬ p4708) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4708 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h70035 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step104403 (p2177 p2341 p2573 p3389 p3551 p4708 p5196 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73952 : p5196 ∨ p3389)
    (h70599 : (¬ p5196) ∨ (¬ p2573) ∨ (¬ p4708) ∨ (¬ p2177) ∨ (¬ p3551))
    : p2341 ∨ (¬ p2177) ∨ (¬ p4708) ∨ p3389 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4708 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p5196 := (Or.elim h73952 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70599 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step104414 (p2088 p2307 p2363 p3857 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h72660 : (¬ p3857) ∨ (¬ p2363) ∨ (¬ p2307))
    : (¬ p2307) ∨ p2088 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h72660 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u0)))))))

theorem step104423 (p2608 p2696 p3367 p3379 p3452 p4735 p4749 p5213 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73734 : p4735 ∨ (¬ p2608))
    (h73960 : p5213 ∨ p3367)
    (h70940 : (¬ p4735) ∨ (¬ p3452) ∨ (¬ p5213) ∨ (¬ p4749) ∨ (¬ p2696))
    : p3379 ∨ (¬ p2608) ∨ p3367 ∨ (¬ p4749) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4735 := (Or.elim h73734 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p5213 := (Or.elim h73960 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70940 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step104424 (p2132 p2241 p2247 p2608 p4735 p5052 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73734 : p4735 ∨ (¬ p2608))
    (h69826 : (¬ p2247) ∨ (¬ p2132) ∨ (¬ p5052) ∨ (¬ p4735))
    : p2241 ∨ (¬ p2608) ∨ (¬ p2132) ∨ (¬ p5052) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4735 := (Or.elim h73734 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h69826 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step104425 (p2156 p2230 p2573 p2579 p3646 p4537 : Prop)
    (h73435 : (¬ p2156) ∨ (¬ p3646))
    (h73624 : p4537 ∨ (¬ p2230))
    (h73274 : p2579 ∨ p2573)
    (h70225 : (¬ p2579) ∨ (¬ p4537) ∨ p3646)
    : (¬ p2156) ∨ (¬ p2230) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3646) := (Or.elim h73435 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4537 := (Or.elim h73624 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70225 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (u3 r1)))))))

theorem step104428 (p2598 p2651 p2657 p2696 p3055 p3365 p4236 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73349 : (¬ p2598) ∨ (¬ p3055))
    (h73390 : p3365 ∨ p2696)
    (h70792 : p3055 ∨ (¬ p3365) ∨ (¬ p4236) ∨ (¬ p2657))
    : p2651 ∨ (¬ p4236) ∨ (¬ p2598) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : (¬ p3055) := (Or.elim h73349 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70792 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step104429 (p2132 p2284 p2493 p2598 p2696 p3016 p3365 p3541 p3574 p3683 p4752 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73422 : p3574 ∨ p3016)
    (h69933 : (¬ p3365) ∨ (¬ p2132) ∨ (¬ p4752) ∨ (¬ p3683) ∨ (¬ p3574) ∨ (¬ p2493) ∨ (¬ p3541) ∨ (¬ p2598) ∨ (¬ p2284))
    : (¬ p2598) ∨ p2696 ∨ (¬ p3541) ∨ (¬ p4752) ∨ p3016 ∨ (¬ p2284) ∨ (¬ p2493) ∨ (¬ p3683) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69933 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step104432 (p2166 p2191 p2210 p2230 p2363 p2440 p2459 p2608 p2737 p2747 p2807 p3177 p3325 p3389 p3422 p3475 p3555 p3657 p3697 p4197 p4348 p4445 p4503 p4537 p4602 p4732 p4771 p4814 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73222 : p2191 ∨ p2166)
    (h73302 : p2747 ∨ (¬ p2737))
    (h73624 : p4537 ∨ (¬ p2230))
    (h73732 : p4732 ∨ p2608)
    (h73562 : p4348 ∨ p2459)
    (h72621 : (¬ p3422) ∨ (¬ p4537) ∨ (¬ p3325) ∨ (¬ p4602) ∨ (¬ p2191) ∨ (¬ p4445) ∨ (¬ p3657) ∨ (¬ p3475) ∨ (¬ p2807) ∨ (¬ p3177) ∨ (¬ p4771) ∨ (¬ p2747) ∨ (¬ p3697) ∨ (¬ p3555) ∨ p3389 ∨ (¬ p4503) ∨ (¬ p4732) ∨ (¬ p4814) ∨ (¬ p2440) ∨ (¬ p4197) ∨ (¬ p4348))
    : (¬ p3177) ∨ p2210 ∨ (¬ p4503) ∨ (¬ p2363) ∨ (¬ p4197) ∨ p3389 ∨ p2166 ∨ (¬ p3657) ∨ (¬ p4445) ∨ (¬ p2807) ∨ (¬ p3325) ∨ (¬ p4771) ∨ (¬ p2440) ∨ (¬ p2737) ∨ (¬ p3697) ∨ (¬ p2230) ∨ p2608 ∨ (¬ p4814) ∨ (¬ p3422) ∨ (¬ p3475) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))));
    let u21 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u22 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u23 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u24 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u25 : p4537 := (Or.elim h73624 (fun q0 => q0) (fun r0 => (False.elim (r0 u15))));
    let u26 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u16 r0))));
    let u27 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u20 r0))));
    (Or.elim h72621 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u25))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u22))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u23))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u19))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u24))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u14))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u21))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (u5 q14))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u2))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u26))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u17))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u12))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u4))) (fun r19 => (False.elim (r19 u27)))))))))))))))))))))))))))))))))))))))))))

theorem step104434 (p2440 p2651 p2657 p2807 p2901 p4699 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73712 : p4699 ∨ (¬ p2440))
    (h69812 : (¬ p4699) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2901))
    : (¬ p2901) ∨ p2651 ∨ (¬ p2807) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h69812 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step104436 (p2406 p2440 p2727 p3136 p4315 p4699 p4812 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73772 : p4812 ∨ (¬ p2727))
    (h73712 : p4699 ∨ (¬ p2440))
    (h69853 : (¬ p2406) ∨ (¬ p4812) ∨ (¬ p4699) ∨ (¬ p4315))
    : p3136 ∨ (¬ p2406) ∨ (¬ p2727) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4812 := (Or.elim h73772 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u6 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h69853 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step104437 (p2406 p2440 p2630 p2810 p4699 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73712 : p4699 ∨ (¬ p2440))
    (h69867 : (¬ p4699) ∨ (¬ p2810) ∨ (¬ p2406))
    : (¬ p2406) ∨ p2630 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h69867 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step104438 (p2187 p2241 p2251 p2363 p2437 p2651 p2727 p2996 p3189 p3246 p4347 p4505 p4651 p4809 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73606 : p4505 ∨ p2187)
    (h73690 : p4651 ∨ (¬ p2437))
    (h73770 : p4809 ∨ p2727)
    (h73230 : p2251 ∨ (¬ p2241))
    (h70238 : (¬ p3189) ∨ (¬ p3246) ∨ (¬ p4651) ∨ (¬ p4809) ∨ (¬ p4347) ∨ (¬ p2251) ∨ (¬ p2996) ∨ (¬ p4505) ∨ (¬ p2651))
    : (¬ p3246) ∨ p2363 ∨ (¬ p2996) ∨ p2187 ∨ (¬ p2437) ∨ (¬ p3189) ∨ (¬ p2651) ∨ p2727 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4505 := (Or.elim h73606 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4651 := (Or.elim h73690 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u12 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    (Or.elim h70238 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step104440 (p2132 p2187 p2230 p2241 p2247 p2274 p2352 p2363 p2474 p2553 p2563 p2589 p2911 p3136 p3246 p3379 p3644 p3690 p3989 p4110 p4557 p4594 p4602 p5050 p5189 : Prop)
    (h73948 : p5189 ∨ p3379)
    (h73446 : p3690 ∨ p3246)
    (h73284 : p2589 ∨ p2230)
    (h73656 : p4594 ∨ p2352)
    (h73434 : p3644 ∨ p2911)
    (h73502 : p3989 ∨ p2187)
    (h73894 : p5050 ∨ (¬ p3136))
    (h73636 : p4557 ∨ (¬ p2274))
    (h73516 : p4110 ∨ p2563)
    (h73226 : p2247 ∨ p2241)
    (h73662 : p4602 ∨ (¬ p2363))
    (h72642 : (¬ p4594) ∨ (¬ p5050) ∨ (¬ p2553) ∨ (¬ p5189) ∨ (¬ p2474) ∨ (¬ p4110) ∨ (¬ p3644) ∨ (¬ p3989) ∨ (¬ p2132) ∨ (¬ p4602) ∨ (¬ p2589) ∨ (¬ p2247) ∨ (¬ p4557) ∨ (¬ p3690))
    : p3379 ∨ p3246 ∨ (¬ p2553) ∨ p2230 ∨ (¬ p2474) ∨ p2352 ∨ p2911 ∨ p2187 ∨ (¬ p3136) ∨ (¬ p2132) ∨ (¬ p2274) ∨ p2563 ∨ p2241 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2474 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : p5189 := (Or.elim h73948 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u15 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u16 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u17 : p4594 := (Or.elim h73656 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u18 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u19 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u20 : p5050 := (Or.elim h73894 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u21 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    let u22 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u23 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    let u24 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    (Or.elim h72642 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u20))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u22))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u18))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u19))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u24))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u16))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u23))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u21))) (fun r12 => (False.elim (r12 u15)))))))))))))))))))))))))))))

theorem step104445 (p2177 p2187 p2230 p2241 p2244 p2274 p2295 p2363 p2563 p2589 p2668 p2860 p3125 p3136 p3324 p3568 p3744 p3758 p3989 p4197 p4500 p4557 p4602 p4614 p4714 p5050 : Prop)
    (h73415 : (¬ p2295) ∨ (¬ p3568))
    (h73224 : p2244 ∨ p2241)
    (h73386 : p3324 ∨ p2668)
    (h73284 : p2589 ∨ p2230)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73502 : p3989 ∨ p2187)
    (h73454 : p3744 ∨ p3125)
    (h73720 : p4714 ∨ p2563)
    (h73636 : p4557 ∨ (¬ p2274))
    (h73894 : p5050 ∨ (¬ p3136))
    (h73602 : p4500 ∨ p2177)
    (h73456 : p3758 ∨ p2860)
    (h70530 : (¬ p2589) ∨ (¬ p2244) ∨ (¬ p4714) ∨ (¬ p4602) ∨ (¬ p5050) ∨ p3568 ∨ (¬ p3324) ∨ (¬ p4557) ∨ (¬ p4614) ∨ (¬ p4197) ∨ (¬ p3989) ∨ (¬ p4500) ∨ (¬ p3744) ∨ (¬ p3758))
    : (¬ p2295) ∨ p2241 ∨ p2668 ∨ p2230 ∨ (¬ p2363) ∨ p2187 ∨ (¬ p4614) ∨ (¬ p4197) ∨ p3125 ∨ p2563 ∨ (¬ p2274) ∨ (¬ p3136) ∨ p2177 ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4614 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : (¬ p3568) := (Or.elim h73415 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u15 : p2244 := (Or.elim h73224 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u16 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u17 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u18 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u19 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u20 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u21 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u22 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    let u23 : p5050 := (Or.elim h73894 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    let u24 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    let u25 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    (Or.elim h70530 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u15))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u21))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u18))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u23))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u14 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u16))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u22))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u19))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u24))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u20))) (fun r12 => (False.elim (r12 u25)))))))))))))))))))))))))))))

theorem step104446 (p2187 p3093 p3449 p3591 p3860 p3989 p4518 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73481 : (¬ p3449) ∨ (¬ p3860))
    (h73502 : p3989 ∨ p2187)
    (h69891 : (¬ p3591) ∨ (¬ p4518) ∨ (¬ p3989) ∨ p3860)
    : p3093 ∨ (¬ p3449) ∨ (¬ p4518) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : (¬ p3860) := (Or.elim h73481 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69891 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (u5 r2)))))))))

theorem step104447 (p2132 p2138 p2139 p2166 p2177 p2187 p2210 p2220 p2241 p2244 p2284 p2307 p2373 p2417 p2459 p2498 p2528 p2578 p2737 p2740 p2946 p3093 p3166 p3201 p3379 p3399 p3555 p3591 p3631 p3817 p3830 p3834 p3876 p3920 p3945 p3988 p3989 p4033 p4278 p4355 p4366 p4383 p4395 p4500 p4506 p4669 p4702 p4718 p4752 p4786 p4881 p4902 p4960 p5043 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73432 : p3591 ∨ p3093)
    (h73546 : p4278 ∨ p2417)
    (h73602 : p4500 ∨ p2177)
    (h73468 : p3817 ∨ p3631)
    (h73214 : p2138 ∨ p2132)
    (h73474 : p3834 ∨ p3830)
    (h73486 : p3876 ∨ p3201)
    (h73296 : p2740 ∨ p2737)
    (h73502 : p3989 ∨ p2187)
    (h73570 : p4366 ∨ p3399)
    (h73224 : p2244 ∨ p2241)
    (h71175 : (¬ p2740) ∨ (¬ p3834) ∨ (¬ p3817) ∨ (¬ p4278) ∨ (¬ p5043) ∨ (¬ p4033) ∨ (¬ p4395) ∨ (¬ p4383) ∨ (¬ p4500) ∨ (¬ p4902) ∨ (¬ p2528) ∨ (¬ p4669) ∨ (¬ p2459) ∨ (¬ p3945) ∨ (¬ p4881) ∨ (¬ p3876) ∨ (¬ p4752) ∨ (¬ p4786) ∨ (¬ p2139) ∨ (¬ p2138) ∨ (¬ p2220) ∨ (¬ p2166) ∨ (¬ p2373) ∨ (¬ p4355) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4506) ∨ (¬ p3988) ∨ (¬ p3166) ∨ (¬ p2284) ∨ (¬ p4718) ∨ (¬ p4702) ∨ (¬ p4960) ∨ (¬ p2498) ∨ (¬ p2946) ∨ (¬ p4366) ∨ (¬ p2578) ∨ (¬ p2307) ∨ (¬ p2244) ∨ (¬ p3591) ∨ (¬ p3920))
    : p2210 ∨ (¬ p3166) ∨ p3093 ∨ p2417 ∨ (¬ p5043) ∨ (¬ p4033) ∨ (¬ p4395) ∨ (¬ p4383) ∨ p2177 ∨ (¬ p4902) ∨ p3631 ∨ (¬ p2528) ∨ (¬ p2459) ∨ (¬ p3945) ∨ (¬ p2307) ∨ (¬ p2946) ∨ p2132 ∨ (¬ p4786) ∨ (¬ p2139) ∨ (¬ p4669) ∨ (¬ p4881) ∨ p3830 ∨ p3201 ∨ (¬ p2373) ∨ (¬ p4355) ∨ p2737 ∨ (¬ p2166) ∨ (¬ p2220) ∨ (¬ p3988) ∨ (¬ p4752) ∨ (¬ p3379) ∨ (¬ p4718) ∨ (¬ p4702) ∨ (¬ p4960) ∨ (¬ p4506) ∨ p2187 ∨ (¬ p2284) ∨ (¬ p2578) ∨ p3399 ∨ p2241 ∨ (¬ p2498) ∨ (¬ p3920) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p4881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))));
    let u25 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))));
    let u26 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))));
    let u27 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))));
    let u28 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))));
    let u29 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))));
    let u30 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))));
    let u31 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))));
    let u32 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))));
    let u33 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))));
    let u34 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))));
    let u35 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))));
    let u36 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))));
    let u37 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))));
    let u38 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))));
    let u39 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))));
    let u40 : p2498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))));
    let u41 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))))))))))))))))))))))))))));
    let u42 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u43 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u44 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u45 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u46 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u47 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u16 r0))));
    let u48 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u21 r0))));
    let u49 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u22 r0))));
    let u50 : p2740 := (Or.elim h73296 (fun q0 => q0) (fun r0 => (False.elim (u25 r0))));
    let u51 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u35 r0))));
    let u52 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u38 r0))));
    let u53 : p2244 := (Or.elim h73224 (fun q0 => q0) (fun r0 => (False.elim (u39 r0))));
    (Or.elim h71175 (fun q0 => (False.elim (q0 u50))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u48))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u46))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u44))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u45))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u19))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u12))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u13))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u20))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u49))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u29))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u17))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u18))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u47))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u27))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u26))) (fun r21 => (Or.elim r21 (fun q22 => (False.elim (q22 u23))) (fun r22 => (Or.elim r22 (fun q23 => (False.elim (q23 u24))) (fun r23 => (Or.elim r23 (fun q24 => (False.elim (q24 u30))) (fun r24 => (Or.elim r24 (fun q25 => (False.elim (q25 u42))) (fun r25 => (Or.elim r25 (fun q26 => (False.elim (q26 u51))) (fun r26 => (Or.elim r26 (fun q27 => (False.elim (q27 u34))) (fun r27 => (Or.elim r27 (fun q28 => (False.elim (q28 u28))) (fun r28 => (Or.elim r28 (fun q29 => (False.elim (q29 u1))) (fun r29 => (Or.elim r29 (fun q30 => (False.elim (q30 u36))) (fun r30 => (Or.elim r30 (fun q31 => (False.elim (q31 u31))) (fun r31 => (Or.elim r31 (fun q32 => (False.elim (q32 u32))) (fun r32 => (Or.elim r32 (fun q33 => (False.elim (q33 u33))) (fun r33 => (Or.elim r33 (fun q34 => (False.elim (q34 u40))) (fun r34 => (Or.elim r34 (fun q35 => (False.elim (q35 u15))) (fun r35 => (Or.elim r35 (fun q36 => (False.elim (q36 u52))) (fun r36 => (Or.elim r36 (fun q37 => (False.elim (q37 u37))) (fun r37 => (Or.elim r37 (fun q38 => (False.elim (q38 u14))) (fun r38 => (Or.elim r38 (fun q39 => (False.elim (q39 u53))) (fun r39 => (Or.elim r39 (fun q40 => (False.elim (q40 u43))) (fun r40 => (False.elim (r40 u41)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem step104449 (p2187 p2630 p2668 p2810 p3005 p3989 p4417 p4560 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73502 : p3989 ∨ p2187)
    (h72955 : p4560)
    (h69815 : (¬ p3989) ∨ (¬ p4417) ∨ (¬ p2668) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4560))
    : (¬ p2668) ∨ (¬ p3005) ∨ p2630 ∨ p2187 ∨ (¬ p4417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4560 := h72955;
    (Or.elim h69815 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step104453 (p2187 p2563 p2598 p2850 p3055 p3367 p3585 p3684 p3989 p4110 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73350 : p3055 ∨ p2598)
    (h73502 : p3989 ∨ p2187)
    (h73516 : p4110 ∨ p2563)
    (h73428 : p3585 ∨ p3367)
    (h70917 : (¬ p3684) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p3055) ∨ (¬ p3585))
    : p2850 ∨ p2598 ∨ p2187 ∨ p2563 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70917 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u9)))))))))))

theorem step104455 (p2352 p2608 p2630 p2651 p2657 p3016 p3574 p3954 p3956 p4751 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73288 : p2657 ∨ p2651)
    (h73422 : p3574 ∨ p3016)
    (h73742 : p4751 ∨ (¬ p2630))
    (h73500 : p3956 ∨ p2352)
    (h70082 : (¬ p2657) ∨ (¬ p3954) ∨ (¬ p4751) ∨ (¬ p3574) ∨ (¬ p3956))
    : p2608 ∨ p2651 ∨ p3016 ∨ (¬ p2630) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4751 := (Or.elim h73742 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u9 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70082 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u9)))))))))))

theorem step104461 (p2122 p2241 p2251 p2363 p2437 p2440 p2459 p2608 p2727 p2946 p3146 p3389 p3822 p4602 p4649 p4667 p4699 p4812 p5055 p5196 : Prop)
    (h73896 : p5055 ∨ p3146)
    (h73472 : p3822 ∨ p2122)
    (h73952 : p5196 ∨ p3389)
    (h73688 : p4649 ∨ p2437)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73698 : p4667 ∨ (¬ p2459))
    (h73230 : p2251 ∨ (¬ p2241))
    (h73772 : p4812 ∨ (¬ p2727))
    (h73712 : p4699 ∨ (¬ p2440))
    (h70984 : (¬ p4602) ∨ (¬ p2946) ∨ (¬ p3822) ∨ (¬ p2608) ∨ (¬ p5055) ∨ (¬ p4667) ∨ (¬ p4812) ∨ (¬ p5196) ∨ (¬ p4649) ∨ (¬ p4699) ∨ (¬ p2251))
    : p3146 ∨ p2122 ∨ p3389 ∨ p2437 ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2459) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p2946) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p5055 := (Or.elim h73896 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p5196 := (Or.elim h73952 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u14 : p4649 := (Or.elim h73688 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u15 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u16 : p4667 := (Or.elim h73698 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u17 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u18 : p4812 := (Or.elim h73772 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u19 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    (Or.elim h70984 (fun q0 => (False.elim (q0 u15))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u16))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u18))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u14))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u19))) (fun r9 => (False.elim (r9 u17)))))))))))))))))))))))

theorem step104463 (p2122 p2210 p2241 p2247 p2383 p2387 p2608 p2881 p2891 p2972 p3093 p3146 p3692 p3822 p4450 p4556 p4900 p5019 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73246 : p2387 ∨ p2383)
    (h73448 : p3692 ∨ p3146)
    (h73878 : p5019 ∨ (¬ p3093))
    (h73818 : p4900 ∨ p2881)
    (h73472 : p3822 ∨ p2122)
    (h70580 : (¬ p3822) ∨ (¬ p2387) ∨ (¬ p2972) ∨ (¬ p2891) ∨ (¬ p2210) ∨ (¬ p4556) ∨ (¬ p5019) ∨ (¬ p4900) ∨ (¬ p3692) ∨ (¬ p4450) ∨ (¬ p2608) ∨ (¬ p2247))
    : p2241 ∨ p2383 ∨ p3146 ∨ (¬ p2608) ∨ (¬ p3093) ∨ (¬ p2210) ∨ (¬ p2972) ∨ p2881 ∨ (¬ p2891) ∨ (¬ p4556) ∨ p2122 ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u14 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u15 : p5019 := (Or.elim h73878 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u16 : p4900 := (Or.elim h73818 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u17 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h70580 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u15))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u16))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u14))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u3))) (fun r10 => (False.elim (r10 u12)))))))))))))))))))))))))

theorem step104464 (p2352 p2383 p2387 p2470 p2476 p4597 : Prop)
    (h73658 : p4597 ∨ (¬ p2352))
    (h73249 : (¬ p2470) ∨ (¬ p2476))
    (h73246 : p2387 ∨ p2383)
    (h70671 : (¬ p4597) ∨ p2476 ∨ (¬ p2387))
    : (¬ p2352) ∨ (¬ p2470) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4597 := (Or.elim h73658 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u4 : (¬ p2476) := (Or.elim h73249 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70671 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u5)))))))

theorem step104473 (p2241 p2251 p2651 p3379 : Prop)
    (h73230 : p2251 ∨ (¬ p2241))
    (h70347 : p3379 ∨ (¬ p2651) ∨ (¬ p2251))
    : p3379 ∨ (¬ p2241) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h70347 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step104477 (p2241 p2251 p2807 p2996 p3027 p3414 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73230 : p2251 ∨ (¬ p2241))
    (h73392 : p3414 ∨ p2807)
    (h69770 : (¬ p2251) ∨ (¬ p3414) ∨ (¬ p3027))
    : p2996 ∨ (¬ p2241) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u5 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69770 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (False.elim (r1 u3)))))))

theorem step104480 (p2156 p2274 p2284 p2563 p2598 p2696 p2881 p3055 p4484 p4557 p4714 p4788 : Prop)
    (h73594 : p4484 ∨ p2156)
    (h73760 : p4788 ∨ (¬ p2696))
    (h73636 : p4557 ∨ (¬ p2274))
    (h73350 : p3055 ∨ p2598)
    (h73720 : p4714 ∨ p2563)
    (h70939 : (¬ p2284) ∨ (¬ p4484) ∨ (¬ p4788) ∨ (¬ p4714) ∨ (¬ p3055) ∨ (¬ p4557) ∨ (¬ p2881))
    : (¬ p2284) ∨ p2156 ∨ (¬ p2696) ∨ (¬ p2274) ∨ p2598 ∨ (¬ p2881) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4484 := (Or.elim h73594 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u9 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h70939 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step104482 (p2274 p2284 p2307 p2313 p2437 p2563 p2651 p2657 p3097 p3742 p4110 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73238 : p2313 ∨ p2307)
    (h73516 : p4110 ∨ p2563)
    (h73288 : p2657 ∨ p2651)
    (h73352 : p3097 ∨ p2274)
    (h72650 : (¬ p2284) ∨ (¬ p3097) ∨ (¬ p2313) ∨ (¬ p4110) ∨ (¬ p2657) ∨ (¬ p3742))
    : (¬ p2284) ∨ p2437 ∨ p2307 ∨ p2563 ∨ p2651 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h72650 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step104484 (p2156 p2274 p2284 p2295 p3097 p3646 p4565 : Prop)
    (h73640 : p4565 ∨ (¬ p2284))
    (h73352 : p3097 ∨ p2274)
    (h73436 : p3646 ∨ p2156)
    (h70132 : (¬ p3646) ∨ (¬ p2295) ∨ (¬ p4565) ∨ (¬ p3097))
    : (¬ p2284) ∨ (¬ p2295) ∨ p2274 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4565 := (Or.elim h73640 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70132 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step104485 (p2284 p2331 p2563 p2651 p2657 p4110 p4565 p4705 : Prop)
    (h73640 : p4565 ∨ (¬ p2284))
    (h73516 : p4110 ∨ p2563)
    (h73288 : p2657 ∨ p2651)
    (h69995 : (¬ p4565) ∨ (¬ p4705) ∨ (¬ p4110) ∨ (¬ p2657) ∨ (¬ p2331))
    : (¬ p2284) ∨ (¬ p2331) ∨ p2563 ∨ p2651 ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4565 := (Or.elim h73640 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69995 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step104489 (p2751 p2870 p2901 p2996 p3027 p4333 p4906 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h71154 : p2870 ∨ (¬ p2751) ∨ (¬ p4906) ∨ (¬ p2901) ∨ (¬ p4333) ∨ (¬ p3027))
    : (¬ p2901) ∨ p2870 ∨ (¬ p4333) ∨ (¬ p4906) ∨ (¬ p2751) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71154 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step104491 (p2608 p2807 p2996 p3027 p3414 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73392 : p3414 ∨ p2807)
    (h69771 : (¬ p3414) ∨ (¬ p2608) ∨ (¬ p3027))
    : p2996 ∨ (¬ p2608) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69771 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step104494 (p2177 p2437 p2481 p3083 p3742 p4256 p4276 p5203 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73451 : (¬ p2437) ∨ (¬ p3742))
    (h70563 : p3742 ∨ (¬ p2177) ∨ (¬ p4256) ∨ (¬ p2481) ∨ (¬ p5203) ∨ (¬ p4276))
    : (¬ p2481) ∨ p3083 ∨ (¬ p2437) ∨ (¬ p5203) ∨ (¬ p2177) ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2481 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : (¬ p3742) := (Or.elim h73451 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h70563 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step104496 (p2177 p2274 p3125 p3744 p4666 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h71053 : (¬ p3744) ∨ (¬ p2177) ∨ (¬ p4666) ∨ (¬ p2274))
    : (¬ p2274) ∨ p3125 ∨ (¬ p4666) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71053 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step104497 (p2177 p2470 p2476 p2518 p2651 p2657 p3083 p4256 p4276 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73288 : p2657 ∨ p2651)
    (h73542 : p4256 ∨ p3083)
    (h69976 : (¬ p2518) ∨ (¬ p2476) ∨ (¬ p4256) ∨ (¬ p4276) ∨ (¬ p2657) ∨ (¬ p2177))
    : (¬ p2518) ∨ p2470 ∨ p2651 ∨ (¬ p2177) ∨ (¬ p4276) ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h69976 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step104500 (p2177 p2274 p2440 p2459 p2553 p2581 p2598 p2608 p2651 p2657 p2781 p2982 p3055 p3063 p4236 p4502 p4514 p4736 p4948 p5059 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73288 : p2657 ∨ p2651)
    (h73846 : p4948 ∨ p2982)
    (h73604 : p4502 ∨ (¬ p2177))
    (h71017 : (¬ p4502) ∨ (¬ p2459) ∨ p3063 ∨ (¬ p4948) ∨ (¬ p5059) ∨ (¬ p4736) ∨ (¬ p2608) ∨ (¬ p2781) ∨ (¬ p4236) ∨ (¬ p3055) ∨ (¬ p2553) ∨ (¬ p4514) ∨ (¬ p2274) ∨ (¬ p2581) ∨ (¬ p2440) ∨ (¬ p2657))
    : (¬ p4236) ∨ (¬ p4736) ∨ (¬ p2274) ∨ (¬ p2553) ∨ (¬ p5059) ∨ p2598 ∨ p3063 ∨ p2651 ∨ (¬ p2608) ∨ (¬ p2459) ∨ p2982 ∨ (¬ p2177) ∨ (¬ p2440) ∨ (¬ p4514) ∨ (¬ p2581) ∨ (¬ p2781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3063) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))));
    let u16 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u17 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u18 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u19 : p4502 := (Or.elim h73604 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    (Or.elim h71017 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u18))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u15))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u16))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u3))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u13))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u2))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u14))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u12))) (fun r14 => (False.elim (r14 u17)))))))))))))))))))))))))))))))))

theorem step104502 (p2274 p2284 p2563 p2598 p2881 p3093 p3201 p3591 p4554 p4565 p4903 p4992 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73634 : p4554 ∨ p2274)
    (h73640 : p4565 ∨ (¬ p2284))
    (h73820 : p4903 ∨ (¬ p2881))
    (h69914 : (¬ p3201) ∨ (¬ p3591) ∨ (¬ p4992) ∨ (¬ p2598) ∨ (¬ p4565) ∨ (¬ p4903) ∨ (¬ p2563) ∨ (¬ p4554))
    : (¬ p3201) ∨ p3093 ∨ (¬ p2563) ∨ p2274 ∨ (¬ p2284) ∨ (¬ p4992) ∨ (¬ p2598) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4554 := (Or.elim h73634 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4565 := (Or.elim h73640 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u11 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    (Or.elim h69914 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step104504 (p2177 p2230 p2299 p2427 p2459 p2589 p2662 p2727 p3747 p4042 p4111 p4235 p4348 p4559 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73562 : p4348 ∨ p2459)
    (h73536 : p4235 ∨ p2427)
    (h73284 : p2589 ∨ p2230)
    (h73234 : p2299 ∨ p2177)
    (h69795 : (¬ p2299) ∨ (¬ p4348) ∨ (¬ p3747) ∨ (¬ p4042) ∨ (¬ p4235) ∨ (¬ p2589) ∨ (¬ p4559) ∨ (¬ p4111) ∨ (¬ p2662))
    : (¬ p3747) ∨ p2727 ∨ p2459 ∨ (¬ p4042) ∨ p2427 ∨ (¬ p2662) ∨ p2230 ∨ (¬ p4559) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3747 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h69795 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step104514 (p2341 p2459 p3256 p4118 p4854 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h70207 : (¬ p2459) ∨ (¬ p4118) ∨ (¬ p2341) ∨ (¬ p4854))
    : p3256 ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p4854) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4854 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h70207 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step104522 (p2220 p2230 p2373 p2406 p2589 p3904 p4120 p4630 : Prop)
    (h73678 : p4630 ∨ (¬ p2406))
    (h73284 : p2589 ∨ p2230)
    (h73522 : p4120 ∨ p2220)
    (h71105 : (¬ p4630) ∨ (¬ p2373) ∨ (¬ p2589) ∨ (¬ p3904) ∨ (¬ p4120))
    : (¬ p2406) ∨ (¬ p2373) ∨ p2230 ∨ p2220 ∨ (¬ p3904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4630 := (Or.elim h73678 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71105 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step104525 (p2230 p2295 p2373 p2696 p2797 p3146 p3365 p3568 p3917 p4419 p4604 p4840 : Prop)
    (h73786 : p4840 ∨ p2797)
    (h73390 : p3365 ∨ p2696)
    (h73416 : p3568 ∨ p2295)
    (h70623 : (¬ p4840) ∨ (¬ p3917) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4604) ∨ (¬ p4419) ∨ (¬ p3365) ∨ (¬ p3568))
    : (¬ p3917) ∨ p2797 ∨ p2696 ∨ (¬ p4604) ∨ (¬ p4419) ∨ (¬ p3146) ∨ (¬ p2373) ∨ p2295 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3917 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4840 := (Or.elim h73786 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h70623 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u11)))))))))))))))))))

theorem step104526 (p2727 p2737 p2747 p2839 p3583 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73302 : p2747 ∨ (¬ p2737))
    (h70078 : (¬ p3583) ∨ (¬ p2747) ∨ (¬ p2727))
    : p2839 ∨ (¬ p2737) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h70078 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u2)))))))

theorem step104528 (p2241 p2427 p2563 p2737 p2747 p2839 p2860 p4110 p4873 : Prop)
    (h73802 : p4873 ∨ p2839)
    (h73516 : p4110 ∨ p2563)
    (h73302 : p2747 ∨ (¬ p2737))
    (h70761 : (¬ p2747) ∨ (¬ p2241) ∨ (¬ p4873) ∨ (¬ p2860) ∨ (¬ p2427) ∨ (¬ p4110))
    : (¬ p2427) ∨ (¬ p2860) ∨ p2839 ∨ p2563 ∨ (¬ p2241) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4873 := (Or.elim h73802 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h70761 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step104529 (p2230 p2427 p2737 p2747 p2839 p2881 p3189 p3246 p3256 p3759 p3950 p4118 p4360 p4749 p4873 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73802 : p4873 ∨ p2839)
    (h73302 : p2747 ∨ (¬ p2737))
    (h73566 : p4360 ∨ p3189)
    (h70159 : (¬ p2747) ∨ (¬ p4873) ∨ (¬ p4360) ∨ (¬ p3759) ∨ (¬ p2230) ∨ (¬ p3950) ∨ (¬ p4749) ∨ (¬ p4118) ∨ (¬ p3246) ∨ (¬ p2427) ∨ (¬ p2881))
    : (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3950) ∨ (¬ p3759) ∨ p3256 ∨ p2839 ∨ (¬ p2737) ∨ (¬ p4749) ∨ (¬ p3246) ∨ (¬ p2230) ∨ p3189 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4873 := (Or.elim h73802 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u14 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h70159 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (False.elim (r9 u1)))))))))))))))))))))))

theorem step104531 (p2406 p2737 p2839 p2850 p3238 p3583 p4749 p4883 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73374 : p3238 ∨ p2406)
    (h73808 : p4883 ∨ (¬ p2850))
    (h70647 : (¬ p4883) ∨ (¬ p3238) ∨ (¬ p3583) ∨ (¬ p2737) ∨ (¬ p4749))
    : (¬ p2737) ∨ p2839 ∨ p2406 ∨ (¬ p2850) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4883 := (Or.elim h73808 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h70647 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step104533 (p2132 p2142 p2839 p2891 p3051 p3486 p3583 : Prop)
    (h73218 : p2142 ∨ (¬ p2132))
    (h73398 : p3486 ∨ p2891)
    (h73424 : p3583 ∨ p2839)
    (h70247 : (¬ p3583) ∨ (¬ p2142) ∨ (¬ p3051) ∨ (¬ p3486))
    : (¬ p3051) ∨ (¬ p2132) ∨ p2891 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2142 := (Or.elim h73218 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h70247 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step104537 (p2143 p2144 p2563 p2839 p2860 p3367 p3583 p3758 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73456 : p3758 ∨ p2860)
    (h70214 : (¬ p3583) ∨ (¬ p3367) ∨ (¬ p2144) ∨ (¬ p2143) ∨ (¬ p3758) ∨ (¬ p2563))
    : (¬ p3367) ∨ p2839 ∨ (¬ p2563) ∨ (¬ p2144) ∨ (¬ p2143) ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70214 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step104549 (p2122 p2210 p2241 p2363 p2440 p2459 p2662 p2727 p2946 p3389 p3540 p3822 p4347 p4667 p4699 p4812 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73560 : p4347 ∨ p2363)
    (h73698 : p4667 ∨ (¬ p2459))
    (h73712 : p4699 ∨ (¬ p2440))
    (h73402 : p3540 ∨ p3389)
    (h73772 : p4812 ∨ (¬ p2727))
    (h70990 : (¬ p3822) ∨ (¬ p4667) ∨ (¬ p4347) ∨ (¬ p2210) ∨ (¬ p2946) ∨ (¬ p2662) ∨ (¬ p4812) ∨ (¬ p3540) ∨ (¬ p4699) ∨ (¬ p2241))
    : p2122 ∨ p2363 ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2440) ∨ p3389 ∨ (¬ p2210) ∨ (¬ p2727) ∨ (¬ p2946) ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p4667 := (Or.elim h73698 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u13 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u14 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u15 : p4812 := (Or.elim h73772 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    (Or.elim h70990 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u15))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u14))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step104551 (p2241 p2737 p3367 p3379 p3452 p4749 p5213 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73960 : p5213 ∨ p3367)
    (h70677 : (¬ p5213) ∨ (¬ p3452) ∨ (¬ p2737) ∨ (¬ p4749) ∨ (¬ p2241))
    : (¬ p2737) ∨ p3379 ∨ (¬ p4749) ∨ (¬ p2241) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p5213 := (Or.elim h73960 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70677 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step104556 (p2230 p2241 p2406 p2589 p2608 p3954 p4630 p4749 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73284 : p2589 ∨ p2230)
    (h73678 : p4630 ∨ (¬ p2406))
    (h69869 : (¬ p3954) ∨ (¬ p2241) ∨ (¬ p4749) ∨ (¬ p4630) ∨ (¬ p2589))
    : (¬ p2241) ∨ p2608 ∨ (¬ p4749) ∨ p2230 ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4630 := (Or.elim h73678 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h69869 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step104557 (p2241 p2252 p2608 p2750 p2774 p2819 p2946 p2952 p3146 p3156 p3497 p3692 p3906 p4318 p4732 p5580 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73448 : p3692 ∨ p3146)
    (h73732 : p4732 ∨ p2608)
    (h73400 : p3497 ∨ p3156)
    (h70691 : p5580 ∨ (¬ p4732) ∨ (¬ p2241) ∨ (¬ p2252) ∨ (¬ p3906) ∨ (¬ p4318) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2750) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p2952))
    : (¬ p4318) ∨ (¬ p2819) ∨ (¬ p3906) ∨ (¬ p2774) ∨ (¬ p2252) ∨ p2946 ∨ (¬ p2241) ∨ p3146 ∨ p2608 ∨ p5580 ∨ (¬ p2750) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p5580) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u14 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u15 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h70691 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u15))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u13))) (fun r10 => (False.elim (r10 u12)))))))))))))))))))))))))

theorem step104566 (p2156 p2187 p2210 p2241 p2244 p2363 p2563 p2608 p2744 p2946 p2956 p3641 p3874 p3990 p4508 p4520 p4697 p4735 p5160 : Prop)
    (h73224 : p2244 ∨ p2241)
    (h73614 : p4520 ∨ p2210)
    (h73334 : p2956 ∨ (¬ p2946))
    (h73734 : p4735 ∨ (¬ p2608))
    (h73608 : p4508 ∨ (¬ p2187))
    (h73484 : p3874 ∨ p3641)
    (h70907 : (¬ p4508) ∨ (¬ p4520) ∨ (¬ p2156) ∨ (¬ p3874) ∨ (¬ p5160) ∨ (¬ p2956) ∨ (¬ p3990) ∨ (¬ p2363) ∨ (¬ p2244) ∨ (¬ p4697) ∨ (¬ p2563) ∨ (¬ p4735) ∨ (¬ p2744))
    : (¬ p5160) ∨ p2241 ∨ (¬ p2156) ∨ p2210 ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p2608) ∨ (¬ p2187) ∨ (¬ p3990) ∨ p3641 ∨ (¬ p2563) ∨ (¬ p2363) ∨ (¬ p4697) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5160 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p2244 := (Or.elim h73224 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u14 : p4520 := (Or.elim h73614 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u15 : p2956 := (Or.elim h73334 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u16 : p4735 := (Or.elim h73734 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u17 : p4508 := (Or.elim h73608 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u18 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h70907 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u18))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u15))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u16))) (fun r11 => (False.elim (r11 u4)))))))))))))))))))))))))))

theorem step104567 (p2352 p2363 p2518 p2528 p2573 p3379 p5192 : Prop)
    (h73950 : p5192 ∨ (¬ p3379))
    (h70715 : (¬ p5192) ∨ (¬ p2352) ∨ (¬ p2518) ∨ (¬ p2573) ∨ (¬ p2528) ∨ (¬ p2363))
    : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2573) ∨ (¬ p3379) ∨ (¬ p2352) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5192 := (Or.elim h73950 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h70715 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step104573 (p2274 p2427 p2553 p2901 p4320 p4554 p4702 : Prop)
    (h73634 : p4554 ∨ p2274)
    (h73552 : p4320 ∨ p2901)
    (h71165 : (¬ p4554) ∨ (¬ p4320) ∨ (¬ p4702) ∨ (¬ p2427) ∨ (¬ p2553))
    : (¬ p2553) ∨ p2274 ∨ p2901 ∨ (¬ p4702) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4554 := (Or.elim h73634 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71165 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step104576 (p2132 p2210 p2241 p2247 p2737 p2740 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73296 : p2740 ∨ p2737)
    (h70172 : (¬ p2132) ∨ (¬ p2740) ∨ (¬ p2210) ∨ (¬ p2247))
    : p2241 ∨ p2737 ∨ (¬ p2132) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2740 := (Or.elim h73296 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70172 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step104578 (p2187 p2274 p2295 p2563 p2668 p3097 p4714 : Prop)
    (h73720 : p4714 ∨ p2563)
    (h73352 : p3097 ∨ p2274)
    (h70131 : (¬ p4714) ∨ (¬ p2295) ∨ (¬ p2668) ∨ p2187 ∨ (¬ p3097))
    : (¬ p2668) ∨ (¬ p2295) ∨ p2563 ∨ p2187 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70131 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step104580 (p2166 p2440 p2459 p2542 p2737 p2747 p2881 p2891 p3016 p4900 p4971 : Prop)
    (h73302 : p2747 ∨ (¬ p2737))
    (h73270 : p2542 ∨ p2440)
    (h73818 : p4900 ∨ p2881)
    (h73858 : p4971 ∨ p3016)
    (h70188 : (¬ p2542) ∨ (¬ p4971) ∨ (¬ p4900) ∨ (¬ p2459) ∨ (¬ p2891) ∨ (¬ p2166) ∨ (¬ p2747))
    : (¬ p2737) ∨ p2440 ∨ p2881 ∨ (¬ p2891) ∨ (¬ p2459) ∨ p3016 ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4900 := (Or.elim h73818 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4971 := (Or.elim h73858 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70188 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u7)))))))))))))))

theorem step104583 (p2651 p2657 p3016 p3422 p3574 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73422 : p3574 ∨ p3016)
    (h70204 : (¬ p2657) ∨ (¬ p3422) ∨ (¬ p3574))
    : p2651 ∨ p3016 ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70204 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u4)))))))

theorem step104586 (p2230 p2406 p2563 p2598 p2727 p3201 p4535 p4716 p4728 p4812 : Prop)
    (h73622 : p4535 ∨ p2230)
    (h73730 : p4728 ∨ (¬ p2598))
    (h73722 : p4716 ∨ (¬ p2563))
    (h73772 : p4812 ∨ (¬ p2727))
    (h69890 : (¬ p3201) ∨ (¬ p4728) ∨ (¬ p4535) ∨ (¬ p4812) ∨ (¬ p4716) ∨ (¬ p2406))
    : (¬ p3201) ∨ (¬ p2406) ∨ p2230 ∨ (¬ p2598) ∨ (¬ p2563) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4535 := (Or.elim h73622 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4728 := (Or.elim h73730 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u8 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u9 : p4812 := (Or.elim h73772 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h69890 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step104589 (p2156 p2406 p2563 p3646 p5191 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h70451 : (¬ p3646) ∨ (¬ p2406) ∨ (¬ p5191) ∨ (¬ p2563))
    : (¬ p2406) ∨ p2156 ∨ (¬ p5191) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70451 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step104599 (p2132 p2138 p2352 p2528 p2534 p2598 p2630 p2727 p3055 p3422 p3573 p3584 p3956 p4748 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73500 : p3956 ∨ p2352)
    (h73268 : p2534 ∨ p2528)
    (h73349 : (¬ p2598) ∨ (¬ p3055))
    (h73740 : p4748 ∨ p2630)
    (h73426 : p3584 ∨ p3422)
    (h69929 : (¬ p4748) ∨ (¬ p2727) ∨ (¬ p3584) ∨ (¬ p2138) ∨ (¬ p3956) ∨ (¬ p3573) ∨ (¬ p2534) ∨ p3055)
    : p2132 ∨ (¬ p2727) ∨ p2352 ∨ p2528 ∨ (¬ p3573) ∨ (¬ p2598) ∨ p2630 ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : (¬ p3055) := (Or.elim h73349 (fun q0 => (False.elim (q0 u5))) (fun r0 => r0));
    let u12 : p4748 := (Or.elim h73740 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h69929 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (u11 r6)))))))))))))))))

theorem step104611 (p2295 p2307 p2317 p2573 p2583 p3016 p3568 p4971 : Prop)
    (h73242 : p2317 ∨ (¬ p2307))
    (h73858 : p4971 ∨ p3016)
    (h73416 : p3568 ∨ p2295)
    (h73278 : p2583 ∨ (¬ p2573))
    (h70538 : (¬ p4971) ∨ (¬ p2317) ∨ (¬ p3568) ∨ (¬ p2583))
    : (¬ p2307) ∨ p3016 ∨ p2295 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2317 := (Or.elim h73242 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u5 : p4971 := (Or.elim h73858 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2583 := (Or.elim h73278 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h70538 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u7)))))))))

theorem step104613 (p2248 p2331 p2608 p2737 p2829 p3688 p3954 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h71193 : (¬ p3688) ∨ (¬ p2331) ∨ (¬ p3954) ∨ (¬ p2737) ∨ (¬ p2248))
    : p2829 ∨ p2608 ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71193 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step104616 (p2230 p2406 p2881 p3238 p3389 p3540 p3570 p4001 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73374 : p3238 ∨ p2406)
    (h73402 : p3540 ∨ p3389)
    (h70372 : (¬ p3540) ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p4001) ∨ (¬ p3570))
    : p2881 ∨ (¬ p4001) ∨ p2406 ∨ (¬ p2230) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70372 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step104618 (p2406 p2493 p2503 p2590 p3238 : Prop)
    (h73264 : p2503 ∨ (¬ p2493))
    (h73374 : p3238 ∨ p2406)
    (h70212 : (¬ p2503) ∨ (¬ p3238) ∨ (¬ p2590))
    : (¬ p2493) ∨ (¬ p2590) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2503 := (Or.elim h73264 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u4 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70212 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u1)))))))

theorem step104620 (p2406 p2493 p2573 p2579 p2891 p3486 p4203 p4555 p4627 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73274 : p2579 ∨ p2573)
    (h73676 : p4627 ∨ p2406)
    (h70322 : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p4627) ∨ (¬ p4203) ∨ (¬ p4555) ∨ (¬ p3486))
    : p2891 ∨ p2573 ∨ p2406 ∨ (¬ p2493) ∨ (¬ p4555) ∨ (¬ p4203) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4627 := (Or.elim h73676 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70322 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step104621 (p2230 p2406 p2589 p2608 p4630 : Prop)
    (h73678 : p4630 ∨ (¬ p2406))
    (h73284 : p2589 ∨ p2230)
    (h69870 : (¬ p2608) ∨ (¬ p4630) ∨ (¬ p2589))
    : (¬ p2608) ∨ (¬ p2406) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4630 := (Or.elim h73678 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69870 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u4)))))))

theorem step104622 (p2406 p2440 p2737 p2743 p2946 p2952 p4630 p4699 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73678 : p4630 ∨ (¬ p2406))
    (h73298 : p2743 ∨ p2737)
    (h73712 : p4699 ∨ (¬ p2440))
    (h70149 : (¬ p4630) ∨ (¬ p2743) ∨ (¬ p4699) ∨ (¬ p2952))
    : p2946 ∨ (¬ p2406) ∨ p2737 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4630 := (Or.elim h73678 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h70149 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step104623 (p2406 p2493 p2499 p2563 p2573 p2579 p2608 p3212 p4630 p4714 p5046 : Prop)
    (h73678 : p4630 ∨ (¬ p2406))
    (h73274 : p2579 ∨ p2573)
    (h73260 : p2499 ∨ p2493)
    (h73720 : p4714 ∨ p2563)
    (h71045 : (¬ p4630) ∨ (¬ p2608) ∨ (¬ p2499) ∨ (¬ p5046) ∨ (¬ p2579) ∨ (¬ p3212) ∨ (¬ p4714))
    : (¬ p3212) ∨ (¬ p2406) ∨ p2573 ∨ (¬ p2608) ∨ p2493 ∨ (¬ p5046) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4630 := (Or.elim h73678 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u8 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71045 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u10)))))))))))))))

theorem step104625 (p2352 p2501 p3379 p3449 p3860 p4992 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h70845 : (¬ p4992) ∨ (¬ p3860) ∨ (¬ p3379) ∨ (¬ p2501) ∨ (¬ p2352))
    : p3449 ∨ (¬ p2352) ∨ (¬ p2501) ∨ (¬ p4992) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h70845 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step104630 (p2255 p2807 p2891 p2901 p3368 p3486 p4918 p4957 : Prop)
    (h73828 : p4918 ∨ (¬ p2901))
    (h73398 : p3486 ∨ p2891)
    (h70250 : (¬ p4918) ∨ (¬ p4957) ∨ (¬ p2255) ∨ (¬ p3368) ∨ (¬ p2807) ∨ (¬ p3486))
    : (¬ p2901) ∨ (¬ p4957) ∨ (¬ p2807) ∨ (¬ p2255) ∨ p2891 ∨ (¬ p3368) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4918 := (Or.elim h73828 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70250 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step104633 (p2245 p2274 p2563 p2608 p2744 p2992 p3005 p3166 p3172 p4437 p4702 p4973 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h72694 : (¬ p2608) ∨ (¬ p2563) ∨ (¬ p2245) ∨ (¬ p4437) ∨ (¬ p2992) ∨ (¬ p2744) ∨ (¬ p4702) ∨ (¬ p4973) ∨ (¬ p3172) ∨ (¬ p2274) ∨ (¬ p3005))
    : p3166 ∨ (¬ p2245) ∨ (¬ p2563) ∨ (¬ p2608) ∨ (¬ p2274) ∨ (¬ p2744) ∨ (¬ p3005) ∨ (¬ p4973) ∨ (¬ p4702) ∨ (¬ p2992) ∨ (¬ p4437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72694 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (False.elim (r9 u6)))))))))))))))))))))))

theorem step104637 (p2177 p2230 p2274 p2299 p2493 p2589 p2608 p3097 p3379 p4376 p4717 p5189 : Prop)
    (h73948 : p5189 ∨ p3379)
    (h73284 : p2589 ∨ p2230)
    (h73234 : p2299 ∨ p2177)
    (h73352 : p3097 ∨ p2274)
    (h70969 : (¬ p5189) ∨ (¬ p2493) ∨ (¬ p2589) ∨ (¬ p3097) ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p4717) ∨ (¬ p2299))
    : p3379 ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p2493) ∨ p2230 ∨ p2177 ∨ p2274 ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5189 := (Or.elim h73948 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h70969 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step104641 (p2493 p2499 p2608 p3276 p3346 p3379 p4425 p5189 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73948 : p5189 ∨ p3379)
    (h73260 : p2499 ∨ p2493)
    (h71189 : (¬ p2608) ∨ (¬ p4425) ∨ (¬ p2499) ∨ (¬ p3346) ∨ (¬ p5189))
    : p3276 ∨ p3379 ∨ p2493 ∨ (¬ p2608) ∨ (¬ p3346) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p5189 := (Or.elim h73948 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71189 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step104645 (p2177 p2187 p2241 p2245 p2247 p2274 p2363 p2417 p2563 p2598 p2608 p2742 p2744 p3055 p3201 p3876 p4500 p4505 p4639 p4786 : Prop)
    (h73682 : p4639 ∨ (¬ p2417))
    (h73602 : p4500 ∨ p2177)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h73226 : p2247 ∨ p2241)
    (h73606 : p4505 ∨ p2187)
    (h72705 : (¬ p4639) ∨ (¬ p2608) ∨ (¬ p2363) ∨ (¬ p4786) ∨ (¬ p2742) ∨ (¬ p3876) ∨ (¬ p2744) ∨ (¬ p2245) ∨ (¬ p4505) ∨ (¬ p2563) ∨ (¬ p2274) ∨ (¬ p3055) ∨ (¬ p2247) ∨ (¬ p4500))
    : (¬ p2245) ∨ (¬ p2417) ∨ (¬ p2363) ∨ p2177 ∨ p3201 ∨ (¬ p2274) ∨ (¬ p2608) ∨ (¬ p4786) ∨ (¬ p2744) ∨ (¬ p2563) ∨ p2598 ∨ (¬ p2742) ∨ p2241 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : p4639 := (Or.elim h73682 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u15 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u16 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u17 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u18 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    let u19 : p4505 := (Or.elim h73606 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    (Or.elim h72705 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u16))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u19))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u5))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u17))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u18))) (fun r12 => (False.elim (r12 u15)))))))))))))))))))))))))))))

theorem step104646 (p2737 p2743 p3166 p3172 p3256 p3361 p5106 p5284 : Prop)
    (h73922 : p5106 ∨ p3256)
    (h73298 : p2743 ∨ p2737)
    (h73356 : p3172 ∨ p3166)
    (h70757 : (¬ p2743) ∨ (¬ p5284) ∨ (¬ p5106) ∨ (¬ p3361) ∨ (¬ p3172))
    : (¬ p5284) ∨ p3256 ∨ (¬ p3361) ∨ p2737 ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5106 := (Or.elim h73922 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70757 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step104660 (p2274 p2307 p2573 p2583 p2598 p2608 p3097 p3422 p3584 p4728 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73730 : p4728 ∨ (¬ p2598))
    (h73426 : p3584 ∨ p3422)
    (h73278 : p2583 ∨ (¬ p2573))
    (h70927 : (¬ p2583) ∨ (¬ p4728) ∨ (¬ p3584) ∨ (¬ p2608) ∨ (¬ p3097) ∨ (¬ p2307))
    : (¬ p2307) ∨ p2274 ∨ (¬ p2598) ∨ p3422 ∨ (¬ p2608) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4728 := (Or.elim h73730 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u8 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p2583 := (Or.elim h73278 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h70927 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step104665 (p2132 p2142 p2363 p2440 p2563 p2573 p3367 p4602 p4714 p5213 : Prop)
    (h73960 : p5213 ∨ p3367)
    (h73720 : p4714 ∨ p2563)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73218 : p2142 ∨ (¬ p2132))
    (h70517 : (¬ p2142) ∨ (¬ p4602) ∨ (¬ p5213) ∨ (¬ p4714) ∨ (¬ p2573) ∨ (¬ p2440))
    : (¬ p2573) ∨ p3367 ∨ p2563 ∨ (¬ p2363) ∨ (¬ p2440) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5213 := (Or.elim h73960 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u9 : p2142 := (Or.elim h73218 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h70517 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step104668 (p2230 p2553 p2563 p2588 p3389 p4716 : Prop)
    (h73722 : p4716 ∨ (¬ p2563))
    (h73282 : p2588 ∨ p2553)
    (h70200 : (¬ p4716) ∨ p3389 ∨ (¬ p2588) ∨ (¬ p2230))
    : p3389 ∨ (¬ p2563) ∨ p2553 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70200 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step104671 (p2132 p2230 p2440 p2598 p2651 p3367 p4726 p5213 : Prop)
    (h73960 : p5213 ∨ p3367)
    (h73728 : p4726 ∨ p2598)
    (h70513 : (¬ p4726) ∨ (¬ p2132) ∨ (¬ p5213) ∨ (¬ p2651) ∨ (¬ p2230) ∨ (¬ p2440))
    : (¬ p2230) ∨ p3367 ∨ (¬ p2651) ∨ (¬ p2440) ∨ p2598 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5213 := (Or.elim h73960 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4726 := (Or.elim h73728 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70513 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step104678 (p2427 p2553 p2563 p4235 p4716 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73722 : p4716 ∨ (¬ p2563))
    (h71035 : (¬ p4716) ∨ (¬ p4235) ∨ (¬ p2553))
    : p2427 ∨ (¬ p2553) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h71035 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step104686 (p2252 p2331 p2641 p2963 p4758 : Prop)
    (h73746 : p4758 ∨ (¬ p2641))
    (h73338 : p2963 ∨ p2331)
    (h69872 : (¬ p4758) ∨ (¬ p2252) ∨ (¬ p2963))
    : (¬ p2641) ∨ p2331 ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4758 := (Or.elim h73746 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69872 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u4)))))))

theorem step104687 (p2192 p2563 p2922 p4511 p4646 : Prop)
    (h73610 : p4511 ∨ p2192)
    (h70806 : (¬ p4511) ∨ (¬ p2922) ∨ (¬ p4646) ∨ (¬ p2563))
    : (¬ p2922) ∨ p2192 ∨ (¬ p2563) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4511 := (Or.elim h73610 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70806 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step104689 (p2230 p2373 p2417 p2922 p3146 p3379 p5192 : Prop)
    (h73950 : p5192 ∨ (¬ p3379))
    (h70628 : (¬ p5192) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146))
    : (¬ p2417) ∨ (¬ p3146) ∨ (¬ p2373) ∨ (¬ p2922) ∨ (¬ p2230) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5192 := (Or.elim h73950 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h70628 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step104690 (p2230 p2406 p2589 p2727 p2922 p2946 p2952 p2992 p3238 p3475 p3590 p3662 p3879 p4281 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73330 : p2952 ∨ p2946)
    (h73284 : p2589 ∨ p2230)
    (h73374 : p3238 ∨ p2406)
    (h72624 : (¬ p3590) ∨ (¬ p2922) ∨ (¬ p3662) ∨ (¬ p2589) ∨ (¬ p3475) ∨ (¬ p2727) ∨ (¬ p4281) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p3238))
    : p2992 ∨ p2946 ∨ (¬ p2727) ∨ (¬ p3475) ∨ (¬ p4281) ∨ p2230 ∨ p2406 ∨ (¬ p2922) ∨ (¬ p3590) ∨ (¬ p3879) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h72624 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u13)))))))))))))))))))))

theorem step104691 (p2210 p2230 p2255 p2331 p2363 p2406 p2417 p2437 p2440 p2589 p2641 p2761 p2911 p2922 p3238 p3379 p3389 p3631 p3817 p4154 p4278 p4347 p4381 p4582 p4666 p5191 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h73284 : p2589 ∨ p2230)
    (h73546 : p4278 ∨ p2417)
    (h73574 : p4381 ∨ p2761)
    (h73650 : p4582 ∨ (¬ p2331))
    (h73560 : p4347 ∨ p2363)
    (h73374 : p3238 ∨ p2406)
    (h73526 : p4154 ∨ p2641)
    (h70357 : (¬ p4381) ∨ (¬ p4347) ∨ (¬ p3817) ∨ (¬ p4278) ∨ (¬ p4154) ∨ (¬ p4582) ∨ (¬ p3389) ∨ (¬ p5191) ∨ (¬ p4666) ∨ (¬ p2589) ∨ (¬ p3238) ∨ (¬ p3379) ∨ (¬ p2440) ∨ (¬ p2437) ∨ (¬ p2210) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p2255))
    : p3631 ∨ (¬ p2911) ∨ p2230 ∨ (¬ p2255) ∨ p2417 ∨ p2761 ∨ (¬ p2437) ∨ (¬ p2331) ∨ (¬ p4666) ∨ (¬ p2922) ∨ (¬ p3389) ∨ (¬ p3379) ∨ p2363 ∨ p2406 ∨ (¬ p2210) ∨ (¬ p2440) ∨ p2641 ∨ (¬ p5191) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))));
    let u18 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u19 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u20 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u21 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u22 : p4582 := (Or.elim h73650 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u23 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    let u24 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u25 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u16 r0))));
    (Or.elim h70357 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u23))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u18))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u20))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u25))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u22))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u17))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u19))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u24))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u15))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u6))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u14))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u1))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u9))) (fun r16 => (False.elim (r16 u3)))))))))))))))))))))))))))))))))))))

theorem step104692 (p2440 p2459 p2532 p2533 p2563 p2651 p2657 p3146 p3256 p3266 p4110 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73288 : p2657 ∨ p2651)
    (h73516 : p4110 ∨ p2563)
    (h71010 : p2459 ∨ (¬ p4444) ∨ (¬ p2533) ∨ (¬ p2532) ∨ (¬ p3146) ∨ (¬ p3256) ∨ (¬ p4110) ∨ (¬ p2440) ∨ (¬ p2657))
    : p3266 ∨ (¬ p3256) ∨ (¬ p2440) ∨ p2459 ∨ (¬ p3146) ∨ p2651 ∨ (¬ p2532) ∨ p2563 ∨ (¬ p2533) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71010 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u10)))))))))))))))))))

theorem step104694 (p2137 p2220 p2230 p2241 p2245 p2247 p2274 p2440 p2528 p2553 p2589 p2696 p2737 p2747 p2811 p2911 p2960 p2962 p2992 p3146 p3256 p3365 p3367 p3370 p3660 p3662 p3698 p4316 p4521 p4533 p4554 p4560 p4697 p4718 p4923 p4953 p4973 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73226 : p2247 ∨ p2241)
    (h73302 : p2747 ∨ (¬ p2737))
    (h73634 : p4554 ∨ p2274)
    (h73284 : p2589 ∨ p2230)
    (h73390 : p3365 ∨ p2696)
    (h72955 : p4560)
    (h73832 : p4923 ∨ (¬ p2911))
    (h70430 : (¬ p2553) ∨ (¬ p4923) ∨ (¬ p4554) ∨ (¬ p4533) ∨ (¬ p2589) ∨ (¬ p3367) ∨ (¬ p3662) ∨ (¬ p2747) ∨ (¬ p3698) ∨ (¬ p4953) ∨ (¬ p2440) ∨ (¬ p4697) ∨ (¬ p2528) ∨ (¬ p4973) ∨ (¬ p4718) ∨ (¬ p3660) ∨ (¬ p2247) ∨ (¬ p2245) ∨ (¬ p4521) ∨ (¬ p3370) ∨ (¬ p2137) ∨ (¬ p3365) ∨ (¬ p2811) ∨ (¬ p3256) ∨ (¬ p2960) ∨ (¬ p4316) ∨ (¬ p2220) ∨ (¬ p2962) ∨ (¬ p4560) ∨ (¬ p3146))
    : (¬ p3146) ∨ p2992 ∨ p2241 ∨ (¬ p2220) ∨ (¬ p2737) ∨ (¬ p4533) ∨ p2274 ∨ (¬ p3367) ∨ (¬ p4316) ∨ (¬ p3256) ∨ p2230 ∨ (¬ p3698) ∨ (¬ p2440) ∨ (¬ p2962) ∨ (¬ p4718) ∨ (¬ p4697) ∨ (¬ p3660) ∨ (¬ p4973) ∨ (¬ p4521) ∨ (¬ p2553) ∨ (¬ p2528) ∨ (¬ p4953) ∨ (¬ p2811) ∨ (¬ p2245) ∨ (¬ p2960) ∨ (¬ p3370) ∨ p2696 ∨ (¬ p2137) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : p2960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))));
    let u25 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))));
    let u26 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))));
    let u27 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))));
    let u28 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))))))))));
    let u29 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u30 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u31 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u32 : p4554 := (Or.elim h73634 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u33 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u34 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u26 r0))));
    let u35 : p4560 := h72955;
    let u36 : p4923 := (Or.elim h73832 (fun q0 => q0) (fun r0 => (False.elim (r0 u28))));
    (Or.elim h70430 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u36))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u32))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u33))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u29))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u31))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u21))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u12))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u15))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u20))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u17))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u14))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u16))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u30))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u23))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u18))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u25))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u27))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u34))) (fun r21 => (Or.elim r21 (fun q22 => (False.elim (q22 u22))) (fun r22 => (Or.elim r22 (fun q23 => (False.elim (q23 u9))) (fun r23 => (Or.elim r23 (fun q24 => (False.elim (q24 u24))) (fun r24 => (Or.elim r24 (fun q25 => (False.elim (q25 u8))) (fun r25 => (Or.elim r25 (fun q26 => (False.elim (q26 u3))) (fun r26 => (Or.elim r26 (fun q27 => (False.elim (q27 u13))) (fun r27 => (Or.elim r27 (fun q28 => (False.elim (q28 u35))) (fun r28 => (False.elim (r28 u0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem step104702 (p2668 p3166 p3309 p3923 p4757 p4772 : Prop)
    (h73752 : p4772 ∨ (¬ p2668))
    (h69789 : (¬ p3923) ∨ (¬ p4757) ∨ (¬ p3166) ∨ (¬ p3309) ∨ (¬ p4772))
    : (¬ p2668) ∨ (¬ p3309) ∨ (¬ p4757) ∨ (¬ p3166) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4757 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4772 := (Or.elim h73752 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h69789 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step104717 (p2122 p2230 p2274 p2406 p2440 p2493 p2499 p2573 p2579 p2641 p2696 p2742 p2774 p2797 p2911 p3093 p3097 p3309 p3347 p4001 p4564 p4644 p4712 p4715 p4844 p4973 p5143 : Prop)
    (h73938 : p5143 ∨ (¬ p3309))
    (h73788 : p4844 ∨ (¬ p2797))
    (h73260 : p2499 ∨ p2493)
    (h73274 : p2579 ∨ p2573)
    (h73351 : (¬ p2274) ∨ (¬ p3097))
    (h70956 : (¬ p2911) ∨ (¬ p4844) ∨ (¬ p2641) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p4712) ∨ (¬ p4644) ∨ (¬ p4001) ∨ (¬ p2499) ∨ (¬ p4564) ∨ (¬ p2122) ∨ p3097 ∨ (¬ p2742) ∨ (¬ p2406) ∨ (¬ p2774) ∨ (¬ p3347) ∨ (¬ p2230) ∨ (¬ p4973) ∨ (¬ p2696) ∨ (¬ p5143) ∨ (¬ p3093) ∨ (¬ p4715))
    : (¬ p3309) ∨ (¬ p2911) ∨ (¬ p4715) ∨ (¬ p3093) ∨ (¬ p2797) ∨ (¬ p2774) ∨ (¬ p2440) ∨ (¬ p4644) ∨ (¬ p3347) ∨ p2493 ∨ p2573 ∨ (¬ p2274) ∨ (¬ p2122) ∨ (¬ p2742) ∨ (¬ p4712) ∨ (¬ p4564) ∨ (¬ p2641) ∨ (¬ p4973) ∨ (¬ p2230) ∨ (¬ p4001) ∨ (¬ p2406) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))))))));
    let u22 : p5143 := (Or.elim h73938 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u23 : p4844 := (Or.elim h73788 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u24 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u25 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u26 : (¬ p3097) := (Or.elim h73351 (fun q0 => (False.elim (q0 u11))) (fun r0 => r0));
    (Or.elim h70956 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u23))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u16))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u25))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u14))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u19))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u24))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u15))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u12))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (u26 q11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u13))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u20))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u5))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u8))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u18))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u17))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u21))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u22))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u3))) (fun r20 => (False.elim (r20 u2)))))))))))))))))))))))))))))))))))))))))))))

theorem step104745 (p2177 p2299 p2437 p2608 p2829 p3201 p3367 p3585 p3742 p3876 p3921 p4595 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73428 : p3585 ∨ p3367)
    (h73234 : p2299 ∨ p2177)
    (h73485 : (¬ p3201) ∨ (¬ p3876))
    (h70572 : (¬ p3742) ∨ p3876 ∨ (¬ p3921) ∨ (¬ p4595) ∨ (¬ p2829) ∨ (¬ p2299) ∨ (¬ p2608) ∨ (¬ p3585))
    : (¬ p2829) ∨ p2437 ∨ p3367 ∨ p2177 ∨ (¬ p2608) ∨ (¬ p3921) ∨ (¬ p4595) ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4595 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : (¬ p3876) := (Or.elim h73485 (fun q0 => (False.elim (q0 u7))) (fun r0 => r0));
    (Or.elim h70572 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step104746 (p2598 p2737 p2747 p2992 p3367 p3585 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73302 : p2747 ∨ (¬ p2737))
    (h70502 : (¬ p2747) ∨ (¬ p2992) ∨ (¬ p3585) ∨ (¬ p2598))
    : (¬ p2992) ∨ p3367 ∨ (¬ p2598) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h70502 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step104768 (p2255 p2437 p2440 p2727 p3389 p3742 p4111 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73518 : p4111 ∨ p2727)
    (h70975 : (¬ p4111) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p2440) ∨ (¬ p2255))
    : (¬ p3389) ∨ p2437 ∨ p2727 ∨ (¬ p2440) ∨ (¬ p2255) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70975 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step104769 (p2177 p2299 p2437 p2608 p3016 p3367 p3422 p3574 p3742 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73234 : p2299 ∨ p2177)
    (h73452 : p3742 ∨ p2437)
    (h70965 : (¬ p3367) ∨ (¬ p3742) ∨ (¬ p3422) ∨ (¬ p2299) ∨ (¬ p2608) ∨ (¬ p3574))
    : (¬ p3422) ∨ p3016 ∨ (¬ p3367) ∨ p2177 ∨ p2437 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h70965 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step104779 (p2088 p2459 p2761 p3146 p3266 p3692 p3857 p4381 p4455 p4456 p4665 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73447 : (¬ p3146) ∨ (¬ p3692))
    (h73480 : p3857 ∨ p2088)
    (h73696 : p4665 ∨ p2459)
    (h70947 : p3692 ∨ (¬ p3857) ∨ (¬ p4456) ∨ (¬ p4455) ∨ (¬ p3266) ∨ (¬ p4381) ∨ (¬ p4665))
    : p2761 ∨ (¬ p3266) ∨ (¬ p3146) ∨ (¬ p4455) ∨ p2088 ∨ (¬ p4456) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4455 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4456 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : (¬ p3692) := (Or.elim h73447 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u9 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4665 := (Or.elim h73696 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h70947 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u10)))))))))))))))

theorem step104801 (p2284 p2459 p2553 p2696 p2787 p2797 p2839 p2946 p2972 p3105 p3125 p3136 p4315 p4363 p4385 p4516 p4518 p4565 p4665 p4709 p4788 p4870 p4878 p5042 : Prop)
    (h73888 : p5042 ∨ p3125)
    (h73567 : (¬ p2972) ∨ (¬ p4363))
    (h73575 : (¬ p3105) ∨ (¬ p4385))
    (h73550 : p4315 ∨ p3136)
    (h73760 : p4788 ∨ (¬ p2696))
    (h73718 : p4709 ∨ (¬ p2553))
    (h73696 : p4665 ∨ p2459)
    (h73640 : p4565 ∨ (¬ p2284))
    (h70396 : (¬ p4665) ∨ (¬ p4709) ∨ (¬ p2797) ∨ (¬ p5042) ∨ (¬ p2972) ∨ p4363 ∨ p4385 ∨ (¬ p4870) ∨ (¬ p4518) ∨ (¬ p4516) ∨ (¬ p2787) ∨ (¬ p4878) ∨ (¬ p2839) ∨ (¬ p2946) ∨ (¬ p4315) ∨ (¬ p4788) ∨ (¬ p4565))
    : (¬ p2787) ∨ p3125 ∨ (¬ p2972) ∨ (¬ p3105) ∨ p3136 ∨ (¬ p4878) ∨ (¬ p2797) ∨ (¬ p2946) ∨ (¬ p4518) ∨ (¬ p2696) ∨ (¬ p2839) ∨ (¬ p4870) ∨ (¬ p2553) ∨ (¬ p4516) ∨ p2459 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2787 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))));
    let u16 : p5042 := (Or.elim h73888 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u17 : (¬ p4363) := (Or.elim h73567 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u18 : (¬ p4385) := (Or.elim h73575 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    let u19 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u20 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u9))));
    let u21 : p4709 := (Or.elim h73718 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u22 : p4665 := (Or.elim h73696 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    let u23 : p4565 := (Or.elim h73640 (fun q0 => q0) (fun r0 => (False.elim (r0 u15))));
    (Or.elim h70396 (fun q0 => (False.elim (q0 u22))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u21))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u16))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u17 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u18 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u13))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u0))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u5))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u10))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u7))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u19))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u20))) (fun r15 => (False.elim (r15 u23)))))))))))))))))))))))))))))))))))

theorem step104805 (p2190 p2192 p2210 p2274 p2284 p2440 p2598 p3201 p3872 p3952 p4702 p4814 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h70492 : (¬ p2192) ∨ (¬ p3952) ∨ (¬ p2190) ∨ (¬ p2274) ∨ (¬ p3872) ∨ (¬ p2210) ∨ (¬ p4814) ∨ (¬ p4702) ∨ (¬ p2440) ∨ (¬ p3201) ∨ (¬ p2598))
    : (¬ p2190) ∨ (¬ p3201) ∨ (¬ p2192) ∨ (¬ p2598) ∨ (¬ p4814) ∨ (¬ p2274) ∨ (¬ p2210) ∨ p2284 ∨ (¬ p3872) ∨ (¬ p2440) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h70492 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step104829 (p2177 p2437 p2696 p3016 p3201 p3367 p3422 p3742 p3876 p4500 p4788 p4971 p5223 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73858 : p4971 ∨ p3016)
    (h73485 : (¬ p3201) ∨ (¬ p3876))
    (h73760 : p4788 ∨ (¬ p2696))
    (h73966 : p5223 ∨ (¬ p3422))
    (h73602 : p4500 ∨ p2177)
    (h70967 : (¬ p4788) ∨ (¬ p5223) ∨ p3367 ∨ p3876 ∨ (¬ p3742) ∨ (¬ p4971) ∨ (¬ p4500))
    : p2437 ∨ p3016 ∨ (¬ p3201) ∨ (¬ p2696) ∨ (¬ p3422) ∨ p2177 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4971 := (Or.elim h73858 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : (¬ p3876) := (Or.elim h73485 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u10 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u11 : p5223 := (Or.elim h73966 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u12 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70967 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u9 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (False.elim (r5 u12)))))))))))))))

theorem step104834 (p2156 p2274 p2553 p2563 p2696 p2891 p2911 p3486 p4487 p4557 p4709 p4716 p4788 p4923 : Prop)
    (h73596 : p4487 ∨ (¬ p2156))
    (h73398 : p3486 ∨ p2891)
    (h73722 : p4716 ∨ (¬ p2563))
    (h73832 : p4923 ∨ (¬ p2911))
    (h73760 : p4788 ∨ (¬ p2696))
    (h73636 : p4557 ∨ (¬ p2274))
    (h73718 : p4709 ∨ (¬ p2553))
    (h70282 : (¬ p4788) ∨ (¬ p4923) ∨ (¬ p4487) ∨ (¬ p4557) ∨ (¬ p4716) ∨ (¬ p4709) ∨ (¬ p3486))
    : (¬ p2156) ∨ p2891 ∨ (¬ p2563) ∨ (¬ p2911) ∨ (¬ p2696) ∨ (¬ p2274) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4487 := (Or.elim h73596 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u10 : p4923 := (Or.elim h73832 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u11 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u12 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u13 : p4709 := (Or.elim h73718 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    (Or.elim h70282 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (False.elim (r5 u8)))))))))))))))

theorem step104840 (p2156 p2284 p2982 p3506 p3646 p4322 p4705 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73436 : p3646 ∨ p2156)
    (h70610 : (¬ p4322) ∨ (¬ p3506) ∨ (¬ p4705) ∨ (¬ p4948) ∨ (¬ p2284) ∨ (¬ p3646))
    : (¬ p2284) ∨ (¬ p4322) ∨ p2982 ∨ (¬ p3506) ∨ (¬ p4705) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h70610 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step104858 (p2518 p2553 p3309 p3549 p4598 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h69817 : (¬ p3549) ∨ (¬ p4598) ∨ (¬ p2518) ∨ (¬ p2553))
    : (¬ p2518) ∨ (¬ p2553) ∨ (¬ p4598) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69817 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step104861 (p2156 p2192 p2437 p2441 p2881 p2891 p2992 p3051 p3370 p3570 p4173 p4539 p4704 p4958 : Prop)
    (h73852 : p4958 ∨ (¬ p2992))
    (h73046 : p4704)
    (h73528 : p4173 ∨ p2192)
    (h73417 : (¬ p2881) ∨ (¬ p3570))
    (h70294 : (¬ p4958) ∨ (¬ p2437) ∨ (¬ p4539) ∨ (¬ p2441) ∨ (¬ p4704) ∨ (¬ p4173) ∨ p3370 ∨ (¬ p3051) ∨ p3570 ∨ (¬ p2156) ∨ p2891)
    : (¬ p3051) ∨ p3370 ∨ (¬ p2992) ∨ (¬ p2437) ∨ (¬ p4539) ∨ (¬ p2156) ∨ p2192 ∨ p2891 ∨ (¬ p2441) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3370) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4958 := (Or.elim h73852 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u11 : p4704 := h73046;
    let u12 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : (¬ p3570) := (Or.elim h73417 (fun q0 => (False.elim (q0 u9))) (fun r0 => r0));
    (Or.elim h70294 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u13 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (False.elim (u7 r9)))))))))))))))))))))))

theorem step104863 (p2707 p2737 p2829 p3319 p3323 p4026 p4842 p4865 : Prop)
    (h73798 : p4865 ∨ p2829)
    (h73504 : p4026 ∨ p3319)
    (h70679 : (¬ p4865) ∨ (¬ p2707) ∨ (¬ p4026) ∨ (¬ p2737) ∨ (¬ p4842) ∨ (¬ p3323))
    : (¬ p2707) ∨ p2829 ∨ p3319 ∨ (¬ p2737) ∨ (¬ p3323) ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4865 := (Or.elim h73798 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h70679 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step104864 (p2440 p2761 p3193 p3222 p3379 p3506 p4116 p4381 p4953 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73364 : p3222 ∨ p3193)
    (h70241 : (¬ p3222) ∨ (¬ p3506) ∨ (¬ p4381) ∨ (¬ p4953) ∨ (¬ p2440) ∨ (¬ p3379) ∨ (¬ p4116))
    : p2761 ∨ p3193 ∨ (¬ p4953) ∨ (¬ p3506) ∨ (¬ p4116) ∨ (¬ p2440) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h70241 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step104865 (p2727 p2737 p2740 p3193 p3222 p3541 p5160 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73296 : p2740 ∨ p2737)
    (h69919 : (¬ p2740) ∨ (¬ p2727) ∨ (¬ p3222) ∨ (¬ p3541) ∨ (¬ p5160))
    : p3193 ∨ (¬ p5160) ∨ p2737 ∨ (¬ p3541) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2740 := (Or.elim h73296 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69919 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step104873 (p2230 p2252 p2295 p2331 p2363 p2396 p2598 p2668 p2750 p2753 p2963 p2982 p3324 p3362 p3422 p3568 p4107 p4322 p4332 p4347 p4395 p4450 p4789 p4951 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73386 : p3324 ∨ p2668)
    (h73514 : p4107 ∨ p2396)
    (h73848 : p4951 ∨ (¬ p2982))
    (h73338 : p2963 ∨ p2331)
    (h73416 : p3568 ∨ p2295)
    (h70661 : (¬ p4951) ∨ (¬ p4107) ∨ (¬ p4322) ∨ (¬ p2230) ∨ (¬ p3422) ∨ (¬ p2598) ∨ (¬ p3362) ∨ (¬ p2252) ∨ (¬ p4395) ∨ (¬ p4332) ∨ (¬ p4450) ∨ (¬ p2963) ∨ (¬ p4347) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p4789) ∨ (¬ p3324) ∨ (¬ p3568))
    : (¬ p4322) ∨ (¬ p4332) ∨ p2363 ∨ (¬ p3422) ∨ p2668 ∨ (¬ p2230) ∨ (¬ p2753) ∨ (¬ p2252) ∨ p2396 ∨ (¬ p2598) ∨ (¬ p4450) ∨ (¬ p4395) ∨ (¬ p3362) ∨ (¬ p2750) ∨ (¬ p2982) ∨ (¬ p4789) ∨ p2331 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))));
    let u18 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u19 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u20 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u21 : p4951 := (Or.elim h73848 (fun q0 => q0) (fun r0 => (False.elim (r0 u14))));
    let u22 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u16 r0))));
    let u23 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u17 r0))));
    (Or.elim h70661 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u20))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u22))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u18))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u13))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u6))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u15))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u19))) (fun r16 => (False.elim (r16 u23)))))))))))))))))))))))))))))))))))))

theorem step104886 (p2187 p2307 p2313 p2363 p2507 p2696 p2881 p2911 p3093 p3115 p3136 p3156 p3449 p3570 p3581 p3591 p3644 p3860 p3989 p4347 p4450 p4518 p4556 p4733 p4902 p5015 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73502 : p3989 ∨ p2187)
    (h73434 : p3644 ∨ p2911)
    (h73418 : p3570 ∨ p2881)
    (h73432 : p3591 ∨ p3093)
    (h73238 : p2313 ∨ p2307)
    (h73482 : p3860 ∨ p3449)
    (h69887 : (¬ p4347) ∨ (¬ p3860) ∨ (¬ p3115) ∨ (¬ p3156) ∨ (¬ p3989) ∨ (¬ p4450) ∨ (¬ p2507) ∨ (¬ p4902) ∨ (¬ p3570) ∨ (¬ p2313) ∨ (¬ p3644) ∨ (¬ p3581) ∨ (¬ p4556) ∨ (¬ p3591) ∨ (¬ p5015) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p4733) ∨ (¬ p4518))
    : (¬ p3156) ∨ p2363 ∨ (¬ p4518) ∨ (¬ p2696) ∨ (¬ p4733) ∨ p2187 ∨ p2911 ∨ p2881 ∨ (¬ p5015) ∨ p3093 ∨ (¬ p3115) ∨ (¬ p4450) ∨ (¬ p4556) ∨ (¬ p2507) ∨ (¬ p3581) ∨ p2307 ∨ p3449 ∨ (¬ p4902) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))));
    let u19 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u20 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u21 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u22 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u23 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u24 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u15 r0))));
    let u25 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u16 r0))));
    (Or.elim h69887 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u25))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u20))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u17))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u22))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u24))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u21))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u14))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u12))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u23))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u8))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u3))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u18))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u4))) (fun r17 => (False.elim (r17 u2)))))))))))))))))))))))))))))))))))))))

theorem step104912 (p2132 p2138 p2727 p2992 p3136 p4111 p5048 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73892 : p5048 ∨ p3136)
    (h73518 : p4111 ∨ p2727)
    (h72722 : (¬ p2992) ∨ (¬ p5048) ∨ (¬ p4111) ∨ (¬ p2138))
    : (¬ p2992) ∨ p2132 ∨ p3136 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p5048 := (Or.elim h73892 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72722 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step104920 (p2563 p2982 p3564 p3660 p4192 p4555 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h72730 : (¬ p4948) ∨ (¬ p4192) ∨ (¬ p4555) ∨ (¬ p3564) ∨ (¬ p2563) ∨ (¬ p3660))
    : (¬ p3564) ∨ p2982 ∨ (¬ p4555) ∨ (¬ p4192) ∨ (¬ p2563) ∨ (¬ p3660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h72730 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step104921 (p2363 p2528 p2563 p3323 p4037 p4600 p4716 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73660 : p4600 ∨ p2363)
    (h73722 : p4716 ∨ (¬ p2563))
    (h72731 : (¬ p4600) ∨ (¬ p2528) ∨ (¬ p4037) ∨ (¬ p4716))
    : p3323 ∨ (¬ p2528) ∨ p2363 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4600 := (Or.elim h73660 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h72731 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step104924 (p2427 p2440 p3016 p3574 p4235 p4555 : Prop)
    (h73421 : (¬ p3016) ∨ (¬ p3574))
    (h73536 : p4235 ∨ p2427)
    (h72738 : p3574 ∨ (¬ p2440) ∨ (¬ p4555) ∨ (¬ p4235))
    : (¬ p3016) ∨ (¬ p2440) ∨ (¬ p4555) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3574) := (Or.elim h73421 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72738 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step104931 (p2274 p2341 p2363 p2437 p2459 p2563 p2630 p2651 p2665 p2696 p2737 p3097 p3564 p3683 p4030 p4137 p4203 p4281 p4555 p4589 p4602 p4649 p4667 p4717 p4785 p4814 : Prop)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73698 : p4667 ∨ (¬ p2459))
    (h73758 : p4785 ∨ p2696)
    (h73688 : p4649 ∨ p2437)
    (h73352 : p3097 ∨ p2274)
    (h73654 : p4589 ∨ (¬ p2341))
    (h73524 : p4137 ∨ p3564)
    (h72747 : (¬ p4649) ∨ (¬ p4030) ∨ (¬ p2630) ∨ (¬ p3683) ∨ (¬ p4814) ∨ (¬ p4281) ∨ (¬ p2665) ∨ (¬ p2651) ∨ (¬ p3097) ∨ (¬ p4717) ∨ (¬ p2563) ∨ (¬ p4203) ∨ (¬ p4785) ∨ (¬ p4602) ∨ (¬ p4589) ∨ (¬ p2737) ∨ (¬ p4667) ∨ (¬ p4555) ∨ (¬ p4137))
    : (¬ p4030) ∨ (¬ p2563) ∨ (¬ p2630) ∨ (¬ p3683) ∨ (¬ p4814) ∨ (¬ p2363) ∨ (¬ p2737) ∨ (¬ p4281) ∨ (¬ p2651) ∨ (¬ p4717) ∨ (¬ p2665) ∨ (¬ p2459) ∨ p2696 ∨ p2437 ∨ p2274 ∨ (¬ p4203) ∨ (¬ p2341) ∨ (¬ p4555) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4030 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))));
    let u19 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u20 : p4667 := (Or.elim h73698 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    let u21 : p4785 := (Or.elim h73758 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    let u22 : p4649 := (Or.elim h73688 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u23 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    let u24 : p4589 := (Or.elim h73654 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    let u25 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u18 r0))));
    (Or.elim h72747 (fun q0 => (False.elim (q0 u22))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u23))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u1))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u15))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u21))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u19))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u24))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u6))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u20))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u17))) (fun r17 => (False.elim (r17 u25)))))))))))))))))))))))))))))))))))))))

theorem step104942 (p2210 p2696 p2737 p3365 p4877 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h72759 : (¬ p3365) ∨ (¬ p2210) ∨ (¬ p4877) ∨ (¬ p2737))
    : (¬ p2737) ∨ p2696 ∨ (¬ p4877) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h72759 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step104952 (p2363 p2459 p2641 p2668 p2797 p3324 p4154 p4195 p4347 p4790 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73560 : p4347 ∨ p2363)
    (h73526 : p4154 ∨ p2641)
    (h73386 : p3324 ∨ p2668)
    (h72769 : (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4195) ∨ (¬ p4790) ∨ (¬ p4347) ∨ (¬ p2459))
    : p2797 ∨ p2363 ∨ p2641 ∨ (¬ p2459) ∨ (¬ p4790) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h72769 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step104953 (p3323 p3567 p3654 p4037 p5382 : Prop)
    (h74022 : p5382 ∨ (¬ p3654))
    (h73508 : p4037 ∨ p3323)
    (h72770 : (¬ p5382) ∨ (¬ p3567) ∨ (¬ p4037))
    : (¬ p3654) ∨ (¬ p3567) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p5382 := (Or.elim h74022 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u4 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72770 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step104958 (p2187 p2363 p2383 p2406 p2440 p2459 p2528 p2534 p2608 p2737 p3204 p3238 p3660 p4203 p4347 p4505 p4612 p4699 p4717 p4718 p4735 p4882 p5021 p5193 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73668 : p4612 ∨ p2383)
    (h73374 : p3238 ∨ p2406)
    (h73606 : p4505 ∨ p2187)
    (h73734 : p4735 ∨ (¬ p2608))
    (h73268 : p2534 ∨ p2528)
    (h73712 : p4699 ∨ (¬ p2440))
    (h72777 : (¬ p4699) ∨ (¬ p5021) ∨ (¬ p3204) ∨ (¬ p5193) ∨ (¬ p3238) ∨ (¬ p2534) ∨ (¬ p4718) ∨ (¬ p4717) ∨ (¬ p3660) ∨ (¬ p4203) ∨ (¬ p4735) ∨ (¬ p4612) ∨ (¬ p4505) ∨ (¬ p2737) ∨ (¬ p4347) ∨ (¬ p2459) ∨ (¬ p4882))
    : p2363 ∨ p2383 ∨ (¬ p3204) ∨ (¬ p5193) ∨ p2406 ∨ (¬ p4882) ∨ (¬ p4718) ∨ (¬ p4717) ∨ (¬ p3660) ∨ (¬ p4203) ∨ (¬ p5021) ∨ p2187 ∨ (¬ p2608) ∨ p2528 ∨ (¬ p2737) ∨ (¬ p2459) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))));
    let u17 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u18 : p4612 := (Or.elim h73668 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u19 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u20 : p4505 := (Or.elim h73606 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u21 : p4735 := (Or.elim h73734 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u22 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u23 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    (Or.elim h72777 (fun q0 => (False.elim (q0 u23))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u19))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u22))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u21))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u18))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u20))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u14))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u17))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u15))) (fun r15 => (False.elim (r15 u5)))))))))))))))))))))))))))))))))))

theorem step104959 (p2187 p2210 p2363 p2383 p2459 p2737 p2850 p3323 p4037 p4347 p4612 p4880 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73560 : p4347 ∨ p2363)
    (h73806 : p4880 ∨ p2850)
    (h73668 : p4612 ∨ p2383)
    (h72781 : (¬ p4612) ∨ p2187 ∨ (¬ p2210) ∨ (¬ p2737) ∨ (¬ p4347) ∨ (¬ p2459) ∨ (¬ p4880) ∨ (¬ p4037))
    : p3323 ∨ p2363 ∨ p2850 ∨ (¬ p2210) ∨ (¬ p2459) ∨ p2383 ∨ p2187 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4880 := (Or.elim h73806 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4612 := (Or.elim h73668 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h72781 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step104961 (p2187 p2363 p2373 p2459 p2563 p3323 p4037 p4347 p4508 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73560 : p4347 ∨ p2363)
    (h73608 : p4508 ∨ (¬ p2187))
    (h72783 : (¬ p4508) ∨ (¬ p2373) ∨ (¬ p4037) ∨ (¬ p2563) ∨ (¬ p4347) ∨ (¬ p2459))
    : p3323 ∨ p2363 ∨ (¬ p2459) ∨ (¬ p2563) ∨ (¬ p2373) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4508 := (Or.elim h73608 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h72783 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step104963 (p2187 p2383 p2608 p3093 p3954 p3989 p4870 p5020 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73502 : p3989 ∨ p2187)
    (h72785 : (¬ p3954) ∨ (¬ p5020) ∨ (¬ p3093) ∨ (¬ p4870) ∨ (¬ p2383) ∨ (¬ p3989))
    : (¬ p2383) ∨ p2608 ∨ (¬ p3093) ∨ (¬ p5020) ∨ (¬ p4870) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h72785 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step104970 (p2136 p2274 p2341 p2459 p2608 p2737 p2743 p2778 p2779 p2819 p3097 p3256 p3439 p3954 p4118 p4280 p4311 p4401 p4417 p4518 p4586 p4898 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73352 : p3097 ∨ p2274)
    (h73520 : p4118 ∨ p3256)
    (h73652 : p4586 ∨ p2341)
    (h73298 : p2743 ∨ p2737)
    (h72792 : (¬ p4118) ∨ (¬ p2779) ∨ (¬ p2778) ∨ (¬ p3439) ∨ (¬ p4898) ∨ (¬ p2136) ∨ (¬ p4401) ∨ (¬ p4280) ∨ (¬ p4518) ∨ (¬ p3097) ∨ (¬ p2819) ∨ (¬ p2743) ∨ (¬ p3954) ∨ (¬ p4586) ∨ (¬ p4311) ∨ (¬ p4417) ∨ (¬ p2459))
    : (¬ p4417) ∨ p2608 ∨ (¬ p4311) ∨ (¬ p2778) ∨ (¬ p4898) ∨ (¬ p2779) ∨ (¬ p4401) ∨ (¬ p4280) ∨ (¬ p4518) ∨ p2274 ∨ (¬ p2136) ∨ p3256 ∨ (¬ p2459) ∨ p2341 ∨ (¬ p3439) ∨ (¬ p2819) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4898 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3439 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))));
    let u17 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u18 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u19 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u20 : p4586 := (Or.elim h73652 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u21 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u16 r0))));
    (Or.elim h72792 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u18))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u15))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u21))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u17))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u20))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u2))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u0))) (fun r15 => (False.elim (r15 u12)))))))))))))))))))))))))))))))))))

theorem step104971 (p2187 p2249 p2341 p2459 p2528 p2534 p2608 p2641 p2668 p2696 p2737 p2742 p2743 p3365 p3954 p3989 p4154 p4311 p4586 p4790 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73390 : p3365 ∨ p2696)
    (h73525 : (¬ p2641) ∨ (¬ p4154))
    (h73652 : p4586 ∨ p2341)
    (h73502 : p3989 ∨ p2187)
    (h73298 : p2743 ∨ p2737)
    (h73498 : p3954 ∨ p2608)
    (h72793 : p4154 ∨ (¬ p4790) ∨ (¬ p3365) ∨ (¬ p2249) ∨ (¬ p2743) ∨ (¬ p2742) ∨ (¬ p3954) ∨ (¬ p4586) ∨ (¬ p4311) ∨ (¬ p2668) ∨ (¬ p2534) ∨ (¬ p3989) ∨ (¬ p2459))
    : (¬ p2668) ∨ p2528 ∨ p2696 ∨ (¬ p2641) ∨ p2341 ∨ (¬ p4311) ∨ (¬ p2249) ∨ (¬ p2742) ∨ p2187 ∨ p2737 ∨ p2608 ∨ (¬ p4790) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u14 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u15 : (¬ p4154) := (Or.elim h73525 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    let u16 : p4586 := (Or.elim h73652 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u17 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u18 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u19 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h72793 (fun q0 => (False.elim (u15 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u18))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u19))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u16))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u13))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u17))) (fun r11 => (False.elim (r11 u12)))))))))))))))))))))))))))

theorem step104978 (p2307 p2553 p2588 p2598 p2774 p2784 p3055 p4749 p4841 : Prop)
    (h73312 : p2784 ∨ (¬ p2774))
    (h73282 : p2588 ∨ p2553)
    (h73350 : p3055 ∨ p2598)
    (h72800 : (¬ p2784) ∨ (¬ p3055) ∨ (¬ p2588) ∨ (¬ p2307) ∨ (¬ p4749) ∨ (¬ p4841))
    : (¬ p2774) ∨ (¬ p4841) ∨ p2553 ∨ (¬ p2307) ∨ (¬ p4749) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2784 := (Or.elim h73312 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h72800 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step104981 (p2088 p2363 p2373 p2459 p2696 p2717 p2850 p3146 p3367 p3425 p3659 p4602 p4667 p4749 p4788 p5213 : Prop)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73438 : p3659 ∨ p2717)
    (h73960 : p5213 ∨ p3367)
    (h73698 : p4667 ∨ (¬ p2459))
    (h73760 : p4788 ∨ (¬ p2696))
    (h72803 : (¬ p4788) ∨ (¬ p5213) ∨ (¬ p3146) ∨ (¬ p2088) ∨ (¬ p4602) ∨ (¬ p3659) ∨ (¬ p2850) ∨ (¬ p2373) ∨ (¬ p4667) ∨ (¬ p3425) ∨ (¬ p4749))
    : (¬ p2373) ∨ (¬ p3425) ∨ (¬ p3146) ∨ (¬ p2088) ∨ (¬ p2363) ∨ p2717 ∨ (¬ p2850) ∨ p3367 ∨ (¬ p2459) ∨ (¬ p2696) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u12 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p5213 := (Or.elim h73960 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u14 : p4667 := (Or.elim h73698 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u15 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u9))));
    (Or.elim h72803 (fun q0 => (False.elim (q0 u15))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u14))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step104983 (p2187 p2274 p2295 p2307 p2373 p2668 p3097 p3880 p4489 p4560 : Prop)
    (h72955 : p4560)
    (h73352 : p3097 ∨ p2274)
    (h73490 : p3880 ∨ p2373)
    (h72805 : (¬ p3097) ∨ (¬ p4489) ∨ (¬ p4560) ∨ p2187 ∨ (¬ p2668) ∨ (¬ p2295) ∨ (¬ p2307) ∨ (¬ p3880))
    : (¬ p2668) ∨ (¬ p2295) ∨ (¬ p4489) ∨ p2187 ∨ p2274 ∨ p2373 ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4489 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4560 := h72955;
    let u8 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h72805 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step104984 (p2187 p2295 p2307 p2331 p2373 p2553 p2588 p2668 p3880 p3989 p4705 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h73282 : p2588 ∨ p2553)
    (h73490 : p3880 ∨ p2373)
    (h72806 : (¬ p3989) ∨ (¬ p2668) ∨ (¬ p2295) ∨ p2331 ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p4705) ∨ (¬ p3880))
    : p2331 ∨ (¬ p2668) ∨ p2187 ∨ p2553 ∨ p2373 ∨ (¬ p2295) ∨ (¬ p2307) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h72806 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step104986 (p2187 p2274 p2553 p2588 p2901 p3097 p3989 p4705 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73351 : (¬ p2274) ∨ (¬ p3097))
    (h73502 : p3989 ∨ p2187)
    (h72808 : p3097 ∨ (¬ p2901) ∨ (¬ p3989) ∨ (¬ p2588) ∨ (¬ p4705))
    : p2553 ∨ (¬ p2274) ∨ (¬ p2901) ∨ p2187 ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : (¬ p3097) := (Or.elim h73351 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72808 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step104995 (p2608 p2630 p2651 p2657 p2744 p2745 p3379 p3452 p4116 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73288 : p2657 ∨ p2651)
    (h72817 : (¬ p2630) ∨ (¬ p4116) ∨ (¬ p2657) ∨ (¬ p2745) ∨ (¬ p2744) ∨ (¬ p2608) ∨ (¬ p3452))
    : p3379 ∨ (¬ p2608) ∨ (¬ p2630) ∨ p2651 ∨ (¬ p2744) ∨ (¬ p2745) ∨ (¬ p4116) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72817 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u7)))))))))))))))

theorem step104998 (p2166 p2177 p2192 p2274 p3097 p3399 p3449 p3860 p4491 p4500 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73352 : p3097 ∨ p2274)
    (h73602 : p4500 ∨ p2177)
    (h73598 : p4491 ∨ p2166)
    (h72820 : (¬ p4491) ∨ (¬ p2192) ∨ (¬ p3860) ∨ (¬ p4500) ∨ (¬ p3399) ∨ (¬ p3097))
    : p3449 ∨ (¬ p3399) ∨ p2274 ∨ p2177 ∨ (¬ p2192) ∨ p2166 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4491 := (Or.elim h73598 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h72820 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step105000 (p2230 p2470 p2476 p2608 p3093 p3379 p3641 p4210 p4608 p4632 p5189 : Prop)
    (h73948 : p5189 ∨ p3379)
    (h73250 : p2476 ∨ p2470)
    (h72822 : (¬ p2476) ∨ (¬ p4608) ∨ (¬ p3641) ∨ (¬ p2230) ∨ (¬ p4632) ∨ (¬ p4210) ∨ (¬ p3093) ∨ (¬ p2608) ∨ (¬ p5189))
    : (¬ p4210) ∨ (¬ p3093) ∨ (¬ p3641) ∨ (¬ p4608) ∨ p3379 ∨ (¬ p4632) ∨ p2470 ∨ (¬ p2230) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5189 := (Or.elim h73948 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h72822 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step105003 (p2241 p2992 p3379 p4704 p5189 : Prop)
    (h73046 : p4704)
    (h73948 : p5189 ∨ p3379)
    (h72825 : (¬ p2241) ∨ (¬ p2992) ∨ (¬ p4704) ∨ (¬ p5189))
    : (¬ p2241) ∨ (¬ p2992) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4704 := h73046;
    let u4 : p5189 := (Or.elim h73948 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72825 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step105009 (p2145 p2156 p2177 p2187 p2299 p2307 p2313 p2630 p2696 p2787 p3083 p3646 p3989 p4420 p4596 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73238 : p2313 ∨ p2307)
    (h73234 : p2299 ∨ p2177)
    (h73502 : p3989 ∨ p2187)
    (h72831 : (¬ p2630) ∨ (¬ p3646) ∨ (¬ p2313) ∨ (¬ p2696) ∨ (¬ p2145) ∨ (¬ p3989) ∨ (¬ p4596) ∨ (¬ p3083) ∨ (¬ p4420) ∨ (¬ p2787) ∨ (¬ p2299))
    : (¬ p3083) ∨ (¬ p2787) ∨ p2156 ∨ p2307 ∨ p2177 ∨ p2187 ∨ (¬ p4596) ∨ (¬ p2145) ∨ (¬ p2696) ∨ (¬ p4420) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u14 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h72831 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u14))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (False.elim (r9 u13)))))))))))))))))))))))

theorem step105019 (p2210 p2459 p3146 p3449 p3692 p3860 p3906 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73448 : p3692 ∨ p3146)
    (h72841 : (¬ p2459) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p3692) ∨ (¬ p2210))
    : p3449 ∨ p3146 ∨ (¬ p2459) ∨ (¬ p3906) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h72841 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step105026 (p2187 p2331 p2797 p3005 p3877 p4584 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h72848 : (¬ p2187) ∨ (¬ p4584) ∨ (¬ p2331) ∨ (¬ p2797) ∨ (¬ p3877))
    : p3005 ∨ (¬ p2331) ∨ (¬ p2797) ∨ (¬ p4584) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72848 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step105037 (p2166 p2187 p2191 p2352 p2563 p4243 p4505 p4716 p4882 : Prop)
    (h73606 : p4505 ∨ p2187)
    (h73222 : p2191 ∨ p2166)
    (h73722 : p4716 ∨ (¬ p2563))
    (h72859 : (¬ p4505) ∨ (¬ p2352) ∨ (¬ p4243) ∨ (¬ p4882) ∨ (¬ p2191) ∨ (¬ p4716))
    : (¬ p4243) ∨ (¬ p2352) ∨ p2187 ∨ (¬ p4882) ∨ p2166 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4243 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4505 := (Or.elim h73606 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h72859 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u8)))))))))))))

theorem step105045 (p2241 p2253 p2608 p2946 p2992 p3662 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73440 : p3662 ∨ p2992)
    (h72867 : (¬ p3954) ∨ (¬ p2241) ∨ (¬ p2253) ∨ (¬ p3662) ∨ (¬ p2946))
    : p2608 ∨ p2992 ∨ (¬ p2946) ∨ (¬ p2253) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h72867 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step105049 (p2651 p2696 p2727 p2737 p2743 p4111 p4788 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73298 : p2743 ∨ p2737)
    (h73760 : p4788 ∨ (¬ p2696))
    (h72872 : (¬ p4788) ∨ (¬ p2651) ∨ (¬ p4111) ∨ (¬ p2743))
    : p2727 ∨ p2737 ∨ (¬ p2651) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h72872 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step105051 (p2440 p2641 p2727 p4111 p4717 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h72874 : (¬ p2641) ∨ (¬ p2440) ∨ (¬ p4717) ∨ (¬ p4111))
    : p2727 ∨ (¬ p2641) ∨ (¬ p4717) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72874 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step105054 (p2230 p2493 p2563 p2589 p2982 p3347 p4716 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73284 : p2589 ∨ p2230)
    (h73722 : p4716 ∨ (¬ p2563))
    (h72877 : (¬ p4948) ∨ (¬ p2493) ∨ (¬ p2589) ∨ (¬ p3347) ∨ (¬ p4716))
    : p2982 ∨ (¬ p3347) ∨ p2230 ∨ (¬ p2563) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h72877 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step105057 (p2166 p2187 p2210 p2255 p2274 p2307 p2493 p2553 p2641 p2667 p2745 p2774 p2780 p3146 p3166 p3692 p3941 p3987 p4154 p4426 p4505 p4560 p4736 p5122 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73448 : p3692 ∨ p3146)
    (h73606 : p4505 ∨ p2187)
    (h73526 : p4154 ∨ p2641)
    (h72955 : p4560)
    (h72880 : (¬ p4505) ∨ (¬ p3941) ∨ (¬ p3692) ∨ (¬ p5122) ∨ (¬ p2274) ∨ (¬ p2553) ∨ (¬ p2307) ∨ (¬ p2745) ∨ (¬ p4736) ∨ (¬ p4426) ∨ (¬ p2210) ∨ (¬ p2255) ∨ (¬ p3987) ∨ (¬ p2667) ∨ (¬ p3166) ∨ (¬ p2780) ∨ (¬ p4154) ∨ (¬ p4560) ∨ (¬ p2166) ∨ (¬ p2493))
    : (¬ p2553) ∨ (¬ p2307) ∨ p2774 ∨ (¬ p3987) ∨ (¬ p3166) ∨ (¬ p5122) ∨ (¬ p2274) ∨ (¬ p2745) ∨ (¬ p4736) ∨ p3146 ∨ (¬ p4426) ∨ (¬ p2255) ∨ (¬ p2210) ∨ (¬ p2667) ∨ p2187 ∨ (¬ p3941) ∨ p2641 ∨ (¬ p2166) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))));
    let u19 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u20 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u21 : p4505 := (Or.elim h73606 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    let u22 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u16 r0))));
    let u23 : p4560 := h72955;
    (Or.elim h72880 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u15))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u20))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u12))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u3))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u13))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u4))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u19))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u22))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u23))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u17))) (fun r18 => (False.elim (r18 u18)))))))))))))))))))))))))))))))))))))))))

theorem step105069 (p2166 p2210 p2254 p2274 p2307 p2331 p2363 p2373 p2668 p2774 p2780 p2850 p2963 p2972 p3324 p3684 p3986 p4347 p4375 p4620 p4702 p4736 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73338 : p2963 ∨ p2331)
    (h73308 : p2780 ∨ p2774)
    (h73386 : p3324 ∨ p2668)
    (h73442 : p3684 ∨ p2850)
    (h72892 : (¬ p3324) ∨ (¬ p2963) ∨ (¬ p4347) ∨ (¬ p2972) ∨ (¬ p4620) ∨ (¬ p2210) ∨ (¬ p2780) ∨ (¬ p2254) ∨ (¬ p4375) ∨ (¬ p3986) ∨ (¬ p4702) ∨ (¬ p3684) ∨ (¬ p2307) ∨ (¬ p2373) ∨ (¬ p2166) ∨ (¬ p4736) ∨ (¬ p2274))
    : (¬ p2307) ∨ (¬ p2274) ∨ p2363 ∨ p2331 ∨ (¬ p4620) ∨ (¬ p2210) ∨ p2774 ∨ (¬ p2254) ∨ (¬ p4375) ∨ (¬ p3986) ∨ (¬ p4702) ∨ p2668 ∨ p2850 ∨ (¬ p2373) ∨ (¬ p2166) ∨ (¬ p4736) ∨ (¬ p2972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))));
    let u17 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u18 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u19 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u20 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u21 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    (Or.elim h72892 (fun q0 => (False.elim (q0 u20))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u18))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u17))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u16))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u19))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u21))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u0))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u13))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u14))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u15))) (fun r15 => (False.elim (r15 u1)))))))))))))))))))))))))))))))))))

theorem step105077 (p2230 p2406 p2440 p2493 p2542 p2553 p2589 p3238 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h73374 : p3238 ∨ p2406)
    (h72900 : (¬ p2542) ∨ (¬ p2553) ∨ (¬ p3238) ∨ (¬ p2493) ∨ (¬ p2589))
    : (¬ p2553) ∨ p2440 ∨ p2230 ∨ (¬ p2493) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h72900 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step105078 (p2493 p2573 p2579 p2608 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h72901 : (¬ p2608) ∨ (¬ p2579) ∨ (¬ p2493))
    : p2573 ∨ (¬ p2608) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72901 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step105082 (p2493 p2737 p2743 p3016 p3367 p3574 p4752 p5215 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73962 : p5215 ∨ (¬ p3367))
    (h73422 : p3574 ∨ p3016)
    (h72905 : (¬ p5215) ∨ (¬ p3574) ∨ (¬ p4752) ∨ (¬ p2743) ∨ (¬ p2493))
    : p2737 ∨ (¬ p3367) ∨ (¬ p2493) ∨ (¬ p4752) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p5215 := (Or.elim h73962 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h72905 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step105083 (p2274 p2363 p2373 p2459 p2563 p3323 p4037 p4347 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73560 : p4347 ∨ p2363)
    (h72906 : (¬ p4347) ∨ (¬ p2459) ∨ (¬ p4037) ∨ (¬ p2373) ∨ (¬ p2563) ∨ (¬ p2274))
    : p3323 ∨ (¬ p2274) ∨ (¬ p2373) ∨ p2363 ∨ (¬ p2563) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72906 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step105091 (p2187 p2274 p2284 p2363 p2459 p2493 p2563 p2630 p2946 p2956 p2992 p3422 p4508 p4557 p4600 p4646 p4751 : Prop)
    (h73660 : p4600 ∨ p2363)
    (h73636 : p4557 ∨ (¬ p2274))
    (h73334 : p2956 ∨ (¬ p2946))
    (h73742 : p4751 ∨ (¬ p2630))
    (h73608 : p4508 ∨ (¬ p2187))
    (h72915 : (¬ p2992) ∨ (¬ p2956) ∨ (¬ p3422) ∨ (¬ p4751) ∨ (¬ p2493) ∨ (¬ p2563) ∨ (¬ p4646) ∨ (¬ p2459) ∨ (¬ p4508) ∨ (¬ p4600) ∨ (¬ p4557) ∨ (¬ p2284))
    : p2363 ∨ (¬ p2274) ∨ (¬ p2946) ∨ (¬ p2630) ∨ (¬ p2992) ∨ (¬ p3422) ∨ (¬ p4646) ∨ (¬ p2493) ∨ (¬ p2459) ∨ (¬ p2563) ∨ (¬ p2187) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4600 := (Or.elim h73660 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u14 : p2956 := (Or.elim h73334 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u15 : p4751 := (Or.elim h73742 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u16 : p4508 := (Or.elim h73608 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    (Or.elim h72915 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u15))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u16))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u13))) (fun r10 => (False.elim (r10 u11)))))))))))))))))))))))))

theorem step105093 (p2192 p2210 p2241 p2251 p2274 p2363 p2427 p2437 p2493 p2608 p2641 p2651 p2667 p2696 p2737 p2797 p2901 p2922 p3590 p3919 p4154 p4347 p4645 p4651 p4717 p4736 p4785 p4844 : Prop)
    (h73686 : p4645 ∨ (¬ p2427))
    (h73758 : p4785 ∨ p2696)
    (h73788 : p4844 ∨ (¬ p2797))
    (h73560 : p4347 ∨ p2363)
    (h73690 : p4651 ∨ (¬ p2437))
    (h73526 : p4154 ∨ p2641)
    (h73230 : p2251 ∨ (¬ p2241))
    (h72917 : (¬ p4645) ∨ (¬ p4785) ∨ (¬ p3590) ∨ p2737 ∨ (¬ p4844) ∨ (¬ p4651) ∨ (¬ p2922) ∨ (¬ p4717) ∨ (¬ p3919) ∨ (¬ p4347) ∨ (¬ p2493) ∨ (¬ p2192) ∨ (¬ p4736) ∨ (¬ p2608) ∨ (¬ p4154) ∨ (¬ p2210) ∨ (¬ p2251) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (¬ p2901) ∨ (¬ p2274))
    : (¬ p2901) ∨ (¬ p2651) ∨ (¬ p2427) ∨ p2696 ∨ p2737 ∨ (¬ p2797) ∨ (¬ p3590) ∨ (¬ p4717) ∨ (¬ p3919) ∨ p2363 ∨ (¬ p2493) ∨ (¬ p2437) ∨ (¬ p2922) ∨ (¬ p2608) ∨ (¬ p4736) ∨ p2641 ∨ (¬ p2241) ∨ (¬ p2192) ∨ (¬ p2667) ∨ (¬ p2210) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))));
    let u21 : p4645 := (Or.elim h73686 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u22 : p4785 := (Or.elim h73758 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u23 : p4844 := (Or.elim h73788 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u24 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u25 : p4651 := (Or.elim h73690 (fun q0 => q0) (fun r0 => (False.elim (r0 u11))));
    let u26 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u15 r0))));
    let u27 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u16))));
    (Or.elim h72917 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u22))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u23))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u25))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u24))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u17))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u14))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u13))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u26))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u19))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u27))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u1))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u18))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u0))) (fun r19 => (False.elim (r19 u20)))))))))))))))))))))))))))))))))))))))))))

theorem step105098 (p2274 p2284 p2608 p2696 p2946 p4788 : Prop)
    (h73760 : p4788 ∨ (¬ p2696))
    (h72922 : (¬ p4788) ∨ (¬ p2274) ∨ (¬ p2608) ∨ (¬ p2284) ∨ (¬ p2946))
    : (¬ p2274) ∨ (¬ p2608) ∨ (¬ p2946) ∨ (¬ p2696) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h72922 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step105101 (p2331 p2437 p2641 p2922 p3742 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73452 : p3742 ∨ p2437)
    (h72925 : (¬ p2922) ∨ (¬ p3742) ∨ (¬ p4154) ∨ (¬ p2331))
    : (¬ p2922) ∨ p2641 ∨ p2437 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72925 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step105103 (p2509 p2850 p3073 p3609 p3641 p3684 p4261 p5372 : Prop)
    (h74018 : p5372 ∨ (¬ p3641))
    (h73544 : p4261 ∨ p3073)
    (h73442 : p3684 ∨ p2850)
    (h72927 : (¬ p5372) ∨ (¬ p4261) ∨ (¬ p3609) ∨ (¬ p2509) ∨ (¬ p3684))
    : (¬ p3609) ∨ (¬ p3641) ∨ p3073 ∨ p2850 ∨ (¬ p2509) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5372 := (Or.elim h74018 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72927 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step105107 (p2264 p2363 p2459 p3553 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h72931 : p2459 ∨ (¬ p2363) ∨ (¬ p3553))
    : p2459 ∨ p2264 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h72931 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step105108 (p2573 p2578 p2579 p2641 p2662 p2667 p3461 p3564 p4137 p4154 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73526 : p4154 ∨ p2641)
    (h73524 : p4137 ∨ p3564)
    (h73274 : p2579 ∨ p2573)
    (h72932 : (¬ p4191) ∨ (¬ p4137) ∨ (¬ p2579) ∨ (¬ p2578) ∨ (¬ p4154) ∨ (¬ p2662) ∨ (¬ p2667))
    : p3461 ∨ p2641 ∨ (¬ p2578) ∨ (¬ p2667) ∨ p3564 ∨ (¬ p2662) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h72932 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step105115 (p2881 p2946 p2992 p2996 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h72939 : p2996 ∨ (¬ p2881) ∨ (¬ p3662) ∨ (¬ p2946))
    : p2992 ∨ p2996 ∨ (¬ p2946) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72939 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step105131 (p2274 p2307 p2313 p2553 p3051 p3556 p4554 p4718 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73634 : p4554 ∨ p2274)
    (h73414 : p3556 ∨ p3051)
    (h72956 : (¬ p2553) ∨ (¬ p2313) ∨ (¬ p4718) ∨ (¬ p3556) ∨ (¬ p4554))
    : (¬ p2553) ∨ p2307 ∨ (¬ p4718) ∨ p2274 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4554 := (Or.elim h73634 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h72956 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step105140 (p2608 p2707 p2850 p2911 p3367 p3588 p4644 : Prop)
    (h73430 : p3588 ∨ p2707)
    (h72966 : (¬ p3367) ∨ (¬ p3588) ∨ (¬ p2850) ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p4644))
    : p2707 ∨ (¬ p2850) ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3588 := (Or.elim h73430 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72966 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step105152 (p2187 p2352 p2440 p2542 p2668 p3324 p4715 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73270 : p2542 ∨ p2440)
    (h72978 : (¬ p3324) ∨ (¬ p2352) ∨ (¬ p2542) ∨ (¬ p4715) ∨ (¬ p2187))
    : (¬ p2352) ∨ (¬ p2187) ∨ p2668 ∨ (¬ p4715) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h72978 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step105156 (p2470 p3379 p3449 p3860 p5192 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73950 : p5192 ∨ (¬ p3379))
    (h72982 : (¬ p5192) ∨ (¬ p2470) ∨ (¬ p3860))
    : p3449 ∨ (¬ p2470) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p5192 := (Or.elim h73950 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h72982 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step105161 (p2493 p3016 p3136 p3422 p3584 p4116 p4704 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73046 : p4704)
    (h72990 : (¬ p3584) ∨ (¬ p3136) ∨ (¬ p2493) ∨ (¬ p4704) ∨ (¬ p3016) ∨ (¬ p4116))
    : p3422 ∨ (¬ p4116) ∨ (¬ p3136) ∨ (¬ p2493) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4704 := h73046;
    (Or.elim h72990 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step105162 (p2132 p2598 p2630 p2651 p2657 p3055 p4751 p5052 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73742 : p4751 ∨ (¬ p2630))
    (h73350 : p3055 ∨ p2598)
    (h72991 : (¬ p4751) ∨ (¬ p2132) ∨ (¬ p3055) ∨ (¬ p5052) ∨ (¬ p2657))
    : (¬ p2132) ∨ (¬ p5052) ∨ p2651 ∨ (¬ p2630) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4751 := (Or.elim h73742 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u7 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h72991 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step105163 (p2132 p2598 p2651 p2657 p3055 p3136 p4704 p5052 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73046 : p4704)
    (h73350 : p3055 ∨ p2598)
    (h72992 : (¬ p2132) ∨ (¬ p3055) ∨ (¬ p5052) ∨ (¬ p3136) ∨ (¬ p4704) ∨ (¬ p2657))
    : (¬ p2132) ∨ p2651 ∨ (¬ p3136) ∨ (¬ p5052) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4704 := h73046;
    let u7 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h72992 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step105164 (p2132 p2138 p2630 p2839 p3136 p3367 p3585 p4748 p5050 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73740 : p4748 ∨ p2630)
    (h73428 : p3585 ∨ p3367)
    (h73894 : p5050 ∨ (¬ p3136))
    (h72993 : (¬ p4748) ∨ (¬ p3585) ∨ (¬ p2138) ∨ (¬ p2839) ∨ (¬ p5050))
    : (¬ p2839) ∨ p2132 ∨ p2630 ∨ p3367 ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4748 := (Or.elim h73740 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p5050 := (Or.elim h73894 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h72993 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step105178 (p2122 p2166 p2191 p2230 p2274 p2331 p2417 p2668 p2737 p2829 p3073 p3367 p3389 p3425 p3822 p3950 p4134 p4243 p4261 p4471 p4492 p4781 p4889 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73222 : p2191 ∨ p2166)
    (h73472 : p3822 ∨ p2122)
    (h73008 : (¬ p3425) ∨ (¬ p3367) ∨ (¬ p2737) ∨ (¬ p4243) ∨ (¬ p2829) ∨ (¬ p4781) ∨ (¬ p3822) ∨ (¬ p4471) ∨ (¬ p4261) ∨ (¬ p2417) ∨ (¬ p2191) ∨ (¬ p4492) ∨ (¬ p3950) ∨ (¬ p4889) ∨ (¬ p3389) ∨ (¬ p2331) ∨ (¬ p4134) ∨ (¬ p2274) ∨ (¬ p2230) ∨ (¬ p2668))
    : (¬ p2417) ∨ (¬ p3950) ∨ (¬ p2668) ∨ (¬ p3425) ∨ p3073 ∨ (¬ p2737) ∨ (¬ p4243) ∨ (¬ p4781) ∨ (¬ p2829) ∨ (¬ p3367) ∨ p2166 ∨ (¬ p4492) ∨ p2122 ∨ (¬ p4889) ∨ (¬ p3389) ∨ (¬ p4471) ∨ (¬ p4134) ∨ (¬ p2274) ∨ (¬ p2230) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p4471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))))));
    let u20 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u21 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u22 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    (Or.elim h73008 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u22))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u15))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u20))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u21))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u1))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u13))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u14))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u19))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u16))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u17))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u18))) (fun r18 => (False.elim (r18 u2)))))))))))))))))))))))))))))))))))))))))

theorem step105179 (p2187 p2192 p2241 p2246 p2247 p2248 p2274 p2352 p2608 p2641 p2651 p2654 p2727 p2946 p2957 p2958 p2992 p3016 p3063 p3093 p3591 p3958 p4111 p4134 p4140 p4153 p4173 p4198 p4241 p4317 p4365 p4509 p4512 p4558 p4559 p4597 p4704 p4732 p4758 p4974 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h73432 : p3591 ∨ p3093)
    (h73046 : p4704)
    (h73746 : p4758 ∨ (¬ p2641))
    (h73732 : p4732 ∨ p2608)
    (h73286 : p2654 ∨ p2651)
    (h73226 : p2247 ∨ p2241)
    (h73658 : p4597 ∨ (¬ p2352))
    (h73860 : p4974 ∨ (¬ p3016))
    (h73518 : p4111 ∨ p2727)
    (h73009 : (¬ p4758) ∨ (¬ p4512) ∨ (¬ p4198) ∨ (¬ p4173) ∨ (¬ p3591) ∨ (¬ p4153) ∨ (¬ p4134) ∨ (¬ p4509) ∨ (¬ p4559) ∨ (¬ p4558) ∨ (¬ p2274) ∨ (¬ p4140) ∨ (¬ p2187) ∨ (¬ p3958) ∨ (¬ p2992) ∨ (¬ p4365) ∨ (¬ p4704) ∨ (¬ p4241) ∨ (¬ p2946) ∨ (¬ p2958) ∨ (¬ p2957) ∨ (¬ p4732) ∨ (¬ p2654) ∨ (¬ p2248) ∨ (¬ p2247) ∨ (¬ p2246) ∨ (¬ p3063) ∨ (¬ p4317) ∨ (¬ p4597) ∨ (¬ p4974) ∨ (¬ p4111))
    : (¬ p3063) ∨ (¬ p4317) ∨ (¬ p4198) ∨ p2192 ∨ p3093 ∨ (¬ p4153) ∨ (¬ p4512) ∨ (¬ p4509) ∨ (¬ p4559) ∨ (¬ p4558) ∨ (¬ p2274) ∨ (¬ p4140) ∨ (¬ p2187) ∨ (¬ p3958) ∨ (¬ p2992) ∨ (¬ p4365) ∨ (¬ p4241) ∨ (¬ p2641) ∨ (¬ p2958) ∨ (¬ p2946) ∨ p2608 ∨ p2651 ∨ (¬ p2248) ∨ p2241 ∨ (¬ p2246) ∨ (¬ p4134) ∨ (¬ p2957) ∨ (¬ p2352) ∨ (¬ p3016) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))));
    let u25 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))));
    let u26 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))));
    let u27 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))));
    let u28 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))));
    let u29 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))))))))))))))));
    let u30 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u31 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u32 : p4704 := h73046;
    let u33 : p4758 := (Or.elim h73746 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    let u34 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u20 r0))));
    let u35 : p2654 := (Or.elim h73286 (fun q0 => q0) (fun r0 => (False.elim (u21 r0))));
    let u36 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u23 r0))));
    let u37 : p4597 := (Or.elim h73658 (fun q0 => q0) (fun r0 => (False.elim (r0 u27))));
    let u38 : p4974 := (Or.elim h73860 (fun q0 => q0) (fun r0 => (False.elim (r0 u28))));
    let u39 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u29 r0))));
    (Or.elim h73009 (fun q0 => (False.elim (q0 u33))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u30))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u31))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u25))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u12))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u13))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u14))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u15))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u32))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u16))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u19))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u18))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u26))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u34))) (fun r21 => (Or.elim r21 (fun q22 => (False.elim (q22 u35))) (fun r22 => (Or.elim r22 (fun q23 => (False.elim (q23 u22))) (fun r23 => (Or.elim r23 (fun q24 => (False.elim (q24 u36))) (fun r24 => (Or.elim r24 (fun q25 => (False.elim (q25 u24))) (fun r25 => (Or.elim r25 (fun q26 => (False.elim (q26 u0))) (fun r26 => (Or.elim r26 (fun q27 => (False.elim (q27 u1))) (fun r27 => (Or.elim r27 (fun q28 => (False.elim (q28 u37))) (fun r28 => (Or.elim r28 (fun q29 => (False.elim (q29 u38))) (fun r29 => (False.elim (r29 u39)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem step105193 (p2598 p2608 p2630 p2651 p2657 p2881 p2946 p2992 p3051 p3055 p3367 p3556 p3570 p3585 p3954 p4704 p4748 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73414 : p3556 ∨ p3051)
    (h73498 : p3954 ∨ p2608)
    (h73418 : p3570 ∨ p2881)
    (h73740 : p4748 ∨ p2630)
    (h73288 : p2657 ∨ p2651)
    (h73046 : p4704)
    (h73350 : p3055 ∨ p2598)
    (h73023 : (¬ p4748) ∨ (¬ p3585) ∨ (¬ p3570) ∨ (¬ p3556) ∨ (¬ p2992) ∨ (¬ p2657) ∨ (¬ p3954) ∨ (¬ p2946) ∨ (¬ p4704) ∨ (¬ p3055))
    : (¬ p2992) ∨ (¬ p2946) ∨ p3367 ∨ p3051 ∨ p2608 ∨ p2881 ∨ p2630 ∨ p2651 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p4748 := (Or.elim h73740 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u14 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u15 : p4704 := h73046;
    let u16 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h73023 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u14))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u15))) (fun r8 => (False.elim (r8 u16)))))))))))))))))))))

theorem step105200 (p2363 p2528 p2534 p3125 p3958 p4602 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73030 : (¬ p4602) ∨ (¬ p2534) ∨ (¬ p3125) ∨ (¬ p3958))
    : (¬ p3125) ∨ p2528 ∨ (¬ p2363) ∨ (¬ p3958) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h73030 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step105201 (p2274 p2459 p2573 p2608 p2839 p2870 p2881 p3125 p3146 p3389 p3583 p3954 p3958 p4134 p4244 p4277 p4665 p4903 p5057 p5190 : Prop)
    (h73820 : p4903 ∨ (¬ p2881))
    (h73540 : p4244 ∨ p2870)
    (h73424 : p3583 ∨ p2839)
    (h73498 : p3954 ∨ p2608)
    (h73696 : p4665 ∨ p2459)
    (h73898 : p5057 ∨ (¬ p3146))
    (h73031 : (¬ p5057) ∨ (¬ p3125) ∨ (¬ p2274) ∨ (¬ p4134) ∨ (¬ p3958) ∨ (¬ p4665) ∨ (¬ p2573) ∨ (¬ p3583) ∨ (¬ p4903) ∨ (¬ p3389) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p5190) ∨ (¬ p3954))
    : (¬ p3125) ∨ (¬ p2274) ∨ (¬ p2881) ∨ p2870 ∨ (¬ p3958) ∨ p2839 ∨ p2608 ∨ p2459 ∨ (¬ p3146) ∨ (¬ p3389) ∨ (¬ p4134) ∨ (¬ p4277) ∨ (¬ p2573) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u15 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u16 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u17 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u18 : p4665 := (Or.elim h73696 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u19 : p5057 := (Or.elim h73898 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    (Or.elim h73031 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u18))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u16))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u14))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u15))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u13))) (fun r12 => (False.elim (r12 u17)))))))))))))))))))))))))))))

theorem step105203 (p2598 p2608 p2630 p2850 p2946 p2992 p3051 p3055 p3136 p3367 p3556 p3585 p4732 p4748 p5050 : Prop)
    (h73732 : p4732 ∨ p2608)
    (h73428 : p3585 ∨ p3367)
    (h73894 : p5050 ∨ (¬ p3136))
    (h73414 : p3556 ∨ p3051)
    (h73350 : p3055 ∨ p2598)
    (h73740 : p4748 ∨ p2630)
    (h73033 : (¬ p3585) ∨ (¬ p3556) ∨ (¬ p4732) ∨ (¬ p2992) ∨ (¬ p5050) ∨ (¬ p2850) ∨ (¬ p2946) ∨ (¬ p4748) ∨ (¬ p3055))
    : (¬ p2992) ∨ p2608 ∨ p3367 ∨ (¬ p3136) ∨ p3051 ∨ p2598 ∨ p2630 ∨ (¬ p2946) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p5050 := (Or.elim h73894 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u12 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u14 : p4748 := (Or.elim h73740 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h73033 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u14))) (fun r7 => (False.elim (r7 u13)))))))))))))))))))

theorem step105207 (p2166 p2427 p2881 p2911 p3644 p4632 p4643 p4903 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73820 : p4903 ∨ (¬ p2881))
    (h73684 : p4643 ∨ p2427)
    (h73037 : (¬ p4903) ∨ (¬ p3644) ∨ (¬ p2166) ∨ (¬ p4643) ∨ (¬ p4632))
    : p2911 ∨ (¬ p2881) ∨ (¬ p2166) ∨ p2427 ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p4643 := (Or.elim h73684 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h73037 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step105214 (p2210 p2608 p2727 p2911 p2946 p3051 p3556 p3954 p4704 p4809 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73046 : p4704)
    (h73770 : p4809 ∨ p2727)
    (h73414 : p3556 ∨ p3051)
    (h73045 : (¬ p4704) ∨ (¬ p2210) ∨ (¬ p2911) ∨ (¬ p2946) ∨ (¬ p3954) ∨ (¬ p4809) ∨ (¬ p3556))
    : p2608 ∨ (¬ p2210) ∨ (¬ p2946) ∨ p2727 ∨ (¬ p2911) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4704 := h73046;
    let u8 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h73045 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (False.elim (r5 u9)))))))))))))))

theorem step105220 (p2187 p2192 p2210 p2363 p2651 p2657 p2727 p2911 p2946 p2992 p3370 p3555 p3579 p3989 p4111 p4173 p4347 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73288 : p2657 ∨ p2651)
    (h73559 : (¬ p2363) ∨ (¬ p4347))
    (h73412 : p3555 ∨ p2210)
    (h73528 : p4173 ∨ p2192)
    (h73501 : (¬ p2187) ∨ (¬ p3989))
    (h73053 : p4347 ∨ (¬ p3579) ∨ (¬ p2992) ∨ (¬ p3370) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p2657) ∨ p3989 ∨ (¬ p4111) ∨ (¬ p2911) ∨ (¬ p2946))
    : (¬ p2911) ∨ p2727 ∨ (¬ p3579) ∨ (¬ p2992) ∨ (¬ p2946) ∨ (¬ p3370) ∨ p2651 ∨ (¬ p2363) ∨ p2210 ∨ p2192 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : (¬ p4347) := (Or.elim h73559 (fun q0 => (False.elim (q0 u7))) (fun r0 => r0));
    let u14 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u15 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u16 : (¬ p3989) := (Or.elim h73501 (fun q0 => (False.elim (q0 u10))) (fun r0 => r0));
    (Or.elim h73053 (fun q0 => (False.elim (u13 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u15))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u16 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (False.elim (r9 u4)))))))))))))))))))))))

theorem step105223 (p2241 p2253 p2598 p2946 p2992 p3055 p3379 p3452 p3662 p4376 p4749 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73394 : p3452 ∨ p3379)
    (h73350 : p3055 ∨ p2598)
    (h73056 : (¬ p3452) ∨ (¬ p4376) ∨ (¬ p3055) ∨ (¬ p2241) ∨ (¬ p2253) ∨ (¬ p3662) ∨ (¬ p2946) ∨ (¬ p4749))
    : p2992 ∨ p3379 ∨ (¬ p4376) ∨ (¬ p2241) ∨ (¬ p2253) ∨ p2598 ∨ (¬ p2946) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h73056 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step105228 (p2210 p2246 p2459 p2598 p2630 p2850 p2911 p2946 p3055 p3367 p3370 p3555 p3585 p4748 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73350 : p3055 ∨ p2598)
    (h73740 : p4748 ∨ p2630)
    (h73428 : p3585 ∨ p3367)
    (h73061 : (¬ p2911) ∨ (¬ p2459) ∨ (¬ p3555) ∨ (¬ p3370) ∨ (¬ p2850) ∨ (¬ p3055) ∨ (¬ p4748) ∨ (¬ p2946) ∨ (¬ p3585) ∨ (¬ p2246))
    : (¬ p2911) ∨ (¬ p2946) ∨ p2210 ∨ (¬ p3370) ∨ (¬ p2850) ∨ p2598 ∨ (¬ p2459) ∨ p2630 ∨ p3367 ∨ (¬ p2246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4748 := (Or.elim h73740 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h73061 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step105230 (p2274 p2352 p2881 p2911 p3644 p3958 p4557 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73636 : p4557 ∨ (¬ p2274))
    (h73064 : (¬ p4557) ∨ p2352 ∨ (¬ p2881) ∨ (¬ p3958) ∨ (¬ p3644))
    : p2911 ∨ (¬ p2881) ∨ (¬ p2274) ∨ (¬ p3958) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h73064 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step105231 (p2132 p2138 p2274 p2608 p2829 p2860 p3097 p3688 p3954 p4887 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73810 : p4887 ∨ p2860)
    (h73498 : p3954 ∨ p2608)
    (h73444 : p3688 ∨ p2829)
    (h73352 : p3097 ∨ p2274)
    (h73065 : (¬ p3097) ∨ (¬ p4887) ∨ (¬ p3688) ∨ (¬ p2138) ∨ (¬ p3954))
    : p2132 ∨ p2860 ∨ p2608 ∨ p2829 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4887 := (Or.elim h73810 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h73065 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step105234 (p2187 p2352 p2427 p2553 p2797 p3743 p3956 p4031 p4153 p4198 p4241 p4558 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h73068 : (¬ p2427) ∨ (¬ p2797) ∨ (¬ p4241) ∨ (¬ p4031) ∨ (¬ p3956) ∨ (¬ p2553) ∨ (¬ p2187) ∨ (¬ p3743) ∨ (¬ p4198) ∨ (¬ p4153) ∨ (¬ p4558))
    : (¬ p2553) ∨ (¬ p2187) ∨ (¬ p4241) ∨ (¬ p4031) ∨ (¬ p2427) ∨ (¬ p2797) ∨ p2352 ∨ (¬ p3743) ∨ (¬ p4198) ∨ (¬ p4153) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h73068 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step105236 (p2187 p2241 p2247 p2248 p2249 p2352 p2528 p2553 p2608 p2630 p2839 p2870 p3019 p3083 p3413 p3434 p3582 p3583 p3743 p3954 p3956 p3984 p4031 p4153 p4198 p4241 p4324 p4344 p4558 p4669 p4885 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h73226 : p2247 ∨ p2241)
    (h73500 : p3956 ∨ p2352)
    (h73498 : p3954 ∨ p2608)
    (h73424 : p3583 ∨ p2839)
    (h73070 : (¬ p2630) ∨ (¬ p3413) ∨ (¬ p4241) ∨ (¬ p3019) ∨ (¬ p3984) ∨ (¬ p3083) ∨ (¬ p4324) ∨ (¬ p2249) ∨ (¬ p2248) ∨ (¬ p2247) ∨ (¬ p4031) ∨ (¬ p4885) ∨ (¬ p3582) ∨ (¬ p3956) ∨ (¬ p2528) ∨ (¬ p4669) ∨ (¬ p2553) ∨ (¬ p2870) ∨ (¬ p4344) ∨ (¬ p2187) ∨ (¬ p3743) ∨ (¬ p4198) ∨ (¬ p4153) ∨ (¬ p3583) ∨ (¬ p4558) ∨ (¬ p3954))
    : (¬ p4031) ∨ (¬ p2553) ∨ p3434 ∨ (¬ p2630) ∨ (¬ p3413) ∨ (¬ p3984) ∨ (¬ p3019) ∨ (¬ p2249) ∨ (¬ p2248) ∨ p2241 ∨ (¬ p4241) ∨ (¬ p4885) ∨ (¬ p3582) ∨ p2352 ∨ p2608 ∨ (¬ p3083) ∨ (¬ p4669) ∨ (¬ p2528) ∨ (¬ p4344) ∨ (¬ p2187) ∨ (¬ p3743) ∨ (¬ p4198) ∨ (¬ p4153) ∨ p2839 ∨ (¬ p4558) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4031 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))));
    let u25 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))))))))))));
    let u26 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u27 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u28 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u29 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    let u30 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u23 r0))));
    (Or.elim h73070 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u15))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u26))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u27))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u0))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u12))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u28))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u17))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u16))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u1))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u25))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u18))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u19))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u20))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u21))) (fun r21 => (Or.elim r21 (fun q22 => (False.elim (q22 u22))) (fun r22 => (Or.elim r22 (fun q23 => (False.elim (q23 u30))) (fun r23 => (Or.elim r23 (fun q24 => (False.elim (q24 u24))) (fun r24 => (False.elim (r24 u29)))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem step105241 (p2187 p2230 p2241 p2244 p2274 p2284 p2363 p2563 p2630 p2992 p3146 p4031 p4537 p4557 p4562 p4714 p4751 : Prop)
    (h73742 : p4751 ∨ (¬ p2630))
    (h73720 : p4714 ∨ p2563)
    (h73638 : p4562 ∨ p2284)
    (h73624 : p4537 ∨ (¬ p2230))
    (h73224 : p2244 ∨ p2241)
    (h73636 : p4557 ∨ (¬ p2274))
    (h73075 : p2992 ∨ (¬ p3146) ∨ (¬ p2363) ∨ (¬ p4751) ∨ (¬ p4537) ∨ (¬ p4714) ∨ (¬ p4031) ∨ (¬ p4562) ∨ (¬ p2244) ∨ (¬ p2187) ∨ (¬ p4557))
    : p2992 ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2630) ∨ (¬ p3146) ∨ p2563 ∨ (¬ p4031) ∨ p2284 ∨ (¬ p2230) ∨ p2241 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4751 := (Or.elim h73742 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u12 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p4562 := (Or.elim h73638 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u14 : p4537 := (Or.elim h73624 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u15 : p2244 := (Or.elim h73224 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u16 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    (Or.elim h73075 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u15))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (False.elim (r9 u16)))))))))))))))))))))))

theorem step105242 (p2132 p2138 p2608 p2707 p2870 p2881 p3570 p3588 p4732 p4893 : Prop)
    (h73430 : p3588 ∨ p2707)
    (h73214 : p2138 ∨ p2132)
    (h73814 : p4893 ∨ p2870)
    (h73732 : p4732 ∨ p2608)
    (h73418 : p3570 ∨ p2881)
    (h73077 : (¬ p4732) ∨ (¬ p3570) ∨ (¬ p2138) ∨ (¬ p3588) ∨ (¬ p4893))
    : p2707 ∨ p2132 ∨ p2870 ∨ p2608 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3588 := (Or.elim h73430 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4893 := (Or.elim h73814 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h73077 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step105245 (p2274 p2307 p2313 p2608 p3093 p5014 : Prop)
    (h73876 : p5014 ∨ p3093)
    (h73238 : p2313 ∨ p2307)
    (h73080 : (¬ p5014) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2608))
    : p3093 ∨ (¬ p2274) ∨ (¬ p2608) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5014 := (Or.elim h73876 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h73080 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step105250 (p2241 p2247 p2406 p2528 p3379 p3449 p3860 p4608 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73226 : p2247 ∨ p2241)
    (h73085 : (¬ p3379) ∨ (¬ p2528) ∨ (¬ p3860) ∨ (¬ p2406) ∨ (¬ p4608) ∨ (¬ p2247))
    : (¬ p2406) ∨ p3449 ∨ p2241 ∨ (¬ p3379) ∨ (¬ p4608) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h73085 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step105252 (p2187 p3093 p3449 p3860 p4514 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73087 : (¬ p3860) ∨ (¬ p2187) ∨ (¬ p4514) ∨ (¬ p3093))
    : p3449 ∨ (¬ p2187) ∨ (¬ p4514) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h73087 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step105260 (p2241 p2244 p2274 p2307 p2310 p2553 p2608 p2630 p2829 p2870 p3399 p4105 p4366 p4557 p4707 p4735 p4751 p4865 p4893 : Prop)
    (h73798 : p4865 ∨ p2829)
    (h73224 : p2244 ∨ p2241)
    (h73569 : (¬ p3399) ∨ (¬ p4366))
    (h73636 : p4557 ∨ (¬ p2274))
    (h73716 : p4707 ∨ p2553)
    (h73742 : p4751 ∨ (¬ p2630))
    (h73236 : p2310 ∨ p2307)
    (h73814 : p4893 ∨ p2870)
    (h73734 : p4735 ∨ (¬ p2608))
    (h73095 : (¬ p2244) ∨ (¬ p4865) ∨ p4366 ∨ (¬ p4105) ∨ (¬ p4557) ∨ (¬ p4707) ∨ (¬ p4751) ∨ (¬ p2310) ∨ (¬ p4893) ∨ (¬ p4735))
    : p2829 ∨ p2241 ∨ (¬ p3399) ∨ (¬ p4105) ∨ (¬ p2274) ∨ p2553 ∨ (¬ p2630) ∨ p2307 ∨ p2870 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4865 := (Or.elim h73798 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2244 := (Or.elim h73224 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : (¬ p4366) := (Or.elim h73569 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u13 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u14 : p4707 := (Or.elim h73716 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u15 : p4751 := (Or.elim h73742 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u16 : p2310 := (Or.elim h73236 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u17 : p4893 := (Or.elim h73814 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u18 : p4735 := (Or.elim h73734 (fun q0 => q0) (fun r0 => (False.elim (r0 u9))));
    (Or.elim h73095 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u12 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u14))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u15))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u16))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u17))) (fun r8 => (False.elim (r8 u18)))))))))))))))))))))

theorem step105278 (p2352 p2829 p3367 p3923 p4865 p5221 : Prop)
    (h73798 : p4865 ∨ p2829)
    (h73113 : (¬ p3367) ∨ (¬ p4865) ∨ (¬ p2352) ∨ (¬ p3923) ∨ (¬ p5221))
    : (¬ p3367) ∨ (¬ p2352) ∨ p2829 ∨ (¬ p3923) ∨ (¬ p5221) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5221 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4865 := (Or.elim h73798 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h73113 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step105282 (p2274 p2563 p2891 p3309 p3486 p3549 p4557 p4629 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73406 : p3549 ∨ p3309)
    (h73636 : p4557 ∨ (¬ p2274))
    (h73117 : (¬ p4557) ∨ (¬ p3486) ∨ (¬ p2563) ∨ (¬ p4629) ∨ (¬ p3549))
    : p2891 ∨ p3309 ∨ (¬ p2563) ∨ (¬ p4629) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h73117 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step105289 (p2230 p2284 p2406 p2589 p2982 p3115 p3238 p3413 p3952 p4750 p4948 p5214 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73496 : p3952 ∨ p2284)
    (h73284 : p2589 ∨ p2230)
    (h73374 : p3238 ∨ p2406)
    (h73124 : (¬ p3115) ∨ (¬ p4948) ∨ (¬ p4750) ∨ (¬ p2589) ∨ (¬ p5214) ∨ (¬ p3952) ∨ (¬ p3413) ∨ (¬ p3238))
    : (¬ p3115) ∨ p2982 ∨ (¬ p4750) ∨ p2284 ∨ p2230 ∨ (¬ p5214) ∨ (¬ p3413) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h73124 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u11)))))))))))))))))

theorem step105293 (p2230 p2295 p2406 p2440 p2501 p2630 p2656 p2696 p2781 p2810 p2881 p2901 p3016 p3093 p3096 p3115 p3136 p3238 p3365 p3872 p4208 p4315 p4320 p4514 p4703 p4715 p4903 p4971 p5020 : Prop)
    (h73820 : p4903 ∨ (¬ p2881))
    (h73552 : p4320 ∨ p2901)
    (h73858 : p4971 ∨ p3016)
    (h73534 : p4208 ∨ p3115)
    (h73390 : p3365 ∨ p2696)
    (h73550 : p4315 ∨ p3136)
    (h73374 : p3238 ∨ p2406)
    (h73316 : p2810 ∨ p2630)
    (h73714 : p4703 ∨ p2440)
    (h73128 : (¬ p4971) ∨ (¬ p4320) ∨ (¬ p4903) ∨ (¬ p4208) ∨ (¬ p2295) ∨ (¬ p3872) ∨ (¬ p3093) ∨ (¬ p5020) ∨ (¬ p2781) ∨ (¬ p2501) ∨ (¬ p3365) ∨ (¬ p4715) ∨ (¬ p3096) ∨ (¬ p4514) ∨ (¬ p4315) ∨ (¬ p3238) ∨ (¬ p2656) ∨ (¬ p2810) ∨ (¬ p4703) ∨ (¬ p2230))
    : (¬ p2295) ∨ (¬ p3872) ∨ (¬ p2881) ∨ p2901 ∨ p3016 ∨ p3115 ∨ (¬ p3093) ∨ (¬ p5020) ∨ (¬ p2781) ∨ (¬ p2501) ∨ p2696 ∨ (¬ p4715) ∨ (¬ p3096) ∨ (¬ p4514) ∨ p3136 ∨ p2406 ∨ (¬ p2656) ∨ p2630 ∨ p2440 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))))));
    let u20 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u21 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u22 : p4971 := (Or.elim h73858 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u23 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u24 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u25 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    let u26 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u15 r0))));
    let u27 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u17 r0))));
    let u28 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u18 r0))));
    (Or.elim h73128 (fun q0 => (False.elim (q0 u22))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u21))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u20))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u23))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u24))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u12))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u13))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u25))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u26))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u16))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u27))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u28))) (fun r18 => (False.elim (r18 u19)))))))))))))))))))))))))))))))))))))))))

theorem step105299 (p2274 p2383 p3097 p3146 p3609 p3692 p3923 p3955 p3988 p4489 p4615 p4861 p4867 : Prop)
    (h73670 : p4615 ∨ (¬ p2383))
    (h73352 : p3097 ∨ p2274)
    (h73448 : p3692 ∨ p3146)
    (h73134 : (¬ p4615) ∨ (¬ p3609) ∨ (¬ p3923) ∨ (¬ p3097) ∨ (¬ p4861) ∨ (¬ p3692) ∨ (¬ p3955) ∨ (¬ p3988) ∨ (¬ p4867) ∨ (¬ p4489))
    : (¬ p2383) ∨ (¬ p3609) ∨ (¬ p3923) ∨ p2274 ∨ (¬ p4861) ∨ p3146 ∨ (¬ p3955) ∨ (¬ p3988) ∨ (¬ p4867) ∨ (¬ p4489) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4861 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4867 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4489 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4615 := (Or.elim h73670 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u11 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h73134 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step105301 (p2383 p2387 p2630 p2668 p2810 p2819 p3324 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73316 : p2810 ∨ p2630)
    (h73386 : p3324 ∨ p2668)
    (h73136 : (¬ p2810) ∨ (¬ p2819) ∨ (¬ p2387) ∨ (¬ p3324))
    : (¬ p2819) ∨ p2383 ∨ p2630 ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h73136 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step105302 (p2363 p2630 p2668 p2819 p3016 p3146 p3319 p3483 p3683 p3692 p3922 p4026 p4433 p4974 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h73860 : p4974 ∨ (¬ p3016))
    (h73448 : p3692 ∨ p3146)
    (h73137 : (¬ p4974) ∨ (¬ p3922) ∨ (¬ p2630) ∨ (¬ p3683) ∨ (¬ p4026) ∨ (¬ p3483) ∨ (¬ p2819) ∨ p2668 ∨ (¬ p4433) ∨ (¬ p3692) ∨ (¬ p2363))
    : (¬ p3483) ∨ p3319 ∨ (¬ p3016) ∨ (¬ p3683) ∨ (¬ p2630) ∨ (¬ p3922) ∨ (¬ p2819) ∨ p2668 ∨ (¬ p4433) ∨ p3146 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p4974 := (Or.elim h73860 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u13 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h73137 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u13))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step105303 (p2352 p2383 p2387 p2819 p3016 p3574 p3956 p4753 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73500 : p3956 ∨ p2352)
    (h73246 : p2387 ∨ p2383)
    (h73138 : (¬ p3956) ∨ (¬ p3574) ∨ (¬ p4753) ∨ (¬ p2819) ∨ (¬ p2387))
    : (¬ p2819) ∨ p3016 ∨ p2352 ∨ (¬ p4753) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h73138 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step105304 (p2187 p2352 p2363 p3146 p3692 p3956 p3988 p3989 : Prop)
    (h73499 : (¬ p2352) ∨ (¬ p3956))
    (h73448 : p3692 ∨ p3146)
    (h73502 : p3989 ∨ p2187)
    (h73139 : p3956 ∨ (¬ p3989) ∨ (¬ p3988) ∨ (¬ p3692) ∨ (¬ p2363))
    : (¬ p2352) ∨ p3146 ∨ (¬ p3988) ∨ p2187 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3956) := (Or.elim h73499 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h73139 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step105305 (p2274 p2352 p2363 p2383 p2387 p2668 p2819 p2829 p3097 p3146 p3688 p3692 p3923 p3955 p3956 p4197 p4433 p4602 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73500 : p3956 ∨ p2352)
    (h73352 : p3097 ∨ p2274)
    (h73246 : p2387 ∨ p2383)
    (h73448 : p3692 ∨ p3146)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73140 : (¬ p2819) ∨ (¬ p3688) ∨ (¬ p3923) ∨ (¬ p3956) ∨ (¬ p3097) ∨ (¬ p2387) ∨ (¬ p4197) ∨ p2668 ∨ (¬ p4433) ∨ (¬ p3692) ∨ (¬ p4602) ∨ (¬ p3955))
    : (¬ p2819) ∨ p2829 ∨ (¬ p3923) ∨ p2352 ∨ p2274 ∨ p2383 ∨ (¬ p4197) ∨ p2668 ∨ (¬ p4433) ∨ p3146 ∨ (¬ p2363) ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u14 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u15 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u16 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u17 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    (Or.elim h73140 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u15))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u16))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u17))) (fun r10 => (False.elim (r10 u11)))))))))))))))))))))))))

theorem step105316 (p2088 p2177 p2363 p2911 p3325 p3644 p3857 p4276 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73480 : p3857 ∨ p2088)
    (h73152 : (¬ p3644) ∨ (¬ p4276) ∨ (¬ p2177) ∨ (¬ p3325) ∨ (¬ p3857) ∨ (¬ p2363))
    : p2911 ∨ p2088 ∨ (¬ p4276) ∨ (¬ p3325) ∨ (¬ p2177) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h73152 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step105317 (p2088 p2177 p2315 p2459 p3857 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h73153 : (¬ p2459) ∨ (¬ p2177) ∨ (¬ p2315) ∨ (¬ p3857))
    : p2088 ∨ (¬ p2177) ∨ (¬ p2315) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h73153 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step105321 (p2245 p2608 p2630 p2651 p2657 p3379 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73288 : p2657 ∨ p2651)
    (h73158 : (¬ p2608) ∨ (¬ p2245) ∨ (¬ p3452) ∨ (¬ p2657) ∨ (¬ p2630))
    : (¬ p2245) ∨ p3379 ∨ (¬ p2608) ∨ p2651 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h73158 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step105322 (p2210 p2363 p3073 p3146 p3156 p3497 p3555 p3692 p4960 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73400 : p3497 ∨ p3156)
    (h73412 : p3555 ∨ p2210)
    (h73159 : (¬ p3692) ∨ (¬ p3073) ∨ (¬ p3497) ∨ (¬ p3555) ∨ (¬ p4960) ∨ (¬ p2363))
    : p3146 ∨ (¬ p3073) ∨ p3156 ∨ p2210 ∨ (¬ p4960) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h73159 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step105324 (p2088 p2630 p3256 p3857 p4118 p4121 : Prop)
    (h73519 : (¬ p3256) ∨ (¬ p4118))
    (h73480 : p3857 ∨ p2088)
    (h73161 : p4118 ∨ (¬ p4121) ∨ (¬ p3857) ∨ (¬ p2630))
    : (¬ p4121) ∨ (¬ p3256) ∨ p2088 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4121 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4118) := (Or.elim h73519 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u5 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h73161 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step105331 (p2088 p2122 p2274 p2363 p2528 p2696 p3016 p3506 p3574 p3755 p3822 p3857 p4067 p4391 p4557 p4729 p4831 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73422 : p3574 ∨ p3016)
    (h73636 : p4557 ∨ (¬ p2274))
    (h73480 : p3857 ∨ p2088)
    (h73168 : (¬ p4557) ∨ (¬ p3574) ∨ (¬ p2528) ∨ (¬ p3755) ∨ (¬ p4067) ∨ (¬ p3822) ∨ (¬ p4729) ∨ (¬ p3506) ∨ (¬ p4391) ∨ (¬ p2696) ∨ (¬ p4831) ∨ (¬ p2363) ∨ (¬ p3857))
    : p2122 ∨ (¬ p4391) ∨ (¬ p2528) ∨ p3016 ∨ (¬ p2274) ∨ (¬ p4067) ∨ (¬ p4729) ∨ (¬ p3755) ∨ (¬ p3506) ∨ (¬ p2696) ∨ (¬ p4831) ∨ (¬ p2363) ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u14 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u15 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u16 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    (Or.elim h73168 (fun q0 => (False.elim (q0 u15))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (False.elim (r11 u16)))))))))))))))))))))))))))

theorem step105334 (p2187 p2230 p2406 p2440 p2553 p2563 p2589 p3989 p4630 p4699 p4707 p4714 : Prop)
    (h73678 : p4630 ∨ (¬ p2406))
    (h73716 : p4707 ∨ p2553)
    (h73284 : p2589 ∨ p2230)
    (h73712 : p4699 ∨ (¬ p2440))
    (h73720 : p4714 ∨ p2563)
    (h73502 : p3989 ∨ p2187)
    (h73172 : (¬ p4630) ∨ (¬ p4707) ∨ (¬ p2589) ∨ (¬ p4699) ∨ (¬ p4714) ∨ (¬ p3989))
    : (¬ p2406) ∨ p2553 ∨ p2230 ∨ (¬ p2440) ∨ p2563 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4630 := (Or.elim h73678 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p4707 := (Or.elim h73716 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u10 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h73172 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (False.elim (r4 u11)))))))))))))

theorem step105353 (p2187 p2363 p2406 p2459 p2563 p2685 p2696 p3238 p3989 p4110 p4347 p4665 : Prop)
    (h73696 : p4665 ∨ p2459)
    (h73374 : p3238 ∨ p2406)
    (h73559 : (¬ p2363) ∨ (¬ p4347))
    (h73516 : p4110 ∨ p2563)
    (h73502 : p3989 ∨ p2187)
    (h73193 : (¬ p4665) ∨ (¬ p2685) ∨ (¬ p3238) ∨ p4347 ∨ (¬ p4110) ∨ (¬ p2696) ∨ (¬ p3989))
    : p2459 ∨ p2406 ∨ (¬ p2685) ∨ (¬ p2363) ∨ p2563 ∨ (¬ p2696) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2406) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4665 := (Or.elim h73696 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : (¬ p4347) := (Or.elim h73559 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    let u10 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h73193 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u9 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u11)))))))))))))))

theorem step105358 (p2230 p2406 p2440 p2584 p2589 p2630 p2685 p2696 p2810 p3019 p3238 p4646 p4717 p4788 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73374 : p3238 ∨ p2406)
    (h73760 : p4788 ∨ (¬ p2696))
    (h73284 : p2589 ∨ p2230)
    (h73199 : (¬ p2440) ∨ (¬ p2584) ∨ (¬ p3019) ∨ (¬ p2810) ∨ (¬ p4646) ∨ (¬ p4717) ∨ (¬ p3238) ∨ (¬ p4788) ∨ (¬ p2685) ∨ (¬ p2589))
    : (¬ p2584) ∨ (¬ p3019) ∨ (¬ p2440) ∨ p2630 ∨ (¬ p4646) ∨ (¬ p4717) ∨ p2406 ∨ (¬ p2696) ∨ (¬ p2685) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2584 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u13 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h73199 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u13)))))))))))))))))))))

theorem step105359 (p2230 p2406 p2504 p2505 p2589 p2630 p2685 p2696 p2810 p3238 p4646 p4711 p4717 p4788 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73374 : p3238 ∨ p2406)
    (h73760 : p4788 ∨ (¬ p2696))
    (h73284 : p2589 ∨ p2230)
    (h73200 : (¬ p2810) ∨ (¬ p4711) ∨ (¬ p4646) ∨ (¬ p4717) ∨ (¬ p2505) ∨ (¬ p2504) ∨ (¬ p3238) ∨ (¬ p4788) ∨ (¬ p2685) ∨ (¬ p2589))
    : p2630 ∨ (¬ p4711) ∨ (¬ p4646) ∨ (¬ p4717) ∨ (¬ p2505) ∨ (¬ p2504) ∨ p2406 ∨ (¬ p2696) ∨ (¬ p2685) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u13 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h73200 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u13)))))))))))))))))))))

theorem step105360 (p2241 p2811 p4790 : Prop)
    (h81877 : p4790 ∨ (¬ p2811) ∨ p2241)
    (h42656 : (¬ p2241) ∨ (¬ p2811) ∨ p4790)
    : p4790 ∨ (¬ p2811) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4790) := (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p2241 := (Or.elim h81877 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h42656 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step105361 (p2264 p2341 p2881 p4333 : Prop)
    (h79866 : (¬ p4333) ∨ (¬ p2881) ∨ p2264)
    (h104076 : p2341 ∨ (¬ p2264) ∨ (¬ p2881))
    : (¬ p4333) ∨ (¬ p2881) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2264 := (Or.elim h79866 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h104076 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step105364 (p2132 p2140 : Prop)
    (h99785 : p2132 ∨ p2140)
    (h44776 : (¬ p2132) ∨ p2140)
    : p2140 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2140) := (fun h => hn h);
    let u1 : p2132 := (Or.elim h99785 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44776 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105365 (p2241 p2248 : Prop)
    (h48036 : (¬ p2241) ∨ p2248)
    (h75368 : p2241 ∨ p2248)
    : p2248 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2248) := (fun h => hn h);
    let u1 : (¬ p2241) := (Or.elim h48036 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75368 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105366 (p2241 p2254 : Prop)
    (h97425 : (¬ p2241) ∨ p2254)
    (h80774 : p2241 ∨ p2254)
    : p2254 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2254) := (fun h => hn h);
    let u1 : (¬ p2241) := (Or.elim h97425 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h80774 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105367 (p2241 p2255 : Prop)
    (h97426 : (¬ p2241) ∨ p2255)
    (h80773 : p2241 ∨ p2255)
    : p2255 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2255) := (fun h => hn h);
    let u1 : (¬ p2241) := (Or.elim h97426 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h80773 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105368 (p2307 p2315 : Prop)
    (h98418 : p2307 ∨ p2315)
    (h48077 : (¬ p2307) ∨ p2315)
    : p2315 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2315) := (fun h => hn h);
    let u1 : p2307 := (Or.elim h98418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48077 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105369 (p2307 p2321 : Prop)
    (h98291 : p2307 ∨ p2321)
    (h78423 : (¬ p2307) ∨ p2321)
    : p2321 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2321) := (fun h => hn h);
    let u1 : p2307 := (Or.elim h98291 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h78423 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105370 (p2470 p2484 : Prop)
    (h99647 : p2470 ∨ p2484)
    (h75935 : (¬ p2470) ∨ p2484)
    : p2484 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2484) := (fun h => hn h);
    let u1 : p2470 := (Or.elim h99647 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75935 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105371 (p2573 p2581 : Prop)
    (h98475 : p2573 ∨ p2581)
    (h48019 : (¬ p2573) ∨ p2581)
    : p2581 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2581) := (fun h => hn h);
    let u1 : p2573 := (Or.elim h98475 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48019 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105372 (p2573 p2586 : Prop)
    (h101052 : p2573 ∨ p2586)
    (h76947 : (¬ p2573) ∨ p2586)
    : p2586 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2586) := (fun h => hn h);
    let u1 : p2573 := (Or.elim h101052 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h76947 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105373 (p2651 p2665 : Prop)
    (h97234 : p2651 ∨ p2665)
    (h78223 : (¬ p2651) ∨ p2665)
    : p2665 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2665) := (fun h => hn h);
    let u1 : p2651 := (Or.elim h97234 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h78223 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105374 (p2774 p2787 : Prop)
    (h101516 : (¬ p2774) ∨ p2787)
    (h86296 : p2774 ∨ p2787)
    : p2787 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2787) := (fun h => hn h);
    let u1 : (¬ p2774) := (Or.elim h101516 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h86296 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105375 (p2774 p2788 : Prop)
    (h101517 : (¬ p2774) ∨ p2788)
    (h86294 : p2774 ∨ p2788)
    : p2788 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2788) := (fun h => hn h);
    let u1 : (¬ p2774) := (Or.elim h101517 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h86294 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105376 (p2922 p2930 : Prop)
    (h97755 : p2922 ∨ p2930)
    (h47960 : (¬ p2922) ∨ p2930)
    : p2930 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2930) := (fun h => hn h);
    let u1 : p2922 := (Or.elim h97755 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47960 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105377 (p2946 p2960 : Prop)
    (h98524 : p2946 ∨ p2960)
    (h78248 : (¬ p2946) ∨ p2960)
    : p2960 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2960) := (fun h => hn h);
    let u1 : p2946 := (Or.elim h98524 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h78248 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105378 (p2563 p3958 : Prop)
    (h49277 : (¬ p2563) ∨ p3958)
    (h78001 : p3958 ∨ p2563)
    : p3958 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3958) := (fun h => hn h);
    let u1 : (¬ p2563) := (Or.elim h49277 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h78001 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step105379 (p2187 p4134 : Prop)
    (h98496 : p2187 ∨ p4134)
    (h78672 : p4134 ∨ (¬ p2187))
    : p4134 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4134) := (fun h => hn h);
    let u1 : p2187 := (Or.elim h98496 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h78672 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step105380 (p2427 p4277 : Prop)
    (h47774 : (¬ p2427) ∨ p4277)
    (h78256 : p4277 ∨ p2427)
    : p4277 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4277) := (fun h => hn h);
    let u1 : (¬ p2427) := (Or.elim h47774 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h78256 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step105381 (p2437 p4327 : Prop)
    (h47758 : (¬ p2437) ∨ p4327)
    (h75101 : p4327 ∨ p2437)
    : p4327 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4327) := (fun h => hn h);
    let u1 : (¬ p2437) := (Or.elim h47758 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75101 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step105382 (p2295 p4361 : Prop)
    (h98610 : p2295 ∨ p4361)
    (h79270 : p4361 ∨ (¬ p2295))
    : p4361 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4361) := (fun h => hn h);
    let u1 : p2295 := (Or.elim h98610 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h79270 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step105390 (p2156 p4489 : Prop)
    (h97927 : (¬ p2156) ∨ p4489)
    (h85380 : p2156 ∨ p4489)
    : p4489 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4489) := (fun h => hn h);
    let u1 : (¬ p2156) := (Or.elim h97927 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h85380 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105391 (p2166 p4494 : Prop)
    (h56022 : (¬ p2166) ∨ p4494)
    (h76120 : p2166 ∨ p4494)
    : p4494 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4494) := (fun h => hn h);
    let u1 : (¬ p2166) := (Or.elim h56022 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h76120 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105392 (p2187 p4509 : Prop)
    (h98494 : p2187 ∨ p4509)
    (h78671 : (¬ p2187) ∨ p4509)
    : p4509 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4509) := (fun h => hn h);
    let u1 : p2187 := (Or.elim h98494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h78671 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105393 (p2210 p4522 : Prop)
    (h45231 : (¬ p2210) ∨ p4522)
    (h75446 : p2210 ∨ p4522)
    : p4522 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4522) := (fun h => hn h);
    let u1 : (¬ p2210) := (Or.elim h45231 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75446 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105394 (p2230 p4533 : Prop)
    (h98087 : p4533 ∨ p2230)
    (h42643 : (¬ p2230) ∨ p4533)
    : p4533 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4533) := (fun h => hn h);
    let u1 : p2230 := (Or.elim h98087 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h42643 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105395 (p2230 p4539 : Prop)
    (h98213 : p2230 ∨ p4539)
    (h78252 : (¬ p2230) ∨ p4539)
    : p4539 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4539) := (fun h => hn h);
    let u1 : p2230 := (Or.elim h98213 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h78252 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105399 (p2274 p4556 : Prop)
    (h98493 : p2274 ∨ p4556)
    (h42660 : (¬ p2274) ∨ p4556)
    : p4556 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4556) := (fun h => hn h);
    let u1 : p2274 := (Or.elim h98493 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42660 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105400 (p2274 p4558 : Prop)
    (h98503 : p2274 ∨ p4558)
    (h77958 : (¬ p2274) ∨ p4558)
    : p4558 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4558) := (fun h => hn h);
    let u1 : p2274 := (Or.elim h98503 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h77958 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105401 (p2284 p4564 : Prop)
    (h49736 : (¬ p2284) ∨ p4564)
    (h77963 : p2284 ∨ p4564)
    : p4564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4564) := (fun h => hn h);
    let u1 : (¬ p2284) := (Or.elim h49736 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h77963 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105405 (p2331 p4581 : Prop)
    (h100963 : p2331 ∨ p4581)
    (h48272 : (¬ p2331) ∨ p4581)
    : p4581 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4581) := (fun h => hn h);
    let u1 : p2331 := (Or.elim h100963 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48272 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105406 (p2331 p4584 : Prop)
    (h101084 : p2331 ∨ p4584)
    (h83403 : (¬ p2331) ∨ p4584)
    : p4584 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4584) := (fun h => hn h);
    let u1 : p2331 := (Or.elim h101084 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h83403 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105407 (p2396 p4621 : Prop)
    (h100891 : p2396 ∨ p4621)
    (h42712 : (¬ p2396) ∨ p4621)
    : p4621 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4621) := (fun h => hn h);
    let u1 : p2396 := (Or.elim h100891 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42712 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105408 (p2396 p4624 : Prop)
    (h100892 : p2396 ∨ p4624)
    (h75376 : (¬ p2396) ∨ p4624)
    : p4624 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4624) := (fun h => hn h);
    let u1 : p2396 := (Or.elim h100892 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75376 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105409 (p2417 p4638 : Prop)
    (h100105 : p2417 ∨ p4638)
    (h48350 : (¬ p2417) ∨ p4638)
    : p4638 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4638) := (fun h => hn h);
    let u1 : p2417 := (Or.elim h100105 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48350 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105410 (p2417 p4640 : Prop)
    (h100034 : p2417 ∨ p4640)
    (h75819 : (¬ p2417) ∨ p4640)
    : p4640 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4640) := (fun h => hn h);
    let u1 : p2417 := (Or.elim h100034 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75819 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105411 (p2427 p4644 : Prop)
    (h42916 : (¬ p2427) ∨ p4644)
    (h78255 : p2427 ∨ p4644)
    : p4644 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4644) := (fun h => hn h);
    let u1 : (¬ p2427) := (Or.elim h42916 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h78255 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105412 (p2427 p4647 : Prop)
    (h98089 : (¬ p2427) ∨ p4647)
    (h90850 : p2427 ∨ p4647)
    : p4647 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4647) := (fun h => hn h);
    let u1 : (¬ p2427) := (Or.elim h98089 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h90850 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105413 (p2437 p4652 : Prop)
    (h98007 : (¬ p2437) ∨ p4652)
    (h75102 : p2437 ∨ p4652)
    : p4652 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4652) := (fun h => hn h);
    let u1 : (¬ p2437) := (Or.elim h98007 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75102 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105414 (p2459 p4668 : Prop)
    (h101294 : (¬ p2459) ∨ p4668)
    (h74486 : p2459 ∨ p4668)
    : p4668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4668) := (fun h => hn h);
    let u1 : (¬ p2459) := (Or.elim h101294 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h74486 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105415 (p2459 p4669 : Prop)
    (h101295 : (¬ p2459) ∨ p4669)
    (h74488 : p2459 ∨ p4669)
    : p4669 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4669) := (fun h => hn h);
    let u1 : (¬ p2459) := (Or.elim h101295 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h74488 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105422 (p2553 p4712 : Prop)
    (h98262 : p2553 ∨ p4712)
    (h76951 : (¬ p2553) ∨ p4712)
    : p4712 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4712) := (fun h => hn h);
    let u1 : p2553 := (Or.elim h98262 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h76951 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105423 (p2563 p4715 : Prop)
    (h42679 : (¬ p2563) ∨ p4715)
    (h78000 : p2563 ∨ p4715)
    : p4715 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4715) := (fun h => hn h);
    let u1 : (¬ p2563) := (Or.elim h42679 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h78000 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105424 (p2440 p4717 : Prop)
    (h70353 : p4717 ∨ (¬ p2440))
    (h74510 : p2440 ∨ p4717)
    : p4717 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4717) := (fun h => hn h);
    let u1 : (¬ p2440) := (Or.elim h70353 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h74510 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105425 (p2563 p4718 : Prop)
    (h98509 : (¬ p2563) ∨ p4718)
    (h78004 : p2563 ∨ p4718)
    : p4718 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4718) := (fun h => hn h);
    let u1 : (¬ p2563) := (Or.elim h98509 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h78004 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105429 (p2598 p4729 : Prop)
    (h97804 : (¬ p2598) ∨ p4729)
    (h80980 : p2598 ∨ p4729)
    : p4729 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4729) := (fun h => hn h);
    let u1 : (¬ p2598) := (Or.elim h97804 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h80980 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105430 (p2608 p4733 : Prop)
    (h48274 : (¬ p2608) ∨ p4733)
    (h75626 : p2608 ∨ p4733)
    : p4733 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4733) := (fun h => hn h);
    let u1 : (¬ p2608) := (Or.elim h48274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75626 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105431 (p2608 p4736 : Prop)
    (h97278 : (¬ p2608) ∨ p4736)
    (h75631 : p2608 ∨ p4736)
    : p4736 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4736) := (fun h => hn h);
    let u1 : (¬ p2608) := (Or.elim h97278 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75631 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105432 (p2630 p4749 : Prop)
    (h100555 : p2630 ∨ p4749)
    (h48721 : (¬ p2630) ∨ p4749)
    : p4749 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4749) := (fun h => hn h);
    let u1 : p2630 := (Or.elim h100555 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48721 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105433 (p2630 p4750 : Prop)
    (h100556 : p2630 ∨ p4750)
    (h48275 : (¬ p2630) ∨ p4750)
    : p4750 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4750) := (fun h => hn h);
    let u1 : p2630 := (Or.elim h100556 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48275 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105434 (p2630 p4752 : Prop)
    (h99646 : p2630 ∨ p4752)
    (h80975 : (¬ p2630) ∨ p4752)
    : p4752 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4752) := (fun h => hn h);
    let u1 : p2630 := (Or.elim h99646 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h80975 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105438 (p2707 p4793 : Prop)
    (h48390 : (¬ p2707) ∨ p4793)
    (h88248 : p2707 ∨ p4793)
    : p4793 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4793) := (fun h => hn h);
    let u1 : (¬ p2707) := (Or.elim h48390 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h88248 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105439 (p2707 p4796 : Prop)
    (h101861 : (¬ p2707) ∨ p4796)
    (h88250 : p2707 ∨ p4796)
    : p4796 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4796) := (fun h => hn h);
    let u1 : (¬ p2707) := (Or.elim h101861 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h88250 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105440 (p2727 p4814 : Prop)
    (h100203 : p2727 ∨ p4814)
    (h82178 : (¬ p2727) ∨ p4814)
    : p4814 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4814) := (fun h => hn h);
    let u1 : p2727 := (Or.elim h100203 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h82178 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105444 (p2761 p4826 : Prop)
    (h48931 : (¬ p2761) ∨ p4826)
    (h81947 : p2761 ∨ p4826)
    : p4826 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4826) := (fun h => hn h);
    let u1 : (¬ p2761) := (Or.elim h48931 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h81947 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105445 (p2761 p4831 : Prop)
    (h99910 : (¬ p2761) ∨ p4831)
    (h81897 : p2761 ∨ p4831)
    : p4831 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4831) := (fun h => hn h);
    let u1 : (¬ p2761) := (Or.elim h99910 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h81897 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105449 (p2797 p4843 : Prop)
    (h101562 : p2797 ∨ p4843)
    (h48324 : (¬ p2797) ∨ p4843)
    : p4843 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4843) := (fun h => hn h);
    let u1 : p2797 := (Or.elim h101562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48324 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105451 (p2839 p4877 : Prop)
    (h99656 : p2839 ∨ p4877)
    (h83163 : (¬ p2839) ∨ p4877)
    : p4877 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4877) := (fun h => hn h);
    let u1 : p2839 := (Or.elim h99656 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h83163 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105452 (p2839 p4878 : Prop)
    (h99655 : p2839 ∨ p4878)
    (h83164 : (¬ p2839) ∨ p4878)
    : p4878 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4878) := (fun h => hn h);
    let u1 : p2839 := (Or.elim h99655 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h83164 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105453 (p2850 p4882 : Prop)
    (h99639 : p2850 ∨ p4882)
    (h48278 : (¬ p2850) ∨ p4882)
    : p4882 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4882) := (fun h => hn h);
    let u1 : p2850 := (Or.elim h99639 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48278 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105454 (p2850 p4884 : Prop)
    (h101815 : p2850 ∨ p4884)
    (h81319 : (¬ p2850) ∨ p4884)
    : p4884 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4884) := (fun h => hn h);
    let u1 : p2850 := (Or.elim h101815 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h81319 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105455 (p2870 p4898 : Prop)
    (h101530 : (¬ p2870) ∨ p4898)
    (h86563 : p2870 ∨ p4898)
    : p4898 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4898) := (fun h => hn h);
    let u1 : (¬ p2870) := (Or.elim h101530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h86563 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105456 (p2881 p4902 : Prop)
    (h101689 : p2881 ∨ p4902)
    (h45224 : (¬ p2881) ∨ p4902)
    : p4902 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4902) := (fun h => hn h);
    let u1 : p2881 := (Or.elim h101689 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45224 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105463 (p2982 p4949 : Prop)
    (h45281 : (¬ p2982) ∨ p4949)
    (h91315 : p2982 ∨ p4949)
    : p4949 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4949) := (fun h => hn h);
    let u1 : (¬ p2982) := (Or.elim h45281 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h91315 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105464 (p3016 p4975 : Prop)
    (h101732 : (¬ p3016) ∨ p4975)
    (h83861 : p3016 ∨ p4975)
    : p4975 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4975) := (fun h => hn h);
    let u1 : (¬ p3016) := (Or.elim h101732 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h83861 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105465 (p3016 p4976 : Prop)
    (h101733 : (¬ p3016) ∨ p4976)
    (h83860 : p3016 ∨ p4976)
    : p4976 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4976) := (fun h => hn h);
    let u1 : (¬ p3016) := (Or.elim h101733 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h83860 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105469 (p3083 p5008 : Prop)
    (h48286 : (¬ p3083) ∨ p5008)
    (h74857 : p3083 ∨ p5008)
    : p5008 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5008) := (fun h => hn h);
    let u1 : (¬ p3083) := (Or.elim h48286 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h74857 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105470 (p3093 p5022 : Prop)
    (h100616 : (¬ p3093) ∨ p5022)
    (h80338 : p3093 ∨ p5022)
    : p5022 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5022) := (fun h => hn h);
    let u1 : (¬ p3093) := (Or.elim h100616 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h80338 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105471 (p3125 p5043 : Prop)
    (h100644 : p3125 ∨ p5043)
    (h45179 : (¬ p3125) ∨ p5043)
    : p5043 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5043) := (fun h => hn h);
    let u1 : p3125 := (Or.elim h100644 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45179 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105472 (p3125 p5046 : Prop)
    (h100329 : p3125 ∨ p5046)
    (h84248 : (¬ p3125) ∨ p5046)
    : p5046 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5046) := (fun h => hn h);
    let u1 : p3125 := (Or.elim h100329 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h84248 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105473 (p3136 p5052 : Prop)
    (h100767 : p3136 ∨ p5052)
    (h84269 : (¬ p3136) ∨ p5052)
    : p5052 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5052) := (fun h => hn h);
    let u1 : p3136 := (Or.elim h100767 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h84269 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105474 (p3156 p5063 : Prop)
    (h48554 : (¬ p3156) ∨ p5063)
    (h79158 : p3156 ∨ p5063)
    : p5063 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5063) := (fun h => hn h);
    let u1 : (¬ p3156) := (Or.elim h48554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h79158 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105481 (p3256 p5113 : Prop)
    (h100964 : p3256 ∨ p5113)
    (h75878 : (¬ p3256) ∨ p5113)
    : p5113 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5113) := (fun h => hn h);
    let u1 : p3256 := (Or.elim h100964 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75878 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105482 (p3266 p5118 : Prop)
    (h43221 : (¬ p3266) ∨ p5118)
    (h80751 : p3266 ∨ p5118)
    : p5118 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5118) := (fun h => hn h);
    let u1 : (¬ p3266) := (Or.elim h43221 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h80751 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105483 (p3266 p5122 : Prop)
    (h99572 : (¬ p3266) ∨ p5122)
    (h79558 : p3266 ∨ p5122)
    : p5122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5122) := (fun h => hn h);
    let u1 : (¬ p3266) := (Or.elim h99572 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h79558 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105487 (p3379 p5190 : Prop)
    (h47686 : (¬ p3379) ∨ p5190)
    (h75363 : p3379 ∨ p5190)
    : p5190 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5190) := (fun h => hn h);
    let u1 : (¬ p3379) := (Or.elim h47686 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75363 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105488 (p3379 p5193 : Prop)
    (h97319 : (¬ p3379) ∨ p5193)
    (h79656 : p3379 ∨ p5193)
    : p5193 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5193) := (fun h => hn h);
    let u1 : (¬ p3379) := (Or.elim h97319 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h79656 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105489 (p3379 p5194 : Prop)
    (h97320 : (¬ p3379) ∨ p5194)
    (h79655 : p3379 ∨ p5194)
    : p5194 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5194) := (fun h => hn h);
    let u1 : (¬ p3379) := (Or.elim h97320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h79655 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105490 (p3389 p5203 : Prop)
    (h99985 : p3389 ∨ p5203)
    (h85684 : (¬ p3389) ∨ p5203)
    : p5203 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5203) := (fun h => hn h);
    let u1 : p3389 := (Or.elim h99985 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h85684 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105491 (p3399 p5207 : Prop)
    (h49584 : (¬ p3399) ∨ p5207)
    (h76280 : p3399 ∨ p5207)
    : p5207 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5207) := (fun h => hn h);
    let u1 : (¬ p3399) := (Or.elim h49584 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h76280 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105492 (p3367 p5214 : Prop)
    (h52577 : (¬ p3367) ∨ p5214)
    (h75542 : p3367 ∨ p5214)
    : p5214 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5214) := (fun h => hn h);
    let u1 : (¬ p3367) := (Or.elim h52577 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75542 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105493 (p3367 p5217 : Prop)
    (h99607 : (¬ p3367) ∨ p5217)
    (h75543 : p3367 ∨ p5217)
    : p5217 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5217) := (fun h => hn h);
    let u1 : (¬ p3367) := (Or.elim h99607 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h75543 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105494 (p3422 p5224 : Prop)
    (h101445 : p3422 ∨ p5224)
    (h77555 : (¬ p3422) ∨ p5224)
    : p5224 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5224) := (fun h => hn h);
    let u1 : p3422 := (Or.elim h101445 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h77555 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105495 (p3422 p5225 : Prop)
    (h101446 : p3422 ∨ p5225)
    (h77556 : (¬ p3422) ∨ p5225)
    : p5225 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5225) := (fun h => hn h);
    let u1 : p3422 := (Or.elim h101446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h77556 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105496 (p3461 p5249 : Prop)
    (h45499 : (¬ p3461) ∨ p5249)
    (h82519 : p3461 ∨ p5249)
    : p5249 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5249) := (fun h => hn h);
    let u1 : (¬ p3461) := (Or.elim h45499 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h82519 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105497 (p3527 p5309 : Prop)
    (h102000 : p3527 ∨ p5309)
    (h80326 : (¬ p3527) ∨ p5309)
    : p5309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5309) := (fun h => hn h);
    let u1 : p3527 := (Or.elim h102000 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h80326 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105498 (p3599 p5329 : Prop)
    (h102478 : p3599 ∨ p5329)
    (h48789 : (¬ p3599) ∨ p5329)
    : p5329 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5329) := (fun h => hn h);
    let u1 : p3599 := (Or.elim h102478 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48789 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u0 r0)))))

theorem step105503 (p3804 p5480 : Prop)
    (h102803 : (¬ p3804) ∨ p5480)
    (h96808 : p3804 ∨ p5480)
    : p5480 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5480) := (fun h => hn h);
    let u1 : (¬ p3804) := (Or.elim h102803 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h96808 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105504 (p3811 p5481 : Prop)
    (h102798 : (¬ p3811) ∨ p5481)
    (h96806 : p3811 ∨ p5481)
    : p5481 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5481) := (fun h => hn h);
    let u1 : (¬ p3811) := (Or.elim h102798 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h96806 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step105505 (p5480 p5481 p5482 : Prop)
    (h105504 : p5481)
    (h105503 : p5480)
    (h9516 : (¬ p5480) ∨ (¬ p5481) ∨ p5482)
    : p5482 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5482) := (fun h => hn h);
    let u1 : p5481 := h105504;
    let u2 : p5480 := h105503;
    (Or.elim h9516 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step105512 (p2177 p4133 p4405 : Prop)
    (h74609 : p4405 ∨ (¬ p2177))
    (h102536 : p4133 ∨ p2177)
    (h98253 : p4405 ∨ p2177 ∨ (¬ p4133))
    : p4405 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4405) := (fun h => hn h);
    let u1 : (¬ p2177) := (Or.elim h74609 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u2 : p4133 := (Or.elim h102536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h98253 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step105514 (p2440 p2630 p2850 p4343 p4753 : Prop)
    (h97524 : p2850 ∨ p4753)
    (h74509 : p2440 ∨ p4753)
    (h80976 : (¬ p2630) ∨ p4753)
    (h91164 : p4343 ∨ p2630)
    (h87938 : (¬ p2850) ∨ (¬ p2440) ∨ (¬ p4343))
    : p4753 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4753) := (fun h => hn h);
    let u1 : p2850 := (Or.elim h97524 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : p2440 := (Or.elim h74509 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : (¬ p2630) := (Or.elim h80976 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4343 := (Or.elim h91164 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h87938 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u4)))))))

theorem step105516 (p2177 p2553 p2911 p4276 p4710 : Prop)
    (h45689 : (¬ p2911) ∨ p4276)
    (h98258 : p4276 ∨ p2553)
    (h94484 : p4710 ∨ (¬ p2553))
    (h101337 : p2177 ∨ p4276)
    (h93572 : p2911 ∨ (¬ p4710) ∨ (¬ p2177))
    : p4276 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4276) := (fun h => hn h);
    let u1 : (¬ p2911) := (Or.elim h45689 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : p2553 := (Or.elim h98258 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p4710 := (Or.elim h94484 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u4 : p2177 := (Or.elim h101337 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h93572 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u4)))))))

theorem step105523 (p2641 p2737 p2745 p2748 p2797 : Prop)
    (h47531 : (¬ p2641) ∨ p2745)
    (h100326 : p2745 ∨ p2797)
    (h80756 : p2737 ∨ p2745)
    (h86489 : p2748 ∨ (¬ p2737))
    (h100465 : p2641 ∨ (¬ p2797) ∨ (¬ p2748))
    : p2745 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2745) := (fun h => hn h);
    let u1 : (¬ p2641) := (Or.elim h47531 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : p2797 := (Or.elim h100326 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p2737 := (Or.elim h80756 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p2748 := (Or.elim h86489 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h100465 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u4)))))))

theorem step105524 (p2685 p2696 p3425 p4357 p4782 : Prop)
    (h45707 : (¬ p2696) ∨ p4782)
    (h87373 : (¬ p2685) ∨ p4782)
    (h102054 : p4357 ∨ p2685)
    (h82904 : p3425 ∨ p2696 ∨ (¬ p4357))
    : p4782 ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4782) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2696) := (Or.elim h45707 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : (¬ p2685) := (Or.elim h87373 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4357 := (Or.elim h102054 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h82904 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step105525 (p2685 p2696 p2807 p2811 p4782 : Prop)
    (h45707 : (¬ p2696) ∨ p4782)
    (h91165 : p2811 ∨ p2696)
    (h87373 : (¬ p2685) ∨ p4782)
    (h81850 : (¬ p2811) ∨ (¬ p2807) ∨ p2685)
    : p4782 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4782) := (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2696) := (Or.elim h45707 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p2811 := (Or.elim h91165 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u4 : (¬ p2685) := (Or.elim h87373 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h81850 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u4 r1)))))))

theorem step105528 (p2598 p4419 p4730 : Prop)
    (h95982 : p4419 ∨ p2598)
    (h81140 : p4730 ∨ (¬ p4419) ∨ p2598)
    : p2598 ∨ p4730 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2598) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4730) := (fun h => hn (Or.inr h));
    let u2 : p4419 := (Or.elim h95982 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h81140 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u0 r1)))))))

theorem step105534 (p2427 p2553 p2563 p3581 p4646 p4717 : Prop)
    (h98088 : (¬ p2427) ∨ p4646)
    (h105424 : p4717)
    (h23115 : (¬ p3581) ∨ p4646 ∨ (¬ p4717))
    (h98255 : p3581 ∨ p2553)
    (h78005 : p2563 ∨ p4646)
    (h104678 : p2427 ∨ (¬ p2553) ∨ (¬ p2563))
    : p4646 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4646) := (fun h => hn h);
    let u1 : (¬ p2427) := (Or.elim h98088 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : p4717 := h105424;
    let u3 : (¬ p3581) := (Or.elim h23115 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2))))));
    let u4 : p2553 := (Or.elim h98255 (fun q0 => (False.elim (u3 q0))) (fun r0 => r0));
    let u5 : p2563 := (Or.elim h78005 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h104678 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u5)))))))

theorem step105535 (p2373 p2427 p4119 p4608 : Prop)
    (h78878 : p2373 ∨ p4608)
    (h51043 : (¬ p2427) ∨ p4608)
    (h98727 : (¬ p2373) ∨ p2427 ∨ (¬ p4119))
    : p4608 ∨ (¬ p4119) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4608) := (fun h => hn (Or.inl h));
    let u1 : p4119 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p2373 := (Or.elim h78878 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : (¬ p2427) := (Or.elim h51043 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h98727 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step105540 (p2373 p2427 p2441 p2881 p2911 p3875 p4042 p4119 p4608 p4644 : Prop)
    (h105535 : p4608 ∨ (¬ p4119))
    (h87257 : p4119 ∨ p2881)
    (h96358 : p4042 ∨ (¬ p2881))
    (h51043 : (¬ p2427) ∨ p4608)
    (h95462 : p2441 ∨ p2427)
    (h78878 : p2373 ∨ p4608)
    (h105411 : p4644)
    (h23698 : (¬ p3875) ∨ p4608 ∨ (¬ p4644))
    (h80107 : p3875 ∨ (¬ p2911))
    (h98729 : (¬ p4042) ∨ (¬ p2441) ∨ (¬ p2373) ∨ p2911)
    : p4608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4608) := (fun h => hn h);
    let u1 : (¬ p4119) := (Or.elim h105535 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u2 : p2881 := (Or.elim h87257 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    let u3 : p4042 := (Or.elim h96358 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u4 : (¬ p2427) := (Or.elim h51043 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2441 := (Or.elim h95462 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u6 : p2373 := (Or.elim h78878 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4644 := h105411;
    let u8 : (¬ p3875) := (Or.elim h23698 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u7))))));
    let u9 : (¬ p2911) := (Or.elim h80107 (fun q0 => (False.elim (u8 q0))) (fun r0 => r0));
    (Or.elim h98729 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (u9 r2)))))))))

theorem step105542 (p2274 p2427 p2563 p3872 p4555 : Prop)
    (h45376 : (¬ p2427) ∨ p4555)
    (h98492 : p2274 ∨ p4555)
    (h95964 : p3872 ∨ (¬ p2274))
    (h78002 : p2563 ∨ p4555)
    (h90869 : p2427 ∨ (¬ p3872) ∨ (¬ p2563))
    : p4555 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4555) := (fun h => hn h);
    let u1 : (¬ p2427) := (Or.elim h45376 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : p2274 := (Or.elim h98492 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3872 := (Or.elim h95964 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u4 : p2563 := (Or.elim h78002 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h90869 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u4)))))))

theorem step105543 (p2187 p2192 p3063 p4514 p4516 : Prop)
    (h43372 : (¬ p3063) ∨ p4514)
    (h83583 : p2192 ∨ p4514)
    (h101224 : p4516 ∨ (¬ p2192))
    (h24188 : (¬ p2187) ∨ p3063 ∨ (¬ p4516))
    : p4514 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3063) := (Or.elim h43372 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p2192 := (Or.elim h83583 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4516 := (Or.elim h101224 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h24188 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step105544 (p2156 p2192 p3645 p4514 : Prop)
    (h46833 : (¬ p2156) ∨ p4514)
    (h83583 : p2192 ∨ p4514)
    (h85638 : (¬ p2192) ∨ p2156 ∨ (¬ p3645))
    : p4514 ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : p3645 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2156) := (Or.elim h46833 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p2192 := (Or.elim h83583 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h85638 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step105548 (p2192 p2504 p3096 p3958 p4514 p4516 : Prop)
    (h105378 : p3958)
    (h26892 : (¬ p2504) ∨ (¬ p3958) ∨ p4514)
    (h83583 : p2192 ∨ p4514)
    (h101224 : p4516 ∨ (¬ p2192))
    (h24480 : p2504 ∨ (¬ p3096) ∨ (¬ p4516))
    : p4514 ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : p3096 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p3958 := h105378;
    let u3 : (¬ p2504) := (Or.elim h26892 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u0 r1))))));
    let u4 : p2192 := (Or.elim h83583 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4516 := (Or.elim h101224 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h24480 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u5)))))))

theorem step105552 (p2156 p2192 p2210 p3093 p3369 p3645 p4514 p4516 : Prop)
    (h105544 : p4514 ∨ (¬ p3645))
    (h97487 : p3645 ∨ (¬ p2210))
    (h96464 : p3369 ∨ p2210)
    (h46833 : (¬ p2156) ∨ p4514)
    (h83583 : p2192 ∨ p4514)
    (h101224 : p4516 ∨ (¬ p2192))
    (h27738 : p2156 ∨ (¬ p3093) ∨ (¬ p3369) ∨ (¬ p4516))
    : p4514 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3645) := (Or.elim h105544 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : (¬ p2210) := (Or.elim h97487 (fun q0 => (False.elim (u2 q0))) (fun r0 => r0));
    let u4 : p3369 := (Or.elim h96464 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u5 : (¬ p2156) := (Or.elim h46833 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2192 := (Or.elim h83583 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4516 := (Or.elim h101224 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    (Or.elim h27738 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u7)))))))))

theorem step105553 (p2156 p2563 p3096 p4031 p4514 : Prop)
    (h105548 : p4514 ∨ (¬ p3096))
    (h77999 : p3096 ∨ p2563)
    (h46833 : (¬ p2156) ∨ p4514)
    (h23019 : p2156 ∨ (¬ p2563) ∨ (¬ p4031))
    : p4514 ∨ (¬ p4031) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3096) := (Or.elim h105548 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p2563 := (Or.elim h77999 (fun q0 => (False.elim (u2 q0))) (fun r0 => r0));
    let u4 : (¬ p2156) := (Or.elim h46833 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h23019 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step105556 (p2156 p2230 p2440 p2563 p2659 p3096 p3904 p4031 p4514 : Prop)
    (h105548 : p4514 ∨ (¬ p3096))
    (h77999 : p3096 ∨ p2563)
    (h46833 : (¬ p2156) ∨ p4514)
    (h105553 : p4514 ∨ (¬ p4031))
    (h78249 : p4031 ∨ (¬ p2230))
    (h103040 : p2659 ∨ p2230)
    (h102493 : p3904 ∨ p2230)
    (h85485 : p2156 ∨ p2440 ∨ (¬ p2563) ∨ (¬ p2659) ∨ (¬ p3904))
    : p4514 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3096) := (Or.elim h105548 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p2563 := (Or.elim h77999 (fun q0 => (False.elim (u2 q0))) (fun r0 => r0));
    let u4 : (¬ p2156) := (Or.elim h46833 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : (¬ p4031) := (Or.elim h105553 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u6 : (¬ p2230) := (Or.elim h78249 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    let u7 : p2659 := (Or.elim h103040 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u8 : p3904 := (Or.elim h102493 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h85485 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step105557 (p2156 p2230 p2573 p3096 p3904 p4031 p4203 p4514 : Prop)
    (h105548 : p4514 ∨ (¬ p3096))
    (h38209 : p3096 ∨ p4203)
    (h46833 : (¬ p2156) ∨ p4514)
    (h105553 : p4514 ∨ (¬ p4031))
    (h78249 : p4031 ∨ (¬ p2230))
    (h102493 : p3904 ∨ p2230)
    (h40287 : p2156 ∨ (¬ p2573) ∨ (¬ p3904) ∨ (¬ p4203))
    : p4514 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3096) := (Or.elim h105548 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p4203 := (Or.elim h38209 (fun q0 => (False.elim (u2 q0))) (fun r0 => r0));
    let u4 : (¬ p2156) := (Or.elim h46833 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : (¬ p4031) := (Or.elim h105553 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u6 : (¬ p2230) := (Or.elim h78249 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    let u7 : p3904 := (Or.elim h102493 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h40287 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step105558 (p2156 p2187 p2352 p2563 p3096 p3660 p4514 p4533 : Prop)
    (h105548 : p4514 ∨ (¬ p3096))
    (h77999 : p3096 ∨ p2563)
    (h93347 : p3660 ∨ (¬ p2563))
    (h105543 : p4514 ∨ (¬ p2187))
    (h105394 : p4533)
    (h46833 : (¬ p2156) ∨ p4514)
    (h85406 : (¬ p2352) ∨ p2156 ∨ p2187 ∨ (¬ p4533) ∨ (¬ p3660))
    : p4514 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3096) := (Or.elim h105548 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p2563 := (Or.elim h77999 (fun q0 => (False.elim (u2 q0))) (fun r0 => r0));
    let u4 : p3660 := (Or.elim h93347 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u5 : (¬ p2187) := (Or.elim h105543 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u6 : p4533 := h105394;
    let u7 : (¬ p2156) := (Or.elim h46833 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h85406 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step105563 (p2156 p2440 p3016 p3096 p4203 p4514 p4533 : Prop)
    (h105556 : p4514 ∨ p2440)
    (h46833 : (¬ p2156) ∨ p4514)
    (h105394 : p4533)
    (h105548 : p4514 ∨ (¬ p3096))
    (h38209 : p3096 ∨ p4203)
    (h101267 : (¬ p3016) ∨ (¬ p2440) ∨ p2156 ∨ (¬ p4533) ∨ (¬ p4203))
    : p4514 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p2440 := (Or.elim h105556 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : (¬ p2156) := (Or.elim h46833 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4533 := h105394;
    let u5 : (¬ p3096) := (Or.elim h105548 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u6 : p4203 := (Or.elim h38209 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    (Or.elim h101267 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step105566 (p2440 p2563 p2641 p2992 p3096 p3922 p4514 p4564 p4702 : Prop)
    (h105556 : p4514 ∨ p2440)
    (h98764 : p4702 ∨ (¬ p2440))
    (h105401 : p4564)
    (h18259 : (¬ p3922) ∨ p4514 ∨ (¬ p4564))
    (h85985 : p3922 ∨ (¬ p2641))
    (h105548 : p4514 ∨ (¬ p3096))
    (h77999 : p3096 ∨ p2563)
    (h85906 : p2641 ∨ (¬ p2992) ∨ (¬ p4702) ∨ (¬ p2563))
    : p4514 ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p2440 := (Or.elim h105556 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p4702 := (Or.elim h98764 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u4 : p4564 := h105401;
    let u5 : (¬ p3922) := (Or.elim h18259 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u4))))));
    let u6 : (¬ p2641) := (Or.elim h85985 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    let u7 : (¬ p3096) := (Or.elim h105548 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u8 : p2563 := (Or.elim h77999 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    (Or.elim h85906 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u8)))))))))

theorem step105572 (p2352 p3016 p3083 p3573 p4514 : Prop)
    (h105563 : p4514 ∨ (¬ p3016))
    (h105558 : p4514 ∨ (¬ p2352))
    (h102496 : p3573 ∨ p2352)
    (h36597 : p3016 ∨ (¬ p3083) ∨ (¬ p3573))
    : p4514 ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3016) := (Or.elim h105563 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : (¬ p2352) := (Or.elim h105558 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u4 : p3573 := (Or.elim h102496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h36597 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step105576 (p2192 p2284 p2992 p3412 p4338 p4514 p4516 : Prop)
    (h105566 : p4514 ∨ (¬ p2992))
    (h79864 : p3412 ∨ p2992)
    (h83583 : p2192 ∨ p4514)
    (h101224 : p4516 ∨ (¬ p2192))
    (h102260 : p4338 ∨ (¬ p2192))
    (h85625 : (¬ p3412) ∨ p2284 ∨ (¬ p4516) ∨ (¬ p4338))
    : p4514 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2992) := (Or.elim h105566 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3412 := (Or.elim h79864 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u4 : p2192 := (Or.elim h83583 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4516 := (Or.elim h101224 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u6 : p4338 := (Or.elim h102260 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h85625 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step105577 (p2957 p2992 p3412 p3645 p4514 : Prop)
    (h105566 : p4514 ∨ (¬ p2992))
    (h79864 : p3412 ∨ p2992)
    (h105544 : p4514 ∨ (¬ p3645))
    (h11247 : (¬ p2957) ∨ (¬ p3412) ∨ p3645)
    : p4514 ∨ (¬ p2957) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2992) := (Or.elim h105566 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3412 := (Or.elim h79864 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u4 : (¬ p3645) := (Or.elim h105544 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h11247 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u4 r1)))))))

theorem step105582 (p2156 p2563 p2651 p2946 p2957 p3096 p4514 : Prop)
    (h105577 : p4514 ∨ (¬ p2957))
    (h78245 : (¬ p2946) ∨ p2957)
    (h46833 : (¬ p2156) ∨ p4514)
    (h105548 : p4514 ∨ (¬ p3096))
    (h77999 : p3096 ∨ p2563)
    (h102867 : p2946 ∨ p2156 ∨ (¬ p2563) ∨ (¬ p2651))
    : p4514 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2957) := (Or.elim h105577 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : (¬ p2946) := (Or.elim h78245 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u4 : (¬ p2156) := (Or.elim h46833 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : (¬ p3096) := (Or.elim h105548 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u6 : p2563 := (Or.elim h77999 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    (Or.elim h102867 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step105588 (p2352 p2363 p2573 p2651 p3083 p4514 : Prop)
    (h105582 : p4514 ∨ (¬ p2651))
    (h105557 : p4514 ∨ (¬ p2573))
    (h105572 : p4514 ∨ (¬ p3083))
    (h105558 : p4514 ∨ (¬ p2352))
    (h103617 : p2363 ∨ p2573 ∨ p2651 ∨ p3083 ∨ p2352)
    : p4514 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2651) := (Or.elim h105582 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : (¬ p2573) := (Or.elim h105557 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u4 : (¬ p3083) := (Or.elim h105572 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u5 : (¬ p2352) := (Or.elim h105558 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h103617 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (u5 r3)))))))))))

theorem step105591 (p2651 p2655 p2664 : Prop)
    (h88056 : p2655 ∨ p2651)
    (h101844 : p2664 ∨ (¬ p2655) ∨ p2651)
    : p2651 ∨ p2664 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2664) := (fun h => hn (Or.inr h));
    let u2 : p2655 := (Or.elim h88056 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h101844 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u0 r1)))))))

theorem step105596 (p2901 p2957 p3051 p4280 : Prop)
    (h45132 : (¬ p3051) ∨ p4280)
    (h78214 : p4280 ∨ p2901)
    (h92844 : (¬ p2901) ∨ p3051 ∨ (¬ p2957))
    : p4280 ∨ (¬ p2957) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4280) := (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3051) := (Or.elim h45132 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p2901 := (Or.elim h78214 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h92844 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step105597 (p2651 p2901 p2946 p2950 p2957 p3051 p4280 : Prop)
    (h45132 : (¬ p3051) ∨ p4280)
    (h78214 : p4280 ∨ p2901)
    (h105596 : p4280 ∨ (¬ p2957))
    (h78245 : (¬ p2946) ∨ p2957)
    (h102504 : p2950 ∨ p2946)
    (h92881 : (¬ p2901) ∨ p3051 ∨ (¬ p2651) ∨ (¬ p2950))
    : p4280 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4280) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3051) := (Or.elim h45132 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p2901 := (Or.elim h78214 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u4 : (¬ p2957) := (Or.elim h105596 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u5 : (¬ p2946) := (Or.elim h78245 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u6 : p2950 := (Or.elim h102504 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h92881 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step105599 (p2437 p2651 p2807 p3579 p4112 p4277 p4280 : Prop)
    (h105380 : p4277)
    (h6467 : (¬ p3579) ∨ (¬ p4277) ∨ p4280)
    (h98005 : p3579 ∨ (¬ p2437))
    (h96077 : p4112 ∨ p2437)
    (h99154 : p2807 ∨ p4280)
    (h105597 : p4280 ∨ (¬ p2651))
    (h74850 : p2651 ∨ (¬ p4112) ∨ (¬ p2807))
    : p4280 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4280) := (fun h => hn h);
    let u1 : p4277 := h105380;
    let u2 : (¬ p3579) := (Or.elim h6467 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u0 r1))))));
    let u3 : (¬ p2437) := (Or.elim h98005 (fun q0 => (False.elim (u2 q0))) (fun r0 => r0));
    let u4 : p4112 := (Or.elim h96077 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u5 : p2807 := (Or.elim h99154 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : (¬ p2651) := (Or.elim h105597 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h74850 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u5)))))))

theorem step105600 (p2870 p2901 p3136 p4316 p5053 : Prop)
    (h63593 : (¬ p2901) ∨ p5053)
    (h84270 : (¬ p3136) ∨ p5053)
    (h84419 : p4316 ∨ p3136)
    (h100652 : p2901 ∨ (¬ p4316) ∨ (¬ p2870))
    : p5053 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5053) := (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2901) := (Or.elim h63593 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : (¬ p3136) := (Or.elim h84270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4316 := (Or.elim h84419 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h100652 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u1)))))))

theorem step105601 (p2742 p2992 p3136 p5053 : Prop)
    (h99815 : p2992 ∨ p5053)
    (h84270 : (¬ p3136) ∨ p5053)
    (h6529 : (¬ p2742) ∨ (¬ p2992) ∨ p3136)
    : p5053 ∨ (¬ p2742) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5053) := (fun h => hn (Or.inl h));
    let u1 : p2742 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p2992 := (Or.elim h99815 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : (¬ p3136) := (Or.elim h84270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6529 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u3 r1)))))))

theorem step105602 (p2696 p2992 p3136 p5053 : Prop)
    (h99815 : p2992 ∨ p5053)
    (h84270 : (¬ p3136) ∨ p5053)
    (h103692 : p3136 ∨ (¬ p2992) ∨ p2696)
    : p5053 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5053) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr h));
    let u2 : p2992 := (Or.elim h99815 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : (¬ p3136) := (Or.elim h84270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h103692 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step105604 (p2132 p2946 p3136 p5053 : Prop)
    (h101736 : p2946 ∨ p5053)
    (h84270 : (¬ p3136) ∨ p5053)
    (h99697 : p2132 ∨ (¬ p2946) ∨ p3136)
    : p5053 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5053) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr h));
    let u2 : p2946 := (Or.elim h101736 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : (¬ p3136) := (Or.elim h84270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h99697 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u3 r1)))))))

theorem step105606 (p2598 p2696 p2946 p3136 p4117 p4749 p5053 : Prop)
    (h101736 : p2946 ∨ p5053)
    (h84270 : (¬ p3136) ∨ p5053)
    (h105602 : p5053 ∨ p2696)
    (h84448 : p4117 ∨ (¬ p2696))
    (h105432 : p4749)
    (h100727 : p3136 ∨ (¬ p2946) ∨ p2598 ∨ (¬ p4117) ∨ (¬ p4749))
    : p5053 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5053) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr h));
    let u2 : p2946 := (Or.elim h101736 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : (¬ p3136) := (Or.elim h84270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p2696 := (Or.elim h105602 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u5 : p4117 := (Or.elim h84448 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u6 : p4749 := h105432;
    (Or.elim h100727 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step105607 (p2284 p2860 p3136 p4316 p5053 : Prop)
    (h84270 : (¬ p3136) ∨ p5053)
    (h84419 : p4316 ∨ p3136)
    (h47057 : (¬ p2284) ∨ p5053)
    (h98949 : p2284 ∨ (¬ p4316) ∨ (¬ p2860))
    : p5053 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5053) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3136) := (Or.elim h84270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4316 := (Or.elim h84419 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u4 : (¬ p2284) := (Or.elim h47057 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h98949 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step105611 (p2696 p2737 p2742 p2839 p2946 p3136 p4316 p4790 p5053 : Prop)
    (h105601 : p5053 ∨ (¬ p2742))
    (h80754 : p2737 ∨ p2742)
    (h105602 : p5053 ∨ p2696)
    (h100669 : p4790 ∨ (¬ p2696))
    (h101736 : p2946 ∨ p5053)
    (h84270 : (¬ p3136) ∨ p5053)
    (h84419 : p4316 ∨ p3136)
    (h100390 : (¬ p2737) ∨ p2839 ∨ (¬ p4790) ∨ (¬ p2946) ∨ (¬ p4316))
    : p5053 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5053) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2742) := (Or.elim h105601 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p2737 := (Or.elim h80754 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u4 : p2696 := (Or.elim h105602 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u5 : p4790 := (Or.elim h100669 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u6 : p2946 := (Or.elim h101736 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : (¬ p3136) := (Or.elim h84270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4316 := (Or.elim h84419 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h100390 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step105614 (p2696 p4117 p4786 : Prop)
    (h84448 : p4117 ∨ (¬ p2696))
    (h50832 : (¬ p2696) ∨ (¬ p4117) ∨ p4786)
    : (¬ p2696) ∨ p4786 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4786) := (fun h => hn (Or.inr h));
    let u2 : p4117 := (Or.elim h84448 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h50832 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step105617 (p2132 p2630 p3136 p5053 : Prop)
    (h105604 : p5053 ∨ p2132)
    (h84270 : (¬ p3136) ∨ p5053)
    (h100776 : p5053 ∨ p3136 ∨ (¬ p2132) ∨ (¬ p2630))
    : p5053 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5053) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p2132 := (Or.elim h105604 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : (¬ p3136) := (Or.elim h84270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h100776 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step105618 (p2598 p2737 p2742 p2992 p3367 p5053 : Prop)
    (h105606 : p5053 ∨ p2598)
    (h99815 : p2992 ∨ p5053)
    (h105601 : p5053 ∨ (¬ p2742))
    (h80754 : p2737 ∨ p2742)
    (h104746 : (¬ p2992) ∨ p3367 ∨ (¬ p2598) ∨ (¬ p2737))
    : p5053 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5053) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr h));
    let u2 : p2598 := (Or.elim h105606 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p2992 := (Or.elim h99815 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p2742) := (Or.elim h105601 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u5 : p2737 := (Or.elim h80754 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h104746 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step105626 (p3136 p3695 p3879 p4241 p4882 p4906 p5051 : Prop)
    (h100649 : p4906 ∨ p3136)
    (h96314 : p5051 ∨ (¬ p3136))
    (h105453 : p4882)
    (h24637 : (¬ p3879) ∨ (¬ p4882) ∨ p4906)
    (h17832 : p3879 ∨ p4241)
    (h22484 : p3695 ∨ (¬ p4241) ∨ (¬ p5051))
    : p4906 ∨ p3695 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4906) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3695) := (fun h => hn (Or.inr h));
    let u2 : p3136 := (Or.elim h100649 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p5051 := (Or.elim h96314 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u4 : p4882 := h105453;
    let u5 : (¬ p3879) := (Or.elim h24637 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (u0 r1))))));
    let u6 : p4241 := (Or.elim h17832 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    (Or.elim h22484 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (False.elim (r1 u3)))))))

theorem step105632 (p2440 p3695 p3879 p4705 p4882 p4906 : Prop)
    (h105626 : p4906 ∨ p3695)
    (h105453 : p4882)
    (h24637 : (¬ p3879) ∨ (¬ p4882) ∨ p4906)
    (h97929 : p3879 ∨ (¬ p2440))
    (h96415 : p4705 ∨ p2440)
    (h28608 : (¬ p3695) ∨ (¬ p4705) ∨ p4906)
    : p4906 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4906) := (fun h => hn h);
    let u1 : p3695 := (Or.elim h105626 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u2 : p4882 := h105453;
    let u3 : (¬ p3879) := (Or.elim h24637 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u0 r1))))));
    let u4 : (¬ p2440) := (Or.elim h97929 (fun q0 => (False.elim (u3 q0))) (fun r0 => r0));
    let u5 : p4705 := (Or.elim h96415 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h28608 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (False.elim (u0 r1)))))))

theorem step105633 (p2437 p2727 p2922 p3487 p4811 : Prop)
    (h100200 : p2727 ∨ p4811)
    (h95900 : p3487 ∨ (¬ p2727))
    (h75105 : p2437 ∨ p4811)
    (h52302 : (¬ p2922) ∨ p4811)
    (h87700 : p2922 ∨ (¬ p2437) ∨ (¬ p3487))
    : p4811 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4811) := (fun h => hn h);
    let u1 : p2727 := (Or.elim h100200 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : p3487 := (Or.elim h95900 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p2437 := (Or.elim h75105 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p2922) := (Or.elim h52302 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h87700 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step105646 (p2241 p2245 p2254 p2608 p2696 p3589 p3873 p4733 p4789 : Prop)
    (h105430 : p4733)
    (h24596 : (¬ p2245) ∨ (¬ p4733) ∨ p4789)
    (h75366 : p2241 ∨ p2245)
    (h105366 : p2254)
    (h21614 : (¬ p2254) ∨ (¬ p3589) ∨ p4789)
    (h6353 : p3589 ∨ p3873)
    (h100367 : (¬ p2696) ∨ p4789)
    (h97277 : p3589 ∨ (¬ p2608))
    (h103787 : (¬ p2241) ∨ p2696 ∨ (¬ p3873) ∨ p2608)
    : p4789 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4789) := (fun h => hn h);
    let u1 : p4733 := h105430;
    let u2 : (¬ p2245) := (Or.elim h24596 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u0 r1))))));
    let u3 : p2241 := (Or.elim h75366 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u4 : p2254 := h105366;
    let u5 : (¬ p3589) := (Or.elim h21614 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u0 r1))))));
    let u6 : p3873 := (Or.elim h6353 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    let u7 : (¬ p2696) := (Or.elim h100367 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : (¬ p2608) := (Or.elim h97277 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    (Or.elim h103787 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (u8 r2)))))))))

theorem step105655 (p2441 p2553 p2590 p3581 p3660 p4646 p4711 p4715 : Prop)
    (h105423 : p4715)
    (h23287 : (¬ p2441) ∨ p4711 ∨ (¬ p4715))
    (h105534 : p4646)
    (h26720 : (¬ p3660) ∨ (¬ p4646) ∨ p4711)
    (h6931 : p2590 ∨ p3660)
    (h76950 : (¬ p2553) ∨ p4711)
    (h102249 : p3581 ∨ p2553)
    (h11542 : p2441 ∨ (¬ p2590) ∨ (¬ p3581))
    : p4711 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4711) := (fun h => hn h);
    let u1 : p4715 := h105423;
    let u2 : (¬ p2441) := (Or.elim h23287 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1))))));
    let u3 : p4646 := h105534;
    let u4 : (¬ p3660) := (Or.elim h26720 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u0 r1))))));
    let u5 : p2590 := (Or.elim h6931 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u6 : (¬ p2553) := (Or.elim h76950 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3581 := (Or.elim h102249 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h11542 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (False.elim (r1 u7)))))))

theorem step105658 (p2264 p2449 p2459 p3945 p4666 : Prop)
    (h46527 : (¬ p2449) ∨ p4666)
    (h99327 : p2264 ∨ p4666)
    (h79495 : p2459 ∨ p4666)
    (h92417 : p3945 ∨ (¬ p2459))
    (h6901 : (¬ p2264) ∨ p2449 ∨ (¬ p3945))
    : p4666 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4666) := (fun h => hn h);
    let u1 : (¬ p2449) := (Or.elim h46527 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : p2264 := (Or.elim h99327 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p2459 := (Or.elim h79495 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3945 := (Or.elim h92417 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h6901 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step105659 (p2187 p2363 p3125 p3990 p4601 : Prop)
    (h98497 : p2187 ∨ p4601)
    (h78593 : p2363 ∨ p4601)
    (h90097 : p3990 ∨ (¬ p2363))
    (h100341 : p3125 ∨ (¬ p2187) ∨ (¬ p3990))
    : p4601 ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4601) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr h));
    let u2 : p2187 := (Or.elim h98497 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p2363 := (Or.elim h78593 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3990 := (Or.elim h90097 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h100341 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u4)))))))

theorem step105662 (p2363 p3979 p4200 p4601 : Prop)
    (h43294 : (¬ p3979) ∨ p4601)
    (h78593 : p2363 ∨ p4601)
    (h34666 : (¬ p2363) ∨ p3979 ∨ (¬ p4200))
    : p4601 ∨ (¬ p4200) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4601) := (fun h => hn (Or.inl h));
    let u1 : p4200 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3979) := (Or.elim h43294 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p2363 := (Or.elim h78593 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h34666 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step105670 (p2363 p3266 p3461 p3979 p3990 p4200 p4601 p5117 p5577 p5580 p5583 : Prop)
    (h105662 : p4601 ∨ (¬ p4200))
    (h93629 : p4200 ∨ (¬ p3266))
    (h96294 : p5117 ∨ p3266)
    (h78593 : p2363 ∨ p4601)
    (h90097 : p3990 ∨ (¬ p2363))
    (h43294 : (¬ p3979) ∨ p4601)
    (h9814 : p3979 ∨ (¬ p5583))
    (h66486 : p5577 ∨ p5583)
    (h9808 : (¬ p5577) ∨ p5580)
    (h100288 : (¬ p5580) ∨ (¬ p5117) ∨ (¬ p3990) ∨ (¬ p3461))
    : p4601 ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4601) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p4200) := (Or.elim h105662 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : (¬ p3266) := (Or.elim h93629 (fun q0 => (False.elim (u2 q0))) (fun r0 => r0));
    let u4 : p5117 := (Or.elim h96294 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u5 : p2363 := (Or.elim h78593 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3990 := (Or.elim h90097 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u7 : (¬ p3979) := (Or.elim h43294 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : (¬ p5583) := (Or.elim h9814 (fun q0 => (False.elim (u7 q0))) (fun r0 => r0));
    let u9 : p5577 := (Or.elim h66486 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u10 : p5580 := (Or.elim h9808 (fun q0 => (False.elim (q0 u9))) (fun r0 => r0));
    (Or.elim h100288 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step105690 (p2274 p3051 p4559 : Prop)
    (h77959 : (¬ p2274) ∨ p4559)
    (h98226 : p4559 ∨ p2274 ∨ (¬ p3051))
    : p4559 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4559) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2274) := (Or.elim h77959 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h98226 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step105694 (p2274 p2553 p3096 p4559 : Prop)
    (h98259 : p2553 ∨ p4559)
    (h77959 : (¬ p2274) ∨ p4559)
    (h77052 : (¬ p2553) ∨ p2274 ∨ (¬ p3096))
    : p4559 ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4559) := (fun h => hn (Or.inl h));
    let u1 : p3096 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p2553 := (Or.elim h98259 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : (¬ p2274) := (Or.elim h77959 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h77052 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

end ElevenRUP
