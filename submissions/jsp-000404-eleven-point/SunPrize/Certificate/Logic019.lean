import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step59910 (p2015 p2027 p2388 p2797 p3323 p4026 p4315 : Prop)
    (h2175 : p2015)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h34587 : (¬ p2015) ∨ p2027 ∨ p2388 ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p4026) ∨ (¬ p4315))
    : (¬ p2797) ∨ (¬ p3323) ∨ (¬ p4026) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2015 := h2175;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2388) := h40873;
    (Or.elim h34587 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step59914 (p2027 p2298 p3286 p3414 p3690 p4556 p4660 : Prop)
    (h40810 : (¬ p2027))
    (h34591 : p2027 ∨ (¬ p2298) ∨ (¬ p3286) ∨ (¬ p3414) ∨ (¬ p3690) ∨ (¬ p4556) ∨ (¬ p4660))
    : (¬ p2298) ∨ (¬ p3286) ∨ (¬ p3414) ∨ (¬ p3690) ∨ (¬ p4556) ∨ (¬ p4660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2298 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34591 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step59915 (p2003 p2027 p2247 p2313 p2688 p3093 p3309 : Prop)
    (h2163 : p2003)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h34592 : (¬ p2003) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2313) ∨ p2688 ∨ (¬ p3093) ∨ (¬ p3309))
    : (¬ p2247) ∨ (¬ p2313) ∨ (¬ p3093) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2003 := h2163;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h34592 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step59919 (p2027 p2109 p2177 p2707 p3960 p4242 p4473 : Prop)
    (h40810 : (¬ p2027))
    (h34600 : p2027 ∨ (¬ p2109) ∨ (¬ p2177) ∨ (¬ p2707) ∨ (¬ p3960) ∨ (¬ p4242) ∨ (¬ p4473))
    : (¬ p2109) ∨ (¬ p2177) ∨ (¬ p2707) ∨ (¬ p3960) ∨ (¬ p4242) ∨ (¬ p4473) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2109 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34600 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step59921 (p1983 p2027 p2202 p2440 p3276 p3343 p4381 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h34603 : (¬ p1983) ∨ p2027 ∨ p2202 ∨ (¬ p2440) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4381))
    : (¬ p2440) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h34603 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step59926 (p2027 p2210 p2476 p2891 p3083 p3246 p3359 p4641 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h34610 : p2027 ∨ (¬ p2210) ∨ (¬ p2476) ∨ (¬ p2891) ∨ (¬ p3083) ∨ (¬ p3246) ∨ (¬ p3359) ∨ (¬ p4641) ∨ (¬ p5193))
    : (¬ p2210) ∨ (¬ p2476) ∨ (¬ p2891) ∨ (¬ p3083) ∨ (¬ p3246) ∨ (¬ p3359) ∨ (¬ p4641) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h34610 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step59927 (p1991 p2027 p2440 p2462 p2657 p3690 p4235 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h34611 : (¬ p1991) ∨ p2027 ∨ (¬ p2440) ∨ p2462 ∨ (¬ p2657) ∨ (¬ p3690) ∨ (¬ p4235))
    : (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3690) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h34611 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step59930 (p2027 p2588 p3276 p4349 p4405 p4417 p4422 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h34615 : p2027 ∨ (¬ p2588) ∨ (¬ p3276) ∨ (¬ p4349) ∨ (¬ p4405) ∨ (¬ p4417) ∨ (¬ p4422) ∨ (¬ p5284))
    : (¬ p2588) ∨ (¬ p3276) ∨ (¬ p4349) ∨ (¬ p4405) ∨ (¬ p4417) ∨ (¬ p4422) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4349 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h34615 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step59931 (p2027 p2254 p2542 p2589 p2608 p2655 p3359 p3537 p3609 p4947 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h34616 : p2027 ∨ (¬ p2254) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2655) ∨ (¬ p3359) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p4947) ∨ (¬ p5059))
    : (¬ p2254) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2655) ∨ (¬ p3359) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p4947) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h34616 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step59932 (p1975 p2027 p2114 p2299 p2341 p2737 p3365 p3819 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h34617 : (¬ p1975) ∨ p2027 ∨ p2114 ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3819))
    : (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3819) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h34617 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step59937 (p1992 p2027 p2388 p2608 p3755 p3834 p3847 p4315 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h34624 : (¬ p1992) ∨ p2027 ∨ p2388 ∨ (¬ p2608) ∨ (¬ p3755) ∨ (¬ p3834) ∨ (¬ p3847) ∨ (¬ p4315))
    : (¬ p2608) ∨ (¬ p3755) ∨ (¬ p3834) ∨ (¬ p3847) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3847 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2388) := h40873;
    (Or.elim h34624 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step59938 (p2027 p2166 p2210 p3055 p3146 p3584 p4137 p4604 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h34625 : p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4736))
    : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h34625 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step59942 (p2027 p2088 p2578 p2588 p4114 p4118 p4405 p4417 : Prop)
    (h40810 : (¬ p2027))
    (h34629 : p2027 ∨ (¬ p2088) ∨ (¬ p2578) ∨ (¬ p2588) ∨ (¬ p4114) ∨ (¬ p4118) ∨ (¬ p4405) ∨ (¬ p4417))
    : (¬ p2088) ∨ (¬ p2578) ∨ (¬ p2588) ∨ (¬ p4114) ∨ (¬ p4118) ∨ (¬ p4405) ∨ (¬ p4417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h34629 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step59943 (p1986 p2027 p2104 p2598 p2764 p4340 p4444 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h34630 : (¬ p1986) ∨ p2027 ∨ (¬ p2104) ∨ (¬ p2598) ∨ p2764 ∨ (¬ p4340) ∨ (¬ p4444))
    : (¬ p2104) ∨ (¬ p2598) ∨ (¬ p4340) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1986 := h2146;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h34630 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step59945 (p1982 p2027 p2699 p2761 p3399 p3527 p3945 p4444 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h34632 : (¬ p1982) ∨ p2027 ∨ p2699 ∨ (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3945) ∨ (¬ p4444))
    : (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3945) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h34632 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step59956 (p1986 p2027 p2598 p2766 p2780 p4347 p4358 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h34646 : (¬ p1986) ∨ p2027 ∨ (¬ p2598) ∨ p2766 ∨ (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4358))
    : (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1986 := h2146;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h34646 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step59958 (p1986 p2027 p2169 p2363 p2598 p2780 p4078 p4340 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h34648 : (¬ p1986) ∨ p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4078) ∨ (¬ p4340))
    : (¬ p2363) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4078) ∨ (¬ p4340) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1986 := h2146;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h34648 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step59959 (p1990 p2027 p2177 p2192 p2997 p3486 p3570 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h34649 : (¬ p1990) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2192) ∨ p2997 ∨ (¬ p3486) ∨ (¬ p3570))
    : (¬ p2177) ∨ (¬ p2192) ∨ (¬ p3486) ∨ (¬ p3570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h34649 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step59960 (p2027 p2363 p3063 p3093 p3346 p3680 p4425 p5059 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h34650 : p2027 ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3346) ∨ (¬ p3680) ∨ (¬ p4425) ∨ (¬ p5059) ∨ (¬ p5193))
    : (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3346) ∨ (¬ p3680) ∨ (¬ p4425) ∨ (¬ p5059) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h34650 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step59961 (p2007 p2027 p2202 p2440 p2470 p2579 p3016 : Prop)
    (h2167 : p2007)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h34651 : (¬ p2007) ∨ p2027 ∨ p2202 ∨ (¬ p2440) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3016))
    : (¬ p2440) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2007 := h2167;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h34651 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step59963 (p2002 p2027 p2774 p2997 p3365 p3568 p4195 : Prop)
    (h2162 : p2002)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h34653 : (¬ p2002) ∨ p2027 ∨ (¬ p2774) ∨ p2997 ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p4195))
    : (¬ p2774) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p4195) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2002 := h2162;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h34653 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step59968 (p2027 p2870 p3238 p3582 p4235 p5214 : Prop)
    (h40810 : (¬ p2027))
    (h34659 : p2027 ∨ (¬ p2870) ∨ (¬ p3238) ∨ (¬ p3582) ∨ (¬ p4235) ∨ (¬ p5214))
    : (¬ p2870) ∨ (¬ p3238) ∨ (¬ p3582) ∨ (¬ p4235) ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34659 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step59969 (p2027 p2870 p3238 p3413 p4235 p4316 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h34660 : p2027 ∨ (¬ p2870) ∨ (¬ p3238) ∨ (¬ p3413) ∨ (¬ p4235) ∨ (¬ p4316) ∨ (¬ p4811))
    : (¬ p2870) ∨ (¬ p3238) ∨ (¬ p3413) ∨ (¬ p4235) ∨ (¬ p4316) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34660 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step59972 (p2027 p2299 p3093 p3365 p3497 p3527 p3747 p4315 p4452 p4559 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h34665 : p2027 ∨ (¬ p2299) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3497) ∨ (¬ p3527) ∨ (¬ p3747) ∨ (¬ p4315) ∨ (¬ p4452) ∨ (¬ p4559) ∨ (¬ p4736))
    : (¬ p2299) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3497) ∨ (¬ p3527) ∨ (¬ p3747) ∨ (¬ p4315) ∨ (¬ p4452) ∨ (¬ p4559) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h34665 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step59986 (p2027 p2352 p2573 p2665 p3324 p4194 : Prop)
    (h40810 : (¬ p2027))
    (h34687 : p2027 ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p2665) ∨ (¬ p3324) ∨ (¬ p4194))
    : (¬ p2352) ∨ (¬ p2573) ∨ (¬ p2665) ∨ (¬ p3324) ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34687 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step59991 (p2027 p2927 p3389 p3527 p3659 p3686 p4730 : Prop)
    (h40810 : (¬ p2027))
    (h34695 : p2027 ∨ (¬ p2927) ∨ (¬ p3389) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3686) ∨ (¬ p4730))
    : (¬ p2927) ∨ (¬ p3389) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3686) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2927 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3686 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34695 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step59997 (p2027 p2138 p2241 p2264 p3027 p3146 p4340 p4359 p4736 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h34703 : p2027 ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3146) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4736) ∨ (¬ p4905))
    : (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3146) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4736) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h34703 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60001 (p2027 p2470 p2579 p4318 p4358 p4370 p5222 : Prop)
    (h40810 : (¬ p2027))
    (h34710 : p2027 ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p4318) ∨ (¬ p4358) ∨ (¬ p4370) ∨ (¬ p5222))
    : (¬ p2470) ∨ (¬ p2579) ∨ (¬ p4318) ∨ (¬ p4358) ∨ (¬ p4370) ∨ (¬ p5222) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34710 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60006 (p2027 p2363 p2383 p2781 p3266 p3365 p4315 p5405 p5740 : Prop)
    (h40810 : (¬ p2027))
    (h34718 : p2027 ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p5405) ∨ (¬ p5740))
    : (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p5405) ∨ (¬ p5740) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h34718 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60007 (p2027 p2132 p2753 p2870 p2881 p3379 p3591 p3923 p4503 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h34719 : p2027 ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4503) ∨ (¬ p5216))
    : (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4503) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h34719 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60010 (p2010 p2027 p2765 p2881 p3051 p3644 p3646 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h34722 : (¬ p2010) ∨ p2027 ∨ p2765 ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3644) ∨ (¬ p3646))
    : (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3644) ∨ (¬ p3646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2010 := h2170;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h34722 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60011 (p2027 p2247 p2589 p2744 p3366 p3399 p3631 p3744 p3905 p4110 p4625 : Prop)
    (h40810 : (¬ p2027))
    (h34725 : p2027 ∨ (¬ p2247) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3744) ∨ (¬ p3905) ∨ (¬ p4110) ∨ (¬ p4625))
    : (¬ p2247) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3744) ∨ (¬ p3905) ∨ (¬ p4110) ∨ (¬ p4625) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h34725 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60015 (p1994 p2027 p2230 p2440 p2476 p2534 p2766 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h34729 : (¬ p1994) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2534) ∨ p2766)
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2534) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h34729 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step60017 (p2027 p3105 p3947 p4135 p4244 p4280 : Prop)
    (h40810 : (¬ p2027))
    (h34731 : p2027 ∨ (¬ p3105) ∨ (¬ p3947) ∨ (¬ p4135) ∨ (¬ p4244) ∨ (¬ p4280))
    : (¬ p3105) ∨ (¬ p3947) ∨ (¬ p4135) ∨ (¬ p4244) ∨ (¬ p4280) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34731 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60018 (p2027 p2363 p2476 p2534 p2881 p2901 p2946 p3905 p4503 p4786 : Prop)
    (h40810 : (¬ p2027))
    (h34733 : p2027 ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3905) ∨ (¬ p4503) ∨ (¬ p4786))
    : (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3905) ∨ (¬ p4503) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h34733 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60020 (p1984 p2027 p2850 p3008 p3238 p3584 p3954 p4257 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h34735 : (¬ p1984) ∨ p2027 ∨ (¬ p2850) ∨ p3008 ∨ (¬ p3238) ∨ (¬ p3584) ∨ (¬ p3954) ∨ (¬ p4257))
    : (¬ p2850) ∨ (¬ p3238) ∨ (¬ p3584) ∨ (¬ p3954) ∨ (¬ p4257) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3008) := h40891;
    (Or.elim h34735 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60021 (p2027 p2307 p2406 p2497 p2578 p3549 p4715 : Prop)
    (h40810 : (¬ p2027))
    (h34737 : p2027 ∨ (¬ p2307) ∨ (¬ p2406) ∨ (¬ p2497) ∨ (¬ p2578) ∨ (¬ p3549) ∨ (¬ p4715))
    : (¬ p2307) ∨ (¬ p2406) ∨ (¬ p2497) ∨ (¬ p2578) ∨ (¬ p3549) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34737 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60022 (p2027 p2299 p2341 p2396 p3359 p3365 p3413 p4315 p4641 p5257 : Prop)
    (h40810 : (¬ p2027))
    (h34738 : p2027 ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p3413) ∨ (¬ p4315) ∨ (¬ p4641) ∨ (¬ p5257))
    : (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p3413) ∨ (¬ p4315) ∨ (¬ p4641) ∨ (¬ p5257) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h34738 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60025 (p2027 p2246 p2509 p2608 p2744 p2958 p3051 p3156 p3452 p4320 p4434 : Prop)
    (h40810 : (¬ p2027))
    (h34742 : p2027 ∨ (¬ p2246) ∨ (¬ p2509) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p4320) ∨ (¬ p4434))
    : (¬ p2246) ∨ (¬ p2509) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p4320) ∨ (¬ p4434) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h34742 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60026 (p2027 p2254 p2952 p3093 p3309 p3791 p4208 p4322 p4826 : Prop)
    (h40810 : (¬ p2027))
    (h34743 : p2027 ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3791) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4826))
    : (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3791) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4826) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h34743 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60027 (p1982 p2027 p2459 p2842 p2850 p2881 p3051 p4109 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h34744 : (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ p2842 ∨ (¬ p2850) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p4109))
    : (¬ p2459) ∨ (¬ p2850) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2842) := h40885;
    (Or.elim h34744 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60029 (p2027 p2139 p2363 p2476 p2534 p3051 p3156 p3905 p4320 p4433 : Prop)
    (h40810 : (¬ p2027))
    (h34746 : p2027 ∨ (¬ p2139) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3905) ∨ (¬ p4320) ∨ (¬ p4433))
    : (¬ p2139) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3905) ∨ (¬ p4320) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2139 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h34746 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60030 (p2027 p2406 p2499 p2860 p3096 p4885 : Prop)
    (h40810 : (¬ p2027))
    (h34748 : p2027 ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2860) ∨ (¬ p3096) ∨ (¬ p4885))
    : (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2860) ∨ (¬ p3096) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34748 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60031 (p2027 p3319 p3359 p3365 p3366 p3413 p3461 p4315 p4444 p4697 p4866 : Prop)
    (h40810 : (¬ p2027))
    (h34749 : p2027 ∨ (¬ p3319) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3413) ∨ (¬ p3461) ∨ (¬ p4315) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p4866))
    : (¬ p3319) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3413) ∨ (¬ p3461) ∨ (¬ p4315) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p4866) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h34749 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60033 (p1992 p2027 p2608 p2850 p3008 p3555 p3584 p4034 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h34751 : (¬ p1992) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2850) ∨ p3008 ∨ (¬ p3555) ∨ (¬ p3584) ∨ (¬ p4034))
    : (¬ p2608) ∨ (¬ p2850) ∨ (¬ p3555) ∨ (¬ p3584) ∨ (¬ p4034) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3008) := h40891;
    (Or.elim h34751 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60034 (p1975 p2027 p2114 p2299 p3093 p3527 p3954 p4452 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h34752 : (¬ p1975) ∨ p2027 ∨ p2114 ∨ (¬ p2299) ∨ (¬ p3093) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4452))
    : (¬ p2299) ∨ (¬ p3093) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h34752 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60036 (p2027 p2122 p2563 p3556 p3645 p4210 p4275 p4401 : Prop)
    (h40810 : (¬ p2027))
    (h34755 : p2027 ∨ (¬ p2122) ∨ (¬ p2563) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4210) ∨ (¬ p4275) ∨ (¬ p4401))
    : (¬ p2122) ∨ (¬ p2563) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4210) ∨ (¬ p4275) ∨ (¬ p4401) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h34755 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60037 (p2027 p2598 p3585 p3589 p4366 p4793 : Prop)
    (h40810 : (¬ p2027))
    (h34756 : p2027 ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4366) ∨ (¬ p4793))
    : (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4366) ∨ (¬ p4793) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4793 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34756 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60038 (p2027 p2598 p3555 p3585 p3589 p4377 : Prop)
    (h40810 : (¬ p2027))
    (h34758 : p2027 ∨ (¬ p2598) ∨ (¬ p3555) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4377))
    : (¬ p2598) ∨ (¬ p3555) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4377) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34758 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60039 (p2027 p2598 p3585 p3589 p3591 p4866 : Prop)
    (h40810 : (¬ p2027))
    (h34759 : p2027 ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3591) ∨ (¬ p4866))
    : (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3591) ∨ (¬ p4866) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34759 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60043 (p2027 p2396 p2743 p2774 p3172 p3309 p3361 p3918 p3950 p4118 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h34764 : p2027 ∨ (¬ p2396) ∨ (¬ p2743) ∨ (¬ p2774) ∨ (¬ p3172) ∨ (¬ p3309) ∨ (¬ p3361) ∨ (¬ p3918) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4737))
    : (¬ p2396) ∨ (¬ p2743) ∨ (¬ p2774) ∨ (¬ p3172) ∨ (¬ p3309) ∨ (¬ p3361) ∨ (¬ p3918) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h34764 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60046 (p2027 p2284 p3125 p4275 p4320 p4624 : Prop)
    (h40810 : (¬ p2027))
    (h34768 : p2027 ∨ (¬ p2284) ∨ (¬ p3125) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4624))
    : (¬ p2284) ∨ (¬ p3125) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4624) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34768 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60047 (p2027 p2284 p2383 p3743 p4275 p4320 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h34769 : p2027 ∨ (¬ p2284) ∨ (¬ p2383) ∨ (¬ p3743) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4405))
    : (¬ p2284) ∨ (¬ p2383) ∨ (¬ p3743) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34769 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60048 (p2027 p2139 p3212 p3365 p3572 p3680 p3947 p4191 p4621 : Prop)
    (h40810 : (¬ p2027))
    (h34770 : p2027 ∨ (¬ p2139) ∨ (¬ p3212) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3680) ∨ (¬ p3947) ∨ (¬ p4191) ∨ (¬ p4621))
    : (¬ p2139) ∨ (¬ p3212) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3680) ∨ (¬ p3947) ∨ (¬ p4191) ∨ (¬ p4621) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2139 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h34770 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60049 (p2027 p2299 p2319 p2341 p2779 p2829 p3055 p3238 p4030 p4235 p4559 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h34771 : p2027 ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p4030) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4734))
    : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p4030) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h34771 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step60051 (p1978 p2027 p2169 p3323 p3324 p3646 p3744 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h34773 : (¬ p1978) ∨ p2027 ∨ p2169 ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3646) ∨ (¬ p3744))
    : (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3646) ∨ (¬ p3744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1978 := h2138;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h34773 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60053 (p2027 p3609 p3822 p4347 p4405 p4861 : Prop)
    (h40810 : (¬ p2027))
    (h34775 : p2027 ∨ (¬ p3609) ∨ (¬ p3822) ∨ (¬ p4347) ∨ (¬ p4405) ∨ (¬ p4861))
    : (¬ p3609) ∨ (¬ p3822) ∨ (¬ p4347) ∨ (¬ p4405) ∨ (¬ p4861) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4861 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34775 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60057 (p1981 p2027 p2187 p2699 p3093 p3319 p3744 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h34779 : (¬ p1981) ∨ p2027 ∨ (¬ p2187) ∨ p2699 ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3744))
    : (¬ p2187) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h34779 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60058 (p1975 p2027 p2299 p2608 p2699 p2717 p2829 p3426 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h34780 : (¬ p1975) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2717) ∨ (¬ p2829) ∨ (¬ p3426))
    : (¬ p2299) ∨ (¬ p2608) ∨ (¬ p2717) ∨ (¬ p2829) ∨ (¬ p3426) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h34780 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60061 (p1976 p2027 p2797 p2938 p2963 p4236 p4315 p4320 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h34783 : (¬ p1976) ∨ p2027 ∨ (¬ p2797) ∨ p2938 ∨ (¬ p2963) ∨ (¬ p4236) ∨ (¬ p4315) ∨ (¬ p4320))
    : (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4236) ∨ (¬ p4315) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2938) := h40888;
    (Or.elim h34783 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60065 (p2027 p2753 p3379 p3434 p3471 p3657 p3860 p3941 p4261 p5122 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h34787 : p2027 ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3657) ∨ (¬ p3860) ∨ (¬ p3941) ∨ (¬ p4261) ∨ (¬ p5122) ∨ (¬ p5216))
    : (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3657) ∨ (¬ p3860) ∨ (¬ p3941) ∨ (¬ p4261) ∨ (¬ p5122) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h34787 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60067 (p1998 p2027 p2177 p2247 p2545 p2553 p2573 p2810 p3005 p4360 p5190 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h34789 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2247) ∨ p2545 ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4360) ∨ (¬ p5190))
    : (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4360) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p1998 := h2158;
    let u9 : (¬ p2027) := h40810;
    let u10 : (¬ p2545) := h40876;
    (Or.elim h34789 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u10 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step60068 (p1987 p2027 p2938 p2982 p4208 p4235 p4315 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h34791 : (¬ p1987) ∨ p2027 ∨ p2938 ∨ (¬ p2982) ∨ (¬ p4208) ∨ (¬ p4235) ∨ (¬ p4315))
    : (¬ p2982) ∨ (¬ p4208) ∨ (¬ p4235) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h34791 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60069 (p2027 p2651 p2745 p2797 p2963 p4111 : Prop)
    (h40810 : (¬ p2027))
    (h34792 : p2027 ∨ (¬ p2651) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4111))
    : (¬ p2651) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34792 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60071 (p1998 p2027 p2177 p2553 p2622 p2630 p3016 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h34795 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2553) ∨ p2622 ∨ (¬ p2630) ∨ (¬ p3016))
    : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2630) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h34795 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60073 (p2027 p2299 p2589 p2850 p3399 p3527 p3876 p3905 p4001 p4559 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h34797 : p2027 ∨ (¬ p2299) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4001) ∨ (¬ p4559) ∨ (¬ p4736))
    : (¬ p2299) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4001) ∨ (¬ p4559) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h34797 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60075 (p2027 p2248 p2264 p2807 p3941 p3954 p4242 p4340 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h34799 : p2027 ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3941) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p5122))
    : (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3941) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h34799 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60078 (p1992 p2027 p2608 p2765 p3238 p3452 p4110 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h34803 : (¬ p1992) ∨ p2027 ∨ (¬ p2608) ∨ p2765 ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4110))
    : (¬ p2608) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h34803 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60079 (p2027 p2406 p3364 p3541 p3588 p3684 p4778 : Prop)
    (h40810 : (¬ p2027))
    (h34804 : p2027 ∨ (¬ p2406) ∨ (¬ p3364) ∨ (¬ p3541) ∨ (¬ p3588) ∨ (¬ p3684) ∨ (¬ p4778))
    : (¬ p2406) ∨ (¬ p3364) ∨ (¬ p3541) ∨ (¬ p3588) ∨ (¬ p3684) ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34804 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60084 (p2027 p2299 p2406 p2589 p2717 p2928 p3471 p4001 p4108 p4559 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h34809 : p2027 ∨ (¬ p2299) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2717) ∨ (¬ p2928) ∨ (¬ p3471) ∨ (¬ p4001) ∨ (¬ p4108) ∨ (¬ p4559) ∨ (¬ p4733))
    : (¬ p2299) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2717) ∨ (¬ p2928) ∨ (¬ p3471) ∨ (¬ p4001) ∨ (¬ p4108) ∨ (¬ p4559) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h34809 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60086 (p1983 p2027 p2299 p2341 p2396 p2688 p3027 p4066 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h34811 : (¬ p1983) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2396) ∨ p2688 ∨ (¬ p3027) ∨ (¬ p4066))
    : (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3027) ∨ (¬ p4066) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1983 := h2143;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h34811 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60090 (p2027 p2299 p2406 p2589 p2717 p2928 p3471 p4108 p4712 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h34815 : p2027 ∨ (¬ p2299) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2717) ∨ (¬ p2928) ∨ (¬ p3471) ∨ (¬ p4108) ∨ (¬ p4712) ∨ (¬ p4733))
    : (¬ p2299) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2717) ∨ (¬ p2928) ∨ (¬ p3471) ∨ (¬ p4108) ∨ (¬ p4712) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h34815 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60093 (p1994 p2027 p2264 p2651 p2688 p3027 p3551 p4849 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h34819 : (¬ p1994) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p2651) ∨ p2688 ∨ (¬ p3027) ∨ (¬ p3551) ∨ (¬ p4849))
    : (¬ p2264) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p3551) ∨ (¬ p4849) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4849 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h34819 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60100 (p2027 p2246 p2331 p2363 p2608 p2668 p2744 p3555 p4363 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h34827 : p2027 ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059))
    : (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h34827 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60103 (p1994 p2027 p2633 p2651 p2952 p3570 p4320 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h34830 : (¬ p1994) ∨ p2027 ∨ p2633 ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4320))
    : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h34830 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60107 (p2027 p2319 p2341 p2584 p2665 p3644 p3742 : Prop)
    (h40810 : (¬ p2027))
    (h34838 : p2027 ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2584) ∨ (¬ p2665) ∨ (¬ p3644) ∨ (¬ p3742))
    : (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2584) ∨ (¬ p2665) ∨ (¬ p3644) ∨ (¬ p3742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34838 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60110 (p2027 p3005 p3572 p3947 p4378 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h34842 : p2027 ∨ (¬ p3005) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4378) ∨ (¬ p4666))
    : (¬ p3005) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4378) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34842 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60111 (p2027 p2657 p3166 p3238 p3487 p3880 p5063 : Prop)
    (h40810 : (¬ p2027))
    (h34843 : p2027 ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p3238) ∨ (¬ p3487) ∨ (¬ p3880) ∨ (¬ p5063))
    : (¬ p2657) ∨ (¬ p3166) ∨ (¬ p3238) ∨ (¬ p3487) ∨ (¬ p3880) ∨ (¬ p5063) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34843 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60113 (p2027 p2104 p2177 p2528 p3093 p3309 p4340 p4438 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h34845 : p2027 ∨ (¬ p2104) ∨ (¬ p2177) ∨ (¬ p2528) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p4340) ∨ (¬ p4438) ∨ (¬ p4736))
    : (¬ p2104) ∨ (¬ p2177) ∨ (¬ p2528) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p4340) ∨ (¬ p4438) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h34845 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60126 (p2027 p2104 p2187 p2192 p2210 p2528 p4340 p4384 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h34861 : p2027 ∨ (¬ p2104) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2528) ∨ (¬ p4340) ∨ (¬ p4384) ∨ (¬ p4736))
    : (¬ p2104) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2528) ∨ (¬ p4340) ∨ (¬ p4384) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h34861 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60133 (p1987 p2027 p2373 p2765 p3497 p4110 p4315 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h34871 : (¬ p1987) ∨ p2027 ∨ (¬ p2373) ∨ p2765 ∨ (¬ p3497) ∨ (¬ p4110) ∨ (¬ p4315))
    : (¬ p2373) ∨ (¬ p3497) ∨ (¬ p4110) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h34871 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60137 (p1987 p2027 p2737 p3360 p3516 p3588 p4324 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40895 : (¬ p3360))
    (h34875 : (¬ p1987) ∨ p2027 ∨ (¬ p2737) ∨ p3360 ∨ (¬ p3516) ∨ (¬ p3588) ∨ (¬ p4324))
    : (¬ p2737) ∨ (¬ p3516) ∨ (¬ p3588) ∨ (¬ p4324) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3360) := h40895;
    (Or.elim h34875 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60138 (p1986 p2027 p2287 p2963 p3166 p3367 p4242 p4963 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h34876 : (¬ p1986) ∨ p2027 ∨ p2287 ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4963))
    : (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4963) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1986 := h2146;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2287) := h40869;
    (Or.elim h34876 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60139 (p1987 p2027 p2982 p3578 p3880 p4208 p4315 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h34877 : (¬ p1987) ∨ p2027 ∨ (¬ p2982) ∨ p3578 ∨ (¬ p3880) ∨ (¬ p4208) ∨ (¬ p4315))
    : (¬ p2982) ∨ (¬ p3880) ∨ (¬ p4208) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3578) := h40900;
    (Or.elim h34877 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60142 (p1987 p2027 p2765 p2982 p4110 p4208 p4315 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h34880 : (¬ p1987) ∨ p2027 ∨ p2765 ∨ (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4208) ∨ (¬ p4315))
    : (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4208) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h34880 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60148 (p1977 p2027 p2459 p2534 p2633 p2662 p3540 p4111 p4186 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h34887 : (¬ p1977) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2534) ∨ p2633 ∨ (¬ p2662) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4186))
    : (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4186) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1977 := h2137;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2633) := h40879;
    (Or.elim h34887 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step60150 (p1977 p2027 p2462 p2911 p2996 p3551 p4155 p4278 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h34889 : (¬ p1977) ∨ p2027 ∨ p2462 ∨ (¬ p2911) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4278))
    : (¬ p2911) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2462) := h40875;
    (Or.elim h34889 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60152 (p2027 p2952 p3286 p4039 p4385 p4906 : Prop)
    (h40810 : (¬ p2027))
    (h34891 : p2027 ∨ (¬ p2952) ∨ (¬ p3286) ∨ (¬ p4039) ∨ (¬ p4385) ∨ (¬ p4906))
    : (¬ p2952) ∨ (¬ p3286) ∨ (¬ p4039) ∨ (¬ p4385) ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4039 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34891 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60162 (p1993 p2027 p2299 p2313 p2633 p2667 p3189 p4154 : Prop)
    (h2153 : p1993)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h34902 : (¬ p1993) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2313) ∨ p2633 ∨ (¬ p2667) ∨ (¬ p3189) ∨ (¬ p4154))
    : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (¬ p3189) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1993 := h2153;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h34902 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60163 (p1987 p2027 p2252 p2588 p2727 p2810 p2963 p2997 p4389 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h34903 : (¬ p1987) ∨ p2027 ∨ (¬ p2252) ∨ (¬ p2588) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p2963) ∨ p2997 ∨ (¬ p4389))
    : (¬ p2252) ∨ (¬ p2588) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p4389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1987 := h2147;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2997) := h40890;
    (Or.elim h34903 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step60164 (p1977 p2027 p2352 p2387 p2588 p2667 p2997 p4154 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h34904 : (¬ p1977) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p2667) ∨ p2997 ∨ (¬ p4154))
    : (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p2667) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h34904 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60165 (p2027 p2255 p3031 p3166 p3256 p3544 p4261 : Prop)
    (h40810 : (¬ p2027))
    (h34905 : p2027 ∨ (¬ p2255) ∨ (¬ p3031) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3544) ∨ (¬ p4261))
    : (¬ p2255) ∨ (¬ p3031) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3544) ∨ (¬ p4261) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34905 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60168 (p1987 p2027 p2252 p2588 p2651 p2810 p2997 p4154 p4389 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h34910 : (¬ p1987) ∨ p2027 ∨ p2252 ∨ (¬ p2588) ∨ (¬ p2651) ∨ (¬ p2810) ∨ p2997 ∨ (¬ p4154) ∨ (¬ p4389))
    : p2252 ∨ (¬ p2588) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p4154) ∨ (¬ p4389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2252) := (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1987 := h2147;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2997) := h40890;
    (Or.elim h34910 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u8 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step60169 (p1975 p2027 p2299 p2331 p2388 p2952 p3527 p4319 p4452 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h34911 : (¬ p1975) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2331) ∨ p2388 ∨ (¬ p2952) ∨ (¬ p3527) ∨ (¬ p4319) ∨ (¬ p4452))
    : (¬ p2299) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3527) ∨ (¬ p4319) ∨ (¬ p4452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1975 := h2135;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2388) := h40873;
    (Or.elim h34911 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step60170 (p2027 p2255 p2352 p2493 p2651 p2957 p3556 p3570 p3662 p4116 p4133 : Prop)
    (h40810 : (¬ p2027))
    (h34912 : p2027 ∨ (¬ p2255) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2651) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4116) ∨ (¬ p4133))
    : (¬ p2255) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2651) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4116) ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h34912 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60171 (p2027 p2255 p2651 p2996 p3222 p3276 p3577 p3659 p4116 p4155 p5123 p5558 : Prop)
    (h40810 : (¬ p2027))
    (h34913 : p2027 ∨ (¬ p2255) ∨ (¬ p2651) ∨ (¬ p2996) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3577) ∨ (¬ p3659) ∨ (¬ p4116) ∨ (¬ p4155) ∨ (¬ p5123) ∨ (¬ p5558))
    : (¬ p2255) ∨ (¬ p2651) ∨ (¬ p2996) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3577) ∨ (¬ p3659) ∨ (¬ p4116) ∨ (¬ p4155) ∨ (¬ p5123) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h34913 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step60176 (p2027 p2177 p3027 p3177 p3960 p4360 p4570 : Prop)
    (h40810 : (¬ p2027))
    (h34918 : p2027 ∨ (¬ p2177) ∨ (¬ p3027) ∨ (¬ p3177) ∨ (¬ p3960) ∨ (¬ p4360) ∨ (¬ p4570))
    : (¬ p2177) ∨ (¬ p3027) ∨ (¬ p3177) ∨ (¬ p3960) ∨ (¬ p4360) ∨ (¬ p4570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34918 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60177 (p2027 p2331 p2952 p3758 p4319 p4516 p4906 : Prop)
    (h40810 : (¬ p2027))
    (h34919 : p2027 ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3758) ∨ (¬ p4319) ∨ (¬ p4516) ∨ (¬ p4906))
    : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3758) ∨ (¬ p4319) ∨ (¬ p4516) ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34919 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60180 (p2027 p3527 p3570 p4173 p4431 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h34922 : p2027 ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4173) ∨ (¬ p4431) ∨ (¬ p4558))
    : (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4173) ∨ (¬ p4431) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34922 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60184 (p1998 p2027 p2210 p2352 p2588 p2780 p2881 p2891 p2997 p4358 p4736 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h34928 : (¬ p1998) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p2780) ∨ (¬ p2881) ∨ (¬ p2891) ∨ p2997 ∨ (¬ p4358) ∨ (¬ p4736))
    : (¬ p2210) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p2780) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4358) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p1998 := h2158;
    let u9 : (¬ p2027) := h40810;
    let u10 : (¬ p2997) := h40890;
    (Or.elim h34928 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u10 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step60186 (p1994 p2027 p2633 p2651 p2952 p3570 p3879 p4235 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h34930 : (¬ p1994) ∨ p2027 ∨ p2633 ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p3879) ∨ (¬ p4235))
    : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p3879) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h34930 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60187 (p1994 p2027 p2630 p2633 p3570 p3879 p4235 p4315 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h34931 : (¬ p1994) ∨ p2027 ∨ (¬ p2630) ∨ p2633 ∨ (¬ p3570) ∨ (¬ p3879) ∨ (¬ p4235) ∨ (¬ p4315))
    : (¬ p2630) ∨ (¬ p3570) ∨ (¬ p3879) ∨ (¬ p4235) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h34931 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60189 (p2027 p3246 p3309 p4026 p4396 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h34934 : p2027 ∨ (¬ p3246) ∨ (¬ p3309) ∨ (¬ p4026) ∨ (¬ p4396) ∨ (¬ p4559))
    : (¬ p3246) ∨ (¬ p3309) ∨ (¬ p4026) ∨ (¬ p4396) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34934 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60190 (p2027 p2255 p2417 p2651 p2922 p2957 p3662 p3680 p3773 p3951 p4116 p4380 : Prop)
    (h40810 : (¬ p2027))
    (h34935 : p2027 ∨ (¬ p2255) ∨ (¬ p2417) ∨ (¬ p2651) ∨ (¬ p2922) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p3951) ∨ (¬ p4116) ∨ (¬ p4380))
    : (¬ p2255) ∨ (¬ p2417) ∨ (¬ p2651) ∨ (¬ p2922) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p3951) ∨ (¬ p4116) ∨ (¬ p4380) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4380 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h34935 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step60197 (p2027 p2518 p2651 p3364 p3874 p4116 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h34949 : p2027 ∨ (¬ p2518) ∨ (¬ p2651) ∨ (¬ p3364) ∨ (¬ p3874) ∨ (¬ p4116) ∨ (¬ p4790))
    : (¬ p2518) ∨ (¬ p2651) ∨ (¬ p3364) ∨ (¬ p3874) ∨ (¬ p4116) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34949 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60199 (p1989 p2027 p2313 p2764 p4107 p4173 p4356 p4381 : Prop)
    (h2149 : p1989)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h34952 : (¬ p1989) ∨ p2027 ∨ (¬ p2313) ∨ p2764 ∨ (¬ p4107) ∨ (¬ p4173) ∨ (¬ p4356) ∨ (¬ p4381))
    : (¬ p2313) ∨ (¬ p4107) ∨ (¬ p4173) ∨ (¬ p4356) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1989 := h2149;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h34952 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60206 (p2027 p2255 p2528 p2651 p2957 p3083 p3556 p3662 p3690 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h34963 : p2027 ∨ (¬ p2255) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2957) ∨ (¬ p3083) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p4669))
    : (¬ p2255) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2957) ∨ (¬ p3083) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h34963 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60207 (p2027 p2417 p2476 p3389 p4383 p4668 : Prop)
    (h40810 : (¬ p2027))
    (h34964 : p2027 ∨ (¬ p2417) ∨ (¬ p2476) ∨ (¬ p3389) ∨ (¬ p4383) ∨ (¬ p4668))
    : (¬ p2417) ∨ (¬ p2476) ∨ (¬ p3389) ∨ (¬ p4383) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h34964 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60209 (p1979 p2027 p2699 p3093 p3136 p3309 p3822 p4841 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h34966 : (¬ p1979) ∨ p2027 ∨ p2699 ∨ (¬ p3093) ∨ (¬ p3136) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p4841))
    : (¬ p3093) ∨ (¬ p3136) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p4841) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1979 := h2139;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h34966 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60212 (p2027 p2254 p2363 p2440 p2657 p3063 p3093 p4948 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h34969 : p2027 ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p4948) ∨ (¬ p5059))
    : (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p4948) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h34969 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60218 (p1990 p2027 p2114 p2210 p3097 p3309 p3954 p4338 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h34976 : (¬ p1990) ∨ p2027 ∨ p2114 ∨ (¬ p2210) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3954) ∨ (¬ p4338))
    : (¬ p2210) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3954) ∨ (¬ p4338) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h34976 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60219 (p2027 p3073 p3201 p3449 p3540 p3874 p3905 p4347 p4384 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h34977 : p2027 ∨ (¬ p3073) ∨ (¬ p3201) ∨ (¬ p3449) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p4736))
    : (¬ p3073) ∨ (¬ p3201) ∨ (¬ p3449) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h34977 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60224 (p1975 p2027 p2553 p2598 p2633 p2819 p3486 p3555 p3570 p3956 p4375 p4733 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h34982 : (¬ p1975) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2598) ∨ p2633 ∨ (¬ p2819) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p3956) ∨ (¬ p4375) ∨ (¬ p4733))
    : (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2819) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p3956) ∨ (¬ p4375) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p1975 := h2135;
    let u10 : (¬ p2027) := h40810;
    let u11 : (¬ p2633) := h40879;
    (Or.elim h34982 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u11 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (False.elim (r10 u8)))))))))))))))))))))))))

theorem step60226 (p2027 p2187 p2641 p3958 p3984 p4360 p4769 : Prop)
    (h40810 : (¬ p2027))
    (h34984 : p2027 ∨ (¬ p2187) ∨ (¬ p2641) ∨ (¬ p3958) ∨ (¬ p3984) ∨ (¬ p4360) ∨ (¬ p4769))
    : (¬ p2187) ∨ (¬ p2641) ∨ (¬ p3958) ∨ (¬ p3984) ∨ (¬ p4360) ∨ (¬ p4769) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h34984 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60231 (p2027 p2246 p2437 p2608 p2651 p2744 p2911 p3591 p3923 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h34990 : p2027 ∨ (¬ p2246) ∨ (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2911) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4503))
    : (¬ p2246) ∨ (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2911) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h34990 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60232 (p2027 p2138 p3093 p3319 p3461 p3694 p4736 p5123 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h34992 : p2027 ∨ (¬ p2138) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3694) ∨ (¬ p4736) ∨ (¬ p5123) ∨ (¬ p5568))
    : (¬ p2138) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3694) ∨ (¬ p4736) ∨ (¬ p5123) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h34992 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60233 (p1992 p2027 p2132 p2780 p3128 p3583 p3917 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40894 : (¬ p3128))
    (h34993 : (¬ p1992) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2780) ∨ p3128 ∨ (¬ p3583) ∨ (¬ p3917))
    : (¬ p2132) ∨ (¬ p2780) ∨ (¬ p3583) ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3128) := h40894;
    (Or.elim h34993 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60234 (p2027 p2459 p2476 p2534 p3063 p3093 p3347 p3954 p4133 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h34995 : p2027 ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p4133) ∨ (¬ p5216))
    : (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p4133) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h34995 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60237 (p2027 p2663 p2774 p3363 p3414 p3585 p3609 p3945 p3947 p4133 p4347 p4737 p4861 : Prop)
    (h40810 : (¬ p2027))
    (h34999 : p2027 ∨ (¬ p2663) ∨ (¬ p2774) ∨ (¬ p3363) ∨ (¬ p3414) ∨ (¬ p3585) ∨ (¬ p3609) ∨ (¬ p3945) ∨ (¬ p3947) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4737) ∨ (¬ p4861))
    : (¬ p2663) ∨ (¬ p2774) ∨ (¬ p3363) ∨ (¬ p3414) ∨ (¬ p3585) ∨ (¬ p3609) ∨ (¬ p3945) ∨ (¬ p3947) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4737) ∨ (¬ p4861) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2663 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4861 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h34999 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step60238 (p1979 p2027 p2187 p2765 p2946 p2963 p3324 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h35000 : (¬ p1979) ∨ p2027 ∨ (¬ p2187) ∨ p2765 ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3324))
    : (¬ p2187) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3324) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1979 := h2139;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h35000 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60241 (p1994 p2027 p2630 p2748 p2997 p3097 p3662 p3952 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h35003 : (¬ p1994) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p2748) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3662) ∨ (¬ p3952))
    : (¬ p2630) ∨ (¬ p2748) ∨ (¬ p3097) ∨ (¬ p3662) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h35003 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60242 (p1994 p2027 p2630 p2997 p3097 p3952 p4315 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h35004 : (¬ p1994) ∨ p2027 ∨ (¬ p2630) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p4315))
    : (¬ p2630) ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h35004 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60244 (p2027 p2246 p2352 p2608 p2651 p2744 p3016 p3549 p3591 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h35006 : p2027 ∨ (¬ p2246) ∨ (¬ p2352) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4405))
    : (¬ p2246) ∨ (¬ p2352) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35006 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60249 (p2027 p2589 p2608 p2819 p2829 p3097 p4110 p4405 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h35011 : p2027 ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4405) ∨ (¬ p5193))
    : (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4405) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35011 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60255 (p1991 p2027 p2589 p2655 p2850 p3096 p3584 p4206 p4393 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40913 : (¬ p4206))
    (h35017 : (¬ p1991) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3584) ∨ p4206 ∨ (¬ p4393))
    : (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3584) ∨ (¬ p4393) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1991 := h2151;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p4206) := h40913;
    (Or.elim h35017 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step60264 (p2027 p3146 p3266 p3773 p4455 p4529 : Prop)
    (h40810 : (¬ p2027))
    (h35027 : p2027 ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3773) ∨ (¬ p4455) ∨ (¬ p4529))
    : (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3773) ∨ (¬ p4455) ∨ (¬ p4529) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4455 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4529 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35027 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60265 (p1997 p2027 p2406 p2476 p2499 p2573 p3498 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40899 : (¬ p3498))
    (h35028 : (¬ p1997) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2476) ∨ (¬ p2499) ∨ (¬ p2573) ∨ p3498)
    : (¬ p2406) ∨ (¬ p2476) ∨ (¬ p2499) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3498) := h40899;
    (Or.elim h35028 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step60266 (p2027 p3146 p3189 p3848 p4132 p4550 p5107 : Prop)
    (h40810 : (¬ p2027))
    (h35029 : p2027 ∨ (¬ p3146) ∨ (¬ p3189) ∨ (¬ p3848) ∨ (¬ p4132) ∨ (¬ p4550) ∨ (¬ p5107))
    : (¬ p3146) ∨ (¬ p3189) ∨ (¬ p3848) ∨ (¬ p4132) ∨ (¬ p4550) ∨ (¬ p5107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35029 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60269 (p2027 p2668 p2727 p3923 p4245 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h35034 : p2027 ∨ (¬ p2668) ∨ (¬ p2727) ∨ (¬ p3923) ∨ (¬ p4245) ∨ (¬ p4972))
    : (¬ p2668) ∨ (¬ p2727) ∨ (¬ p3923) ∨ (¬ p4245) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35034 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60278 (p1976 p2027 p2417 p2914 p3365 p3572 p3947 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h35043 : (¬ p1976) ∨ p2027 ∨ (¬ p2417) ∨ p2914 ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947))
    : (¬ p2417) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h35043 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60280 (p2027 p2589 p2922 p3347 p3569 p4110 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h35045 : p2027 ∨ (¬ p2589) ∨ (¬ p2922) ∨ (¬ p3347) ∨ (¬ p3569) ∨ (¬ p4110) ∨ (¬ p4558))
    : (¬ p2589) ∨ (¬ p2922) ∨ (¬ p3347) ∨ (¬ p3569) ∨ (¬ p4110) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35045 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60283 (p2027 p2132 p2192 p2274 p2743 p2963 p3324 p3361 p4418 p4501 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h35048 : p2027 ∨ (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3361) ∨ (¬ p4418) ∨ (¬ p4501) ∨ (¬ p4737))
    : (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3361) ∨ (¬ p4418) ∨ (¬ p4501) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35048 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60284 (p2027 p2132 p2192 p2274 p2743 p2963 p3361 p4037 p4418 p4620 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h35049 : p2027 ∨ (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p4037) ∨ (¬ p4418) ∨ (¬ p4620) ∨ (¬ p4737))
    : (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p4037) ∨ (¬ p4418) ∨ (¬ p4620) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35049 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60285 (p2027 p2138 p3063 p3093 p3692 p3694 p3979 p4736 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h35050 : p2027 ∨ (¬ p2138) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3979) ∨ (¬ p4736) ∨ (¬ p5122))
    : (¬ p2138) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3979) ∨ (¬ p4736) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35050 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60287 (p1977 p2027 p2662 p2766 p3266 p3346 p4111 p4425 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h35054 : (¬ p1977) ∨ p2027 ∨ (¬ p2662) ∨ p2766 ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p4111) ∨ (¬ p4425))
    : (¬ p2662) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p4111) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h35054 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60290 (p2027 p3680 p4107 p4192 p4381 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h35057 : p2027 ∨ (¬ p3680) ∨ (¬ p4107) ∨ (¬ p4192) ∨ (¬ p4381) ∨ (¬ p4559))
    : (¬ p3680) ∨ (¬ p4107) ∨ (¬ p4192) ∨ (¬ p4381) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35057 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60294 (p1977 p2027 p2766 p2957 p3266 p3551 p3657 p3662 p4381 p4984 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h35062 : (¬ p1977) ∨ p2027 ∨ p2766 ∨ (¬ p2957) ∨ (¬ p3266) ∨ (¬ p3551) ∨ (¬ p3657) ∨ (¬ p3662) ∨ (¬ p4381) ∨ (¬ p4984))
    : (¬ p2957) ∨ (¬ p3266) ∨ (¬ p3551) ∨ (¬ p3657) ∨ (¬ p3662) ∨ (¬ p4381) ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p1977 := h2137;
    let u8 : (¬ p2027) := h40810;
    let u9 : (¬ p2766) := h40884;
    (Or.elim h35062 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u9 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step60297 (p1976 p2027 p2938 p3055 p3367 p3583 p4244 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h35065 : (¬ p1976) ∨ p2027 ∨ p2938 ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p4244))
    : (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p4244) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h35065 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60300 (p1994 p2027 p2651 p2952 p2997 p3097 p3952 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h35068 : (¬ p1994) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2952) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3952))
    : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h35068 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60303 (p2027 p2255 p2662 p3166 p3256 p3540 p3644 p4111 p4133 p4347 : Prop)
    (h40810 : (¬ p2027))
    (h35072 : p2027 ∨ (¬ p2255) ∨ (¬ p2662) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4111) ∨ (¬ p4133) ∨ (¬ p4347))
    : (¬ p2255) ∨ (¬ p2662) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4111) ∨ (¬ p4133) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35072 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60308 (p1992 p2027 p2143 p2633 p3246 p3570 p3583 p3821 p4984 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35079 : (¬ p1992) ∨ p2027 ∨ (¬ p2143) ∨ p2633 ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p3821) ∨ (¬ p4984))
    : (¬ p2143) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p3821) ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1992 := h2152;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2633) := h40879;
    (Or.elim h35079 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step60313 (p2027 p2493 p3379 p3556 p3564 p3570 p4330 p4348 p4524 : Prop)
    (h40810 : (¬ p2027))
    (h35085 : p2027 ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3556) ∨ (¬ p3564) ∨ (¬ p3570) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4524))
    : (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3556) ∨ (¬ p3564) ∨ (¬ p3570) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4524) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4524 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35085 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60316 (p1979 p2027 p2842 p2992 p3483 p4037 p4154 p4375 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h35088 : (¬ p1979) ∨ p2027 ∨ p2842 ∨ (¬ p2992) ∨ (¬ p3483) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4375))
    : (¬ p2992) ∨ (¬ p3483) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4375) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1979 := h2139;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2842) := h40885;
    (Or.elim h35088 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60317 (p1979 p2027 p2169 p2992 p2996 p3646 p3989 p4155 p4988 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h35089 : (¬ p1979) ∨ p2027 ∨ p2169 ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4155) ∨ (¬ p4988))
    : (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4155) ∨ (¬ p4988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1979 := h2139;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2169) := h40866;
    (Or.elim h35089 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step60321 (p2027 p2274 p2313 p2534 p3073 p3379 p3989 p4198 p4524 p4596 p4688 : Prop)
    (h40810 : (¬ p2027))
    (h35093 : p2027 ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2534) ∨ (¬ p3073) ∨ (¬ p3379) ∨ (¬ p3989) ∨ (¬ p4198) ∨ (¬ p4524) ∨ (¬ p4596) ∨ (¬ p4688))
    : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2534) ∨ (¬ p3073) ∨ (¬ p3379) ∨ (¬ p3989) ∨ (¬ p4198) ∨ (¬ p4524) ∨ (¬ p4596) ∨ (¬ p4688) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4524 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35093 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60323 (p1985 p2027 p2177 p2210 p2699 p3309 p3570 p4338 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h35096 : (¬ p1985) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2210) ∨ p2699 ∨ (¬ p3309) ∨ (¬ p3570) ∨ (¬ p4338))
    : (¬ p2177) ∨ (¬ p2210) ∨ (¬ p3309) ∨ (¬ p3570) ∨ (¬ p4338) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1985 := h2145;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h35096 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60324 (p2005 p2027 p2274 p2588 p2766 p3989 p4138 p4348 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h35097 : (¬ p2005) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2588) ∨ p2766 ∨ (¬ p3989) ∨ (¬ p4138) ∨ (¬ p4348))
    : (¬ p2274) ∨ (¬ p2588) ∨ (¬ p3989) ∨ (¬ p4138) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2005 := h2165;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h35097 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60334 (p2027 p2476 p2493 p2553 p3347 p4432 p4501 : Prop)
    (h40810 : (¬ p2027))
    (h35109 : p2027 ∨ (¬ p2476) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p3347) ∨ (¬ p4432) ∨ (¬ p4501))
    : (¬ p2476) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p3347) ∨ (¬ p4432) ∨ (¬ p4501) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35109 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60337 (p2027 p2177 p2255 p2295 p2331 p2662 p3540 p4111 p4278 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h35113 : p2027 ∨ (¬ p2177) ∨ (¬ p2255) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p4666))
    : (¬ p2177) ∨ (¬ p2255) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35113 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60342 (p2027 p2255 p2331 p2662 p3309 p3346 p3791 p4111 p4319 p4425 p4826 : Prop)
    (h40810 : (¬ p2027))
    (h35118 : p2027 ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3309) ∨ (¬ p3346) ∨ (¬ p3791) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p4425) ∨ (¬ p4826))
    : (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3309) ∨ (¬ p3346) ∨ (¬ p3791) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p4425) ∨ (¬ p4826) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35118 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60343 (p1994 p2027 p2202 p2563 p2727 p2957 p3646 p3662 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h35119 : (¬ p1994) ∨ p2027 ∨ p2202 ∨ (¬ p2563) ∨ (¬ p2727) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662))
    : (¬ p2563) ∨ (¬ p2727) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h35119 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60346 (p1977 p2027 p2313 p2459 p2577 p2633 p2662 p3955 p4111 p4347 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35123 : (¬ p1977) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p2459) ∨ (¬ p2577) ∨ p2633 ∨ (¬ p2662) ∨ (¬ p3955) ∨ (¬ p4111) ∨ (¬ p4347))
    : (¬ p2313) ∨ (¬ p2459) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p3955) ∨ (¬ p4111) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p1977 := h2137;
    let u8 : (¬ p2027) := h40810;
    let u9 : (¬ p2633) := h40879;
    (Or.elim h35123 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u9 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step60349 (p1979 p2027 p2166 p2253 p2651 p2699 p4111 p4119 p4320 p4365 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h35128 : (¬ p1979) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2253) ∨ (¬ p2651) ∨ p2699 ∨ (¬ p4111) ∨ (¬ p4119) ∨ (¬ p4320) ∨ (¬ p4365))
    : (¬ p2166) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p4111) ∨ (¬ p4119) ∨ (¬ p4320) ∨ (¬ p4365) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p1979 := h2139;
    let u8 : (¬ p2027) := h40810;
    let u9 : (¬ p2699) := h40881;
    (Or.elim h35128 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u9 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step60353 (p1979 p2027 p2764 p3051 p4032 p4320 p4322 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h35132 : (¬ p1979) ∨ p2027 ∨ p2764 ∨ (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4320) ∨ (¬ p4322))
    : (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4320) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1979 := h2139;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h35132 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60360 (p2027 p2177 p2274 p3581 p3644 p3958 : Prop)
    (h40810 : (¬ p2027))
    (h35142 : p2027 ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p3958))
    : (¬ p2177) ∨ (¬ p2274) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p3958) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35142 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60361 (p2027 p2641 p3742 p3984 p4111 p4708 : Prop)
    (h40810 : (¬ p2027))
    (h35143 : p2027 ∨ (¬ p2641) ∨ (¬ p3742) ∨ (¬ p3984) ∨ (¬ p4111) ∨ (¬ p4708))
    : (¬ p2641) ∨ (¬ p3742) ∨ (¬ p3984) ∨ (¬ p4111) ∨ (¬ p4708) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4708 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35143 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60365 (p1977 p2027 p2563 p2938 p2957 p3646 p3662 p4235 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h35149 : (¬ p1977) ∨ p2027 ∨ (¬ p2563) ∨ p2938 ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p4235))
    : (¬ p2563) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2938) := h40888;
    (Or.elim h35149 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60366 (p2027 p2166 p2210 p2780 p3917 p3969 p4191 p4736 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h35150 : p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2780) ∨ (¬ p3917) ∨ (¬ p3969) ∨ (¬ p4191) ∨ (¬ p4736) ∨ (¬ p5119))
    : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2780) ∨ (¬ p3917) ∨ (¬ p3969) ∨ (¬ p4191) ∨ (¬ p4736) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35150 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60368 (p2027 p2318 p2510 p2528 p3097 p3857 p3961 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h35152 : p2027 ∨ (¬ p2318) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p3097) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4718))
    : (¬ p2318) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p3097) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35152 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60369 (p2027 p2255 p2311 p2651 p2667 p3222 p3276 p3551 p4116 p4154 p5123 p5558 : Prop)
    (h40810 : (¬ p2027))
    (h35153 : p2027 ∨ (¬ p2255) ∨ (¬ p2311) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3551) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p5123) ∨ (¬ p5558))
    : (¬ p2255) ∨ (¬ p2311) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3551) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p5123) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h35153 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step60370 (p2027 p2177 p2255 p2311 p2651 p2667 p3233 p3551 p3707 p4116 p4154 p4276 p4425 p4635 : Prop)
    (h40810 : (¬ p2027))
    (h35154 : p2027 ∨ (¬ p2177) ∨ (¬ p2255) ∨ (¬ p2311) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (¬ p3233) ∨ (¬ p3551) ∨ (¬ p3707) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p4276) ∨ (¬ p4425) ∨ (¬ p4635))
    : (¬ p2177) ∨ (¬ p2255) ∨ (¬ p2311) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (¬ p3233) ∨ (¬ p3551) ∨ (¬ p3707) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p4276) ∨ (¬ p4425) ∨ (¬ p4635) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : (¬ p2027) := h40810;
    (Or.elim h35154 (fun q0 => (False.elim (u13 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u11))) (fun r12 => (False.elim (r12 u12)))))))))))))))))))))))))))))

theorem step60371 (p2027 p2589 p3389 p3569 p4320 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h35155 : p2027 ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3569) ∨ (¬ p4320) ∨ (¬ p4702))
    : (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3569) ∨ (¬ p4320) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35155 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60374 (p2020 p2027 p2608 p2619 p2699 p2839 p3969 : Prop)
    (h2180 : p2020)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h35158 : (¬ p2020) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2619) ∨ p2699 ∨ (¬ p2839) ∨ (¬ p3969))
    : (¬ p2608) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p3969) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2020 := h2180;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h35158 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60377 (p2003 p2027 p2177 p2311 p2997 p3434 p3659 p3821 : Prop)
    (h2163 : p2003)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h35162 : (¬ p2003) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2311) ∨ p2997 ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3821))
    : (¬ p2177) ∨ (¬ p2311) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3821) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2003 := h2163;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h35162 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60386 (p1980 p2027 p2699 p2797 p3399 p3527 p3659 p4357 : Prop)
    (h2140 : p1980)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h35176 : (¬ p1980) ∨ p2027 ∨ p2699 ∨ (¬ p2797) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p4357))
    : (¬ p2797) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p4357) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1980 := h2140;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h35176 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60387 (p2027 p2313 p2651 p2667 p2745 p2811 p2972 p3680 p3948 p4116 p4154 p4260 p4831 : Prop)
    (h40810 : (¬ p2027))
    (h35178 : p2027 ∨ (¬ p2313) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (¬ p2745) ∨ (¬ p2811) ∨ (¬ p2972) ∨ (¬ p3680) ∨ (¬ p3948) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p4260) ∨ (¬ p4831))
    : (¬ p2313) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (¬ p2745) ∨ (¬ p2811) ∨ (¬ p2972) ∨ (¬ p3680) ∨ (¬ p3948) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p4260) ∨ (¬ p4831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h35178 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step60388 (p1977 p2027 p2299 p2633 p2996 p3791 p4155 p4372 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35179 : (¬ p1977) ∨ p2027 ∨ (¬ p2299) ∨ p2633 ∨ (¬ p2996) ∨ (¬ p3791) ∨ (¬ p4155) ∨ (¬ p4372))
    : (¬ p2299) ∨ (¬ p2996) ∨ (¬ p3791) ∨ (¬ p4155) ∨ (¬ p4372) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h35179 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60390 (p2027 p2274 p2312 p3527 p3546 p3659 p3689 p4889 : Prop)
    (h40810 : (¬ p2027))
    (h35181 : p2027 ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p3527) ∨ (¬ p3546) ∨ (¬ p3659) ∨ (¬ p3689) ∨ (¬ p4889))
    : (¬ p2274) ∨ (¬ p2312) ∨ (¬ p3527) ∨ (¬ p3546) ∨ (¬ p3659) ∨ (¬ p3689) ∨ (¬ p4889) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3689 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35181 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60393 (p2027 p3027 p3497 p3662 p4333 p4901 : Prop)
    (h40810 : (¬ p2027))
    (h35185 : p2027 ∨ (¬ p3027) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4333) ∨ (¬ p4901))
    : (¬ p3027) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4333) ∨ (¬ p4901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3027 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35185 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60395 (p2027 p2255 p2662 p2807 p3032 p3346 p3527 p3941 p4111 p4425 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h35187 : p2027 ∨ (¬ p2255) ∨ (¬ p2662) ∨ (¬ p2807) ∨ (¬ p3032) ∨ (¬ p3346) ∨ (¬ p3527) ∨ (¬ p3941) ∨ (¬ p4111) ∨ (¬ p4425) ∨ (¬ p5119))
    : (¬ p2255) ∨ (¬ p2662) ∨ (¬ p2807) ∨ (¬ p3032) ∨ (¬ p3346) ∨ (¬ p3527) ∨ (¬ p3941) ∨ (¬ p4111) ∨ (¬ p4425) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35187 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60396 (p2027 p2819 p3644 p3822 p4170 p4276 p4403 : Prop)
    (h40810 : (¬ p2027))
    (h35188 : p2027 ∨ (¬ p2819) ∨ (¬ p3644) ∨ (¬ p3822) ∨ (¬ p4170) ∨ (¬ p4276) ∨ (¬ p4403))
    : (¬ p2819) ∨ (¬ p3644) ∨ (¬ p3822) ∨ (¬ p4170) ∨ (¬ p4276) ∨ (¬ p4403) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35188 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60397 (p2027 p2255 p2331 p2662 p3063 p3346 p3979 p4111 p4319 p4425 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h35189 : p2027 ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p3346) ∨ (¬ p3979) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p4425) ∨ (¬ p5119))
    : (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p3346) ∨ (¬ p3979) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p4425) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35189 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60398 (p2027 p2253 p2387 p2651 p3189 p3609 p4111 p4347 p4969 p5021 : Prop)
    (h40810 : (¬ p2027))
    (h35190 : p2027 ∨ (¬ p2253) ∨ (¬ p2387) ∨ (¬ p2651) ∨ (¬ p3189) ∨ (¬ p3609) ∨ (¬ p4111) ∨ (¬ p4347) ∨ (¬ p4969) ∨ (¬ p5021))
    : (¬ p2253) ∨ (¬ p2387) ∨ (¬ p2651) ∨ (¬ p3189) ∨ (¬ p3609) ∨ (¬ p4111) ∨ (¬ p4347) ∨ (¬ p4969) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35190 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60399 (p2027 p2255 p2331 p2363 p2476 p2662 p3063 p3693 p4111 p4319 p5118 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h35191 : p2027 ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p3693) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p5118) ∨ (¬ p5568))
    : (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p3693) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p5118) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h35191 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step60401 (p2027 p2191 p2255 p2946 p3156 p3368 : Prop)
    (h40810 : (¬ p2027))
    (h35193 : p2027 ∨ (¬ p2191) ∨ (¬ p2255) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3368))
    : (¬ p2191) ∨ (¬ p2255) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3368) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35193 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60402 (p2027 p2449 p2995 p3569 p3952 p4278 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h35194 : p2027 ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3569) ∨ (¬ p3952) ∨ (¬ p4278) ∨ (¬ p4558))
    : (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3569) ∨ (¬ p3952) ∨ (¬ p4278) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35194 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60407 (p2027 p2441 p2449 p2870 p3699 p4278 p4885 : Prop)
    (h40810 : (¬ p2027))
    (h35199 : p2027 ∨ (¬ p2441) ∨ (¬ p2449) ∨ (¬ p2870) ∨ (¬ p3699) ∨ (¬ p4278) ∨ (¬ p4885))
    : (¬ p2441) ∨ (¬ p2449) ∨ (¬ p2870) ∨ (¬ p3699) ∨ (¬ p4278) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35199 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60412 (p2027 p2253 p2651 p2780 p3222 p3276 p3822 p4116 p4260 p4736 p4831 : Prop)
    (h40810 : (¬ p2027))
    (h35208 : p2027 ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3822) ∨ (¬ p4116) ∨ (¬ p4260) ∨ (¬ p4736) ∨ (¬ p4831))
    : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3822) ∨ (¬ p4116) ∨ (¬ p4260) ∨ (¬ p4736) ∨ (¬ p4831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35208 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60416 (p1994 p2027 p2299 p2313 p2633 p2667 p2727 p4154 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35213 : (¬ p1994) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2313) ∨ p2633 ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p4154))
    : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h35213 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60423 (p2027 p2331 p2657 p3584 p3984 p4750 : Prop)
    (h40810 : (¬ p2027))
    (h35224 : p2027 ∨ (¬ p2331) ∨ (¬ p2657) ∨ (¬ p3584) ∨ (¬ p3984) ∨ (¬ p4750))
    : (¬ p2331) ∨ (¬ p2657) ∨ (¬ p3584) ∨ (¬ p3984) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35224 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60424 (p1987 p2027 p2579 p2662 p2764 p2810 p4137 p4191 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h35225 : (¬ p1987) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p2662) ∨ p2764 ∨ (¬ p2810) ∨ (¬ p4137) ∨ (¬ p4191))
    : (¬ p2579) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p4137) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h35225 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60426 (p1997 p2027 p2298 p2299 p2542 p2633 p2727 p2996 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35227 : (¬ p1997) ∨ p2027 ∨ (¬ p2298) ∨ (¬ p2299) ∨ (¬ p2542) ∨ p2633 ∨ (¬ p2727) ∨ (¬ p2996))
    : (¬ p2298) ∨ (¬ p2299) ∨ (¬ p2542) ∨ (¬ p2727) ∨ (¬ p2996) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2298 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h35227 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60427 (p1994 p2027 p2299 p2633 p3422 p3574 p3876 p3921 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35228 : (¬ p1994) ∨ p2027 ∨ (¬ p2299) ∨ p2633 ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p3876) ∨ (¬ p3921))
    : (¬ p2299) ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p3876) ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h35228 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60432 (p2005 p2027 p2573 p2633 p2656 p2727 p2996 p3553 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35234 : (¬ p2005) ∨ p2027 ∨ (¬ p2573) ∨ p2633 ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3553))
    : (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2005 := h2165;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h35234 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60433 (p2027 p2641 p2657 p2807 p2996 p4975 : Prop)
    (h40810 : (¬ p2027))
    (h35235 : p2027 ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p4975))
    : (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35235 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60434 (p2027 p2641 p2657 p3166 p4360 p4975 : Prop)
    (h40810 : (¬ p2027))
    (h35236 : p2027 ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p4360) ∨ (¬ p4975))
    : (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p4360) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35236 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60438 (p2027 p2191 p2641 p3156 p3368 p4566 : Prop)
    (h40810 : (¬ p2027))
    (h35240 : p2027 ∨ (¬ p2191) ∨ (¬ p2641) ∨ (¬ p3156) ∨ (¬ p3368) ∨ (¬ p4566))
    : (¬ p2191) ∨ (¬ p2641) ∨ (¬ p3156) ∨ (¬ p3368) ∨ (¬ p4566) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4566 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35240 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60439 (p2027 p2331 p2685 p2810 p3414 p4975 : Prop)
    (h40810 : (¬ p2027))
    (h35241 : p2027 ∨ (¬ p2331) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3414) ∨ (¬ p4975))
    : (¬ p2331) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3414) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35241 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60443 (p2027 p2230 p2373 p2748 p2996 p3365 p3367 p3553 p3759 p4734 p4902 : Prop)
    (h40810 : (¬ p2027))
    (h35245 : p2027 ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2748) ∨ (¬ p2996) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3553) ∨ (¬ p3759) ∨ (¬ p4734) ∨ (¬ p4902))
    : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2748) ∨ (¬ p2996) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3553) ∨ (¬ p3759) ∨ (¬ p4734) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35245 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60444 (p2027 p2579 p2641 p2659 p3984 p4111 : Prop)
    (h40810 : (¬ p2027))
    (h35247 : p2027 ∨ (¬ p2579) ∨ (¬ p2641) ∨ (¬ p2659) ∨ (¬ p3984) ∨ (¬ p4111))
    : (¬ p2579) ∨ (¬ p2641) ∨ (¬ p2659) ∨ (¬ p3984) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35247 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60447 (p2027 p2331 p3027 p3414 p4111 p4975 : Prop)
    (h40810 : (¬ p2027))
    (h35250 : p2027 ∨ (¬ p2331) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111) ∨ (¬ p4975))
    : (¬ p2331) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35250 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60453 (p2027 p3093 p3246 p3309 p3365 p3553 p3572 p4275 p4668 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h35256 : p2027 ∨ (¬ p3093) ∨ (¬ p3246) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4275) ∨ (¬ p4668) ∨ (¬ p4736))
    : (¬ p3093) ∨ (¬ p3246) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4275) ∨ (¬ p4668) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35256 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60461 (p2027 p2241 p2459 p2476 p2534 p2641 p2668 p4133 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h35266 : p2027 ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p4133) ∨ (¬ p5193))
    : (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p4133) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35266 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60462 (p1977 p2027 p2298 p2299 p2331 p2633 p3414 p4154 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35267 : (¬ p1977) ∨ p2027 ∨ (¬ p2298) ∨ (¬ p2299) ∨ (¬ p2331) ∨ p2633 ∨ (¬ p3414) ∨ (¬ p4154))
    : (¬ p2298) ∨ (¬ p2299) ∨ (¬ p2331) ∨ (¬ p3414) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2298 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h35267 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60465 (p2027 p2138 p2352 p2573 p3367 p3486 p3570 p3759 p4133 p4243 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h35270 : p2027 ∨ (¬ p2138) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p3759) ∨ (¬ p4133) ∨ (¬ p4243) ∨ (¬ p4734))
    : (¬ p2138) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p3759) ∨ (¬ p4133) ∨ (¬ p4243) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35270 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60467 (p2027 p2247 p2744 p3063 p3093 p3201 p3366 p3540 p3874 p3905 p4384 : Prop)
    (h40810 : (¬ p2027))
    (h35272 : p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3201) ∨ (¬ p3366) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4384))
    : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3201) ∨ (¬ p3366) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4384) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35272 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60469 (p2027 p3918 p4075 p4358 p4452 p4501 p4710 p5503 : Prop)
    (h40810 : (¬ p2027))
    (h35274 : p2027 ∨ (¬ p3918) ∨ (¬ p4075) ∨ (¬ p4358) ∨ (¬ p4452) ∨ (¬ p4501) ∨ (¬ p4710) ∨ (¬ p5503))
    : (¬ p3918) ∨ (¬ p4075) ∨ (¬ p4358) ∨ (¬ p4452) ∨ (¬ p4501) ∨ (¬ p4710) ∨ (¬ p5503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3918 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35274 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60472 (p2027 p2241 p2295 p2641 p2881 p3540 p3644 p4559 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h35277 : p2027 ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2881) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4559) ∨ (¬ p5193))
    : (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2881) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4559) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35277 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60474 (p1994 p2027 p2299 p2633 p2651 p2963 p3549 p3922 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35279 : (¬ p1994) ∨ p2027 ∨ (¬ p2299) ∨ p2633 ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3549) ∨ (¬ p3922))
    : (¬ p2299) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3549) ∨ (¬ p3922) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h35279 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60475 (p2027 p2098 p2499 p3452 p3609 p3660 p3880 p4348 p4733 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h35280 : p2027 ∨ (¬ p2098) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3660) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4733) ∨ (¬ p4905))
    : (¬ p2098) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3660) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4733) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35280 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60477 (p2027 p2542 p2573 p3540 p3574 p4635 p4949 : Prop)
    (h40810 : (¬ p2027))
    (h35282 : p2027 ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p4635) ∨ (¬ p4949))
    : (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p4635) ∨ (¬ p4949) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35282 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60487 (p2027 p2245 p2417 p2598 p3201 p3292 p3680 p3853 p3951 p4321 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h35292 : p2027 ∨ (¬ p2245) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3292) ∨ (¬ p3680) ∨ (¬ p3853) ∨ (¬ p3951) ∨ (¬ p4321) ∨ (¬ p4733))
    : (¬ p2245) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3292) ∨ (¬ p3680) ∨ (¬ p3853) ∨ (¬ p3951) ∨ (¬ p4321) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35292 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60489 (p2027 p2144 p2191 p2220 p3365 p4030 p4202 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h35294 : p2027 ∨ (¬ p2144) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p3365) ∨ (¬ p4030) ∨ (¬ p4202) ∨ (¬ p4752))
    : (¬ p2144) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p3365) ∨ (¬ p4030) ∨ (¬ p4202) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35294 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60492 (p2027 p2247 p2744 p3055 p3063 p3093 p3366 p3644 p3876 p4133 : Prop)
    (h40810 : (¬ p2027))
    (h35297 : p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133))
    : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35297 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60494 (p2027 p2247 p2579 p2744 p3073 p3366 p3449 p3905 p3956 p5118 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h35300 : p2027 ∨ (¬ p2247) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3905) ∨ (¬ p3956) ∨ (¬ p5118) ∨ (¬ p5580))
    : (¬ p2247) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3905) ∨ (¬ p3956) ∨ (¬ p5118) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35300 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60499 (p2027 p2230 p2274 p2284 p2717 p3548 p3879 p3954 p4400 p4477 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h35305 : p2027 ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2717) ∨ (¬ p3548) ∨ (¬ p3879) ∨ (¬ p3954) ∨ (¬ p4400) ∨ (¬ p4477) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2717) ∨ (¬ p3548) ∨ (¬ p3879) ∨ (¬ p3954) ∨ (¬ p4400) ∨ (¬ p4477) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35305 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60501 (p2027 p2104 p2230 p2274 p2284 p3537 p3588 p3873 p3879 p4477 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h35308 : p2027 ∨ (¬ p2104) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p3879) ∨ (¬ p4477) ∨ (¬ p5190))
    : (¬ p2104) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p3879) ∨ (¬ p4477) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35308 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60502 (p2027 p2230 p2373 p3146 p3588 p3954 p4324 p4669 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h35309 : p2027 ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4669) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4669) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35309 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60505 (p2027 p2088 p2499 p2860 p3452 p3660 p4235 p4340 p4359 p4555 p4590 p5207 : Prop)
    (h40810 : (¬ p2027))
    (h35315 : p2027 ∨ (¬ p2088) ∨ (¬ p2499) ∨ (¬ p2860) ∨ (¬ p3452) ∨ (¬ p3660) ∨ (¬ p4235) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4555) ∨ (¬ p4590) ∨ (¬ p5207))
    : (¬ p2088) ∨ (¬ p2499) ∨ (¬ p2860) ∨ (¬ p3452) ∨ (¬ p3660) ∨ (¬ p4235) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4555) ∨ (¬ p4590) ∨ (¬ p5207) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h35315 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step60506 (p2027 p2230 p2284 p3737 p3879 p3954 p4379 p5190 p5250 p5387 : Prop)
    (h40810 : (¬ p2027))
    (h35316 : p2027 ∨ (¬ p2230) ∨ (¬ p2284) ∨ (¬ p3737) ∨ (¬ p3879) ∨ (¬ p3954) ∨ (¬ p4379) ∨ (¬ p5190) ∨ (¬ p5250) ∨ (¬ p5387))
    : (¬ p2230) ∨ (¬ p2284) ∨ (¬ p3737) ∨ (¬ p3879) ∨ (¬ p3954) ∨ (¬ p4379) ∨ (¬ p5190) ∨ (¬ p5250) ∨ (¬ p5387) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35316 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60507 (p1997 p2027 p2542 p2633 p3246 p3359 p3570 p4636 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35317 : (¬ p1997) ∨ p2027 ∨ (¬ p2542) ∨ p2633 ∨ (¬ p3246) ∨ (¬ p3359) ∨ (¬ p3570) ∨ (¬ p4636))
    : (¬ p2542) ∨ (¬ p3246) ∨ (¬ p3359) ∨ (¬ p3570) ∨ (¬ p4636) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h35317 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60510 (p2027 p2136 p2573 p2870 p3083 p3556 p3574 p3694 p4158 p4419 : Prop)
    (h40810 : (¬ p2027))
    (h35320 : p2027 ∨ (¬ p2136) ∨ (¬ p2573) ∨ (¬ p2870) ∨ (¬ p3083) ∨ (¬ p3556) ∨ (¬ p3574) ∨ (¬ p3694) ∨ (¬ p4158) ∨ (¬ p4419))
    : (¬ p2136) ∨ (¬ p2573) ∨ (¬ p2870) ∨ (¬ p3083) ∨ (¬ p3556) ∨ (¬ p3574) ∨ (¬ p3694) ∨ (¬ p4158) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35320 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60513 (p2027 p2230 p2274 p2284 p3609 p3860 p3879 p4261 p4477 p4805 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h35323 : p2027 ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p3609) ∨ (¬ p3860) ∨ (¬ p3879) ∨ (¬ p4261) ∨ (¬ p4477) ∨ (¬ p4805) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p3609) ∨ (¬ p3860) ∨ (¬ p3879) ∨ (¬ p4261) ∨ (¬ p4477) ∨ (¬ p4805) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4805 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35323 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60514 (p1997 p2027 p2633 p3105 p3570 p4244 p4948 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35324 : (¬ p1997) ∨ p2027 ∨ p2633 ∨ (¬ p3105) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4948))
    : (¬ p3105) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h35324 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60515 (p2027 p2138 p2573 p3083 p3570 p3574 p4244 p4419 p4420 : Prop)
    (h40810 : (¬ p2027))
    (h35325 : p2027 ∨ (¬ p2138) ∨ (¬ p2573) ∨ (¬ p3083) ∨ (¬ p3570) ∨ (¬ p3574) ∨ (¬ p4244) ∨ (¬ p4419) ∨ (¬ p4420))
    : (¬ p2138) ∨ (¬ p2573) ∨ (¬ p3083) ∨ (¬ p3570) ∨ (¬ p3574) ∨ (¬ p4244) ∨ (¬ p4419) ∨ (¬ p4420) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35325 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60521 (p2027 p2230 p2440 p2531 p3083 p3588 p3659 p3954 p4902 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h35331 : p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p3083) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4902) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p3083) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4902) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35331 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60524 (p2027 p2341 p2459 p2499 p2707 p3055 p3577 p4030 p4137 p4604 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h35334 : p2027 ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2707) ∨ (¬ p3055) ∨ (¬ p3577) ∨ (¬ p4030) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4734))
    : (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2707) ∨ (¬ p3055) ∨ (¬ p3577) ∨ (¬ p4030) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35334 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60525 (p2027 p2331 p2751 p3027 p3414 p4195 : Prop)
    (h40810 : (¬ p2027))
    (h35335 : p2027 ∨ (¬ p2331) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4195))
    : (¬ p2331) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4195) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35335 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60532 (p2027 p2528 p3551 p3875 p4348 p5199 : Prop)
    (h40810 : (¬ p2027))
    (h35344 : p2027 ∨ (¬ p2528) ∨ (¬ p3551) ∨ (¬ p3875) ∨ (¬ p4348) ∨ (¬ p5199))
    : (¬ p2528) ∨ (¬ p3551) ∨ (¬ p3875) ∨ (¬ p4348) ∨ (¬ p5199) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5199 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35344 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60534 (p2027 p2246 p2573 p2608 p2663 p2744 p3343 p3574 p4324 p4366 p4424 p4638 : Prop)
    (h40810 : (¬ p2027))
    (h35346 : p2027 ∨ (¬ p2246) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4324) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p4638))
    : (¬ p2246) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4324) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p4638) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h35346 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step60542 (p1994 p2027 p2148 p2651 p2952 p3051 p4320 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h35354 : (¬ p1994) ∨ p2027 ∨ p2148 ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3051) ∨ (¬ p4320))
    : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3051) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2148) := h40865;
    (Or.elim h35354 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60546 (p1984 p2027 p2881 p2928 p2938 p3452 p3644 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h35358 : (¬ p1984) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p2928) ∨ p2938 ∨ (¬ p3452) ∨ (¬ p3644))
    : (¬ p2881) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p3644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h35358 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60549 (p2027 p2136 p2241 p2299 p2727 p3083 p3097 p3646 p4420 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h35361 : p2027 ∨ (¬ p2136) ∨ (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4420) ∨ (¬ p4736))
    : (¬ p2136) ∨ (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4420) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35361 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60553 (p1994 p2027 p2651 p2881 p2938 p3414 p3553 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h35365 : (¬ p1994) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2881) ∨ p2938 ∨ (¬ p3414) ∨ (¬ p3553))
    : (¬ p2651) ∨ (¬ p2881) ∨ (¬ p3414) ∨ (¬ p3553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h35365 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60554 (p2027 p2774 p3238 p3452 p3609 p3880 p4134 p4347 p4733 p4861 : Prop)
    (h40810 : (¬ p2027))
    (h35366 : p2027 ∨ (¬ p2774) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4733) ∨ (¬ p4861))
    : (¬ p2774) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4733) ∨ (¬ p4861) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4861 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35366 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60562 (p2027 p2177 p2249 p2295 p2641 p2657 p3238 p3487 p3880 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h35375 : p2027 ∨ (¬ p2177) ∨ (¬ p2249) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3238) ∨ (¬ p3487) ∨ (¬ p3880) ∨ (¬ p4905))
    : (¬ p2177) ∨ (¬ p2249) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3238) ∨ (¬ p3487) ∨ (¬ p3880) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35375 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60565 (p1987 p2027 p2641 p2651 p2688 p2810 p2963 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h35378 : (¬ p1987) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2651) ∨ p2688 ∨ (¬ p2810) ∨ (¬ p2963))
    : (¬ p2641) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h35378 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60580 (p2027 p2751 p3309 p3568 p4195 p4759 : Prop)
    (h40810 : (¬ p2027))
    (h35400 : p2027 ∨ (¬ p2751) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4759))
    : (¬ p2751) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35400 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60581 (p2027 p2248 p2499 p3166 p3256 p3266 p3452 p5254 p5514 : Prop)
    (h40810 : (¬ p2027))
    (h35401 : p2027 ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3452) ∨ (¬ p5254) ∨ (¬ p5514))
    : (¬ p2248) ∨ (¬ p2499) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3452) ∨ (¬ p5254) ∨ (¬ p5514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35401 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60583 (p2027 p2156 p3737 p3880 p4109 p4506 p5586 : Prop)
    (h40810 : (¬ p2027))
    (h35403 : p2027 ∨ (¬ p2156) ∨ (¬ p3737) ∨ (¬ p3880) ∨ (¬ p4109) ∨ (¬ p4506) ∨ (¬ p5586))
    : (¬ p2156) ∨ (¬ p3737) ∨ (¬ p3880) ∨ (¬ p4109) ∨ (¬ p4506) ∨ (¬ p5586) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35403 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60584 (p2027 p2341 p2459 p3919 p4118 p4854 : Prop)
    (h40810 : (¬ p2027))
    (h35404 : p2027 ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4854))
    : (¬ p2341) ∨ (¬ p2459) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4854) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4854 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35404 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60597 (p2027 p2088 p2249 p2641 p2657 p2928 p3487 p3567 p3644 p4114 p4133 p4347 : Prop)
    (h40810 : (¬ p2027))
    (h35417 : p2027 ∨ (¬ p2088) ∨ (¬ p2249) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2928) ∨ (¬ p3487) ∨ (¬ p3567) ∨ (¬ p3644) ∨ (¬ p4114) ∨ (¬ p4133) ∨ (¬ p4347))
    : (¬ p2088) ∨ (¬ p2249) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2928) ∨ (¬ p3487) ∨ (¬ p3567) ∨ (¬ p3644) ∨ (¬ p4114) ∨ (¬ p4133) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h35417 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step60602 (p2027 p2299 p2341 p2417 p3821 p4712 : Prop)
    (h40810 : (¬ p2027))
    (h35422 : p2027 ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2417) ∨ (¬ p3821) ∨ (¬ p4712))
    : (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2417) ∨ (¬ p3821) ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35422 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60607 (p2027 p2191 p2753 p3166 p3256 p3379 p3555 p4117 p4134 p4347 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h35429 : p2027 ∨ (¬ p2191) ∨ (¬ p2753) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4117) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p5216))
    : (¬ p2191) ∨ (¬ p2753) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4117) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35429 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60613 (p1988 p2027 p2202 p2563 p3115 p3680 p3952 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h35435 : (¬ p1988) ∨ p2027 ∨ p2202 ∨ (¬ p2563) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p3952))
    : (¬ p2563) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h35435 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60615 (p2027 p2132 p2753 p2870 p2881 p2927 p3379 p4278 p4366 p4666 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h35437 : p2027 ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4278) ∨ (¬ p4366) ∨ (¬ p4666) ∨ (¬ p5216))
    : (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4278) ∨ (¬ p4366) ∨ (¬ p4666) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35437 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60619 (p2027 p2295 p2313 p2630 p3361 p3983 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h35441 : p2027 ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2630) ∨ (¬ p3361) ∨ (¬ p3983) ∨ (¬ p4972))
    : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2630) ∨ (¬ p3361) ∨ (¬ p3983) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35441 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60620 (p2027 p2295 p2727 p3549 p4245 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h35442 : p2027 ∨ (¬ p2295) ∨ (¬ p2727) ∨ (¬ p3549) ∨ (¬ p4245) ∨ (¬ p4972))
    : (¬ p2295) ∨ (¬ p2727) ∨ (¬ p3549) ∨ (¬ p4245) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35442 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60621 (p2027 p2727 p3323 p4026 p4245 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h35443 : p2027 ∨ (¬ p2727) ∨ (¬ p3323) ∨ (¬ p4026) ∨ (¬ p4245) ∨ (¬ p4972))
    : (¬ p2727) ∨ (¬ p3323) ∨ (¬ p4026) ∨ (¬ p4245) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35443 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60623 (p1984 p2027 p2114 p2829 p3238 p3452 p3461 p3483 p4444 p4948 p5059 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h35445 : (¬ p1984) ∨ p2027 ∨ p2114 ∨ (¬ p2829) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p4444) ∨ (¬ p4948) ∨ (¬ p5059))
    : (¬ p2829) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p4444) ∨ (¬ p4948) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p1984 := h2144;
    let u9 : (¬ p2027) := h40810;
    let u10 : (¬ p2114) := h40864;
    (Or.elim h35445 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u10 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step60626 (p2027 p2497 p3389 p3519 p3660 p3888 p4435 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h35449 : p2027 ∨ (¬ p2497) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4435) ∨ (¬ p4646))
    : (¬ p2497) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4435) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2497 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35449 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60627 (p2027 p2248 p2499 p2901 p2946 p3246 p3452 p4137 p4625 : Prop)
    (h40810 : (¬ p2027))
    (h35450 : p2027 ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p4137) ∨ (¬ p4625))
    : (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p4137) ∨ (¬ p4625) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35450 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60629 (p2027 p2850 p2927 p3379 p4030 p4366 p4644 : Prop)
    (h40810 : (¬ p2027))
    (h35452 : p2027 ∨ (¬ p2850) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4030) ∨ (¬ p4366) ∨ (¬ p4644))
    : (¬ p2850) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4030) ∨ (¬ p4366) ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35452 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60630 (p2027 p2104 p2246 p2264 p2363 p2598 p2742 p2807 p3550 p4752 p5118 p5612 : Prop)
    (h40810 : (¬ p2027))
    (h35453 : p2027 ∨ (¬ p2104) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p2807) ∨ p3550 ∨ (¬ p4752) ∨ (¬ p5118) ∨ (¬ p5612))
    : (¬ p2104) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p2807) ∨ p3550 ∨ (¬ p4752) ∨ (¬ p5118) ∨ (¬ p5612) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3550) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5612 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h35453 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step60631 (p1988 p2027 p2589 p2662 p2842 p2850 p3276 p3343 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h35454 : (¬ p1988) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2662) ∨ p2842 ∨ (¬ p2850) ∨ (¬ p3276) ∨ (¬ p3343))
    : (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2850) ∨ (¬ p3276) ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2842) := h40885;
    (Or.elim h35454 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60632 (p2027 p2313 p3212 p3309 p3957 p4198 p5046 : Prop)
    (h40810 : (¬ p2027))
    (h35455 : p2027 ∨ (¬ p2313) ∨ (¬ p3212) ∨ (¬ p3309) ∨ (¬ p3957) ∨ (¬ p4198) ∨ (¬ p5046))
    : (¬ p2313) ∨ (¬ p3212) ∨ (¬ p3309) ∨ (¬ p3957) ∨ (¬ p4198) ∨ (¬ p5046) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35455 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60643 (p1994 p2027 p2230 p2440 p2579 p3128 p4137 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40894 : (¬ p3128))
    (h35468 : (¬ p1994) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ p3128 ∨ (¬ p4137))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p4137) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3128) := h40894;
    (Or.elim h35468 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60648 (p2027 p2191 p2248 p2531 p2534 p3286 p3452 p3506 p3950 p4202 p4381 : Prop)
    (h40810 : (¬ p2027))
    (h35473 : p2027 ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2531) ∨ (¬ p2534) ∨ (¬ p3286) ∨ (¬ p3452) ∨ (¬ p3506) ∨ (¬ p3950) ∨ (¬ p4202) ∨ (¬ p4381))
    : (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2531) ∨ (¬ p2534) ∨ (¬ p3286) ∨ (¬ p3452) ∨ (¬ p3506) ∨ (¬ p3950) ∨ (¬ p4202) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35473 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60652 (p1981 p2027 p2202 p2427 p2819 p3707 p4337 p4909 p5274 p5284 p5363 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h35478 : (¬ p1981) ∨ p2027 ∨ p2202 ∨ (¬ p2427) ∨ (¬ p2819) ∨ (¬ p3707) ∨ (¬ p4337) ∨ (¬ p4909) ∨ (¬ p5274) ∨ (¬ p5284) ∨ (¬ p5363))
    : (¬ p2427) ∨ (¬ p2819) ∨ (¬ p3707) ∨ (¬ p4337) ∨ (¬ p4909) ∨ (¬ p5274) ∨ (¬ p5284) ∨ (¬ p5363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p1981 := h2141;
    let u9 : (¬ p2027) := h40810;
    let u10 : (¬ p2202) := h40867;
    (Or.elim h35478 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u10 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step60653 (p2027 p2144 p2630 p2742 p2957 p3425 p3662 p4650 p4777 : Prop)
    (h40810 : (¬ p2027))
    (h35479 : p2027 ∨ (¬ p2144) ∨ (¬ p2630) ∨ p2742 ∨ (¬ p2957) ∨ (¬ p3425) ∨ (¬ p3662) ∨ (¬ p4650) ∨ (¬ p4777))
    : (¬ p2144) ∨ (¬ p2630) ∨ p2742 ∨ (¬ p2957) ∨ (¬ p3425) ∨ (¬ p3662) ∨ (¬ p4650) ∨ (¬ p4777) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2742) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35479 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60654 (p2027 p2138 p2246 p2598 p2742 p3286 p3506 p3951 p4381 p4385 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h35480 : p2027 ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3951) ∨ (¬ p4381) ∨ (¬ p4385) ∨ (¬ p4752))
    : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3951) ∨ (¬ p4381) ∨ (¬ p4385) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35480 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60656 (p1988 p2027 p2373 p2938 p3146 p3266 p4235 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h35482 : (¬ p1988) ∨ p2027 ∨ (¬ p2373) ∨ p2938 ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p4235))
    : (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h35482 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60659 (p2027 p2373 p3553 p4042 p4235 p4280 : Prop)
    (h40810 : (¬ p2027))
    (h35486 : p2027 ∨ (¬ p2373) ∨ (¬ p3553) ∨ (¬ p4042) ∨ (¬ p4235) ∨ (¬ p4280))
    : (¬ p2373) ∨ (¬ p3553) ∨ (¬ p4042) ∨ (¬ p4235) ∨ (¬ p4280) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35486 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60660 (p1982 p2027 p2388 p2619 p2901 p3146 p4244 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h35487 : (¬ p1982) ∨ p2027 ∨ p2388 ∨ (¬ p2619) ∨ (¬ p2901) ∨ (¬ p3146) ∨ (¬ p4244))
    : (¬ p2619) ∨ (¬ p2901) ∨ (¬ p3146) ∨ (¬ p4244) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2388) := h40873;
    (Or.elim h35487 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60664 (p2027 p2088 p2630 p2951 p4238 p4340 p4364 p4701 : Prop)
    (h40810 : (¬ p2027))
    (h35491 : p2027 ∨ (¬ p2088) ∨ (¬ p2630) ∨ (¬ p2951) ∨ (¬ p4238) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4701))
    : (¬ p2088) ∨ (¬ p2630) ∨ (¬ p2951) ∨ (¬ p4238) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4701) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4701 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35491 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60666 (p1987 p2027 p2651 p2810 p2963 p2997 p3568 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h35493 : (¬ p1987) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ p2997 ∨ (¬ p3568))
    : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h35493 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60667 (p2027 p2651 p2737 p2811 p3588 p4650 p4777 : Prop)
    (h40810 : (¬ p2027))
    (h35494 : p2027 ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3588) ∨ (¬ p4650) ∨ (¬ p4777))
    : (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3588) ∨ (¬ p4650) ∨ (¬ p4777) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35494 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60671 (p1987 p2027 p2588 p2651 p2810 p2963 p2997 p4389 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h35498 : (¬ p1987) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ p2997 ∨ (¬ p4389))
    : (¬ p2588) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p4389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h35498 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60672 (p2027 p2341 p2589 p2922 p3097 p3553 p3575 p4173 p4210 p4570 p5191 : Prop)
    (h40810 : (¬ p2027))
    (h35499 : p2027 ∨ (¬ p2341) ∨ (¬ p2589) ∨ (¬ p2922) ∨ (¬ p3097) ∨ (¬ p3553) ∨ (¬ p3575) ∨ (¬ p4173) ∨ (¬ p4210) ∨ (¬ p4570) ∨ (¬ p5191))
    : (¬ p2341) ∨ (¬ p2589) ∨ (¬ p2922) ∨ (¬ p3097) ∨ (¬ p3553) ∨ (¬ p3575) ∨ (¬ p4173) ∨ (¬ p4210) ∨ (¬ p4570) ∨ (¬ p5191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35499 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60676 (p2027 p3319 p3692 p3923 p4433 p4460 p5379 : Prop)
    (h40810 : (¬ p2027))
    (h35504 : p2027 ∨ (¬ p3319) ∨ (¬ p3692) ∨ (¬ p3923) ∨ (¬ p4433) ∨ (¬ p4460) ∨ (¬ p5379))
    : (¬ p3319) ∨ (¬ p3692) ∨ (¬ p3923) ∨ (¬ p4433) ∨ (¬ p4460) ∨ (¬ p5379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4460 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35504 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60677 (p2027 p2319 p2352 p2387 p3660 p4283 p4320 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h35505 : p2027 ∨ (¬ p2319) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3660) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702))
    : (¬ p2319) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3660) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35505 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60681 (p2027 p2373 p2533 p3680 p3773 p4380 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h35510 : p2027 ∨ (¬ p2373) ∨ (¬ p2533) ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p4380) ∨ (¬ p4533))
    : (¬ p2373) ∨ (¬ p2533) ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p4380) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4380 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35510 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60684 (p1991 p2027 p2202 p2427 p2952 p2992 p2996 p3699 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h35513 : (¬ p1991) ∨ p2027 ∨ p2202 ∨ (¬ p2427) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3699))
    : (¬ p2427) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3699) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1991 := h2151;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h35513 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60685 (p2027 p2132 p2493 p2509 p2579 p2870 p2881 p4108 p4438 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h35514 : p2027 ∨ (¬ p2132) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2579) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p4108) ∨ (¬ p4438) ∨ (¬ p4733))
    : (¬ p2132) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2579) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p4108) ∨ (¬ p4438) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35514 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60690 (p2027 p2249 p2499 p2657 p3487 p3506 p3842 p4137 p4444 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h35519 : p2027 ∨ (¬ p2249) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3487) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4137) ∨ (¬ p4444) ∨ (¬ p4604))
    : (¬ p2249) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3487) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4137) ∨ (¬ p4444) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2249 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35519 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60694 (p2027 p2341 p2499 p3434 p3452 p3659 p3819 p4137 p4625 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h35524 : p2027 ∨ (¬ p2341) ∨ (¬ p2499) ∨ (¬ p3434) ∨ (¬ p3452) ∨ (¬ p3659) ∨ (¬ p3819) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4733))
    : (¬ p2341) ∨ (¬ p2499) ∨ (¬ p3434) ∨ (¬ p3452) ∨ (¬ p3659) ∨ (¬ p3819) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35524 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60701 (p2027 p2313 p3309 p3361 p3583 p3983 p4869 p5049 : Prop)
    (h40810 : (¬ p2027))
    (h35533 : p2027 ∨ (¬ p2313) ∨ (¬ p3309) ∨ (¬ p3361) ∨ (¬ p3583) ∨ (¬ p3983) ∨ (¬ p4869) ∨ (¬ p5049))
    : (¬ p2313) ∨ (¬ p3309) ∨ (¬ p3361) ∨ (¬ p3583) ∨ (¬ p3983) ∨ (¬ p4869) ∨ (¬ p5049) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35533 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60703 (p2027 p2341 p2459 p2707 p2748 p3365 p3577 p4037 p4154 p4604 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h35535 : p2027 ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2707) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3577) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4604) ∨ (¬ p4734))
    : (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2707) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3577) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4604) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35535 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60711 (p1984 p2027 p2245 p2657 p2727 p3128 p4037 p4154 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40894 : (¬ p3128))
    (h35545 : (¬ p1984) ∨ p2027 ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ p3128 ∨ (¬ p4037) ∨ (¬ p4154))
    : (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p4037) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3128) := h40894;
    (Or.elim h35545 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60719 (p2027 p2437 p3564 p3660 p4037 p4194 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h35558 : p2027 ∨ (¬ p2437) ∨ (¬ p3564) ∨ (¬ p3660) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4646))
    : (¬ p2437) ∨ (¬ p3564) ∨ (¬ p3660) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35558 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60726 (p1982 p2027 p2622 p2797 p3461 p3567 p3654 p4444 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h35565 : (¬ p1982) ∨ p2027 ∨ p2622 ∨ (¬ p2797) ∨ (¬ p3461) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4444))
    : (¬ p2797) ∨ (¬ p3461) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h35565 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60730 (p2027 p2252 p2750 p2952 p3063 p3093 p3097 p3952 p3954 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h35569 : p2027 ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4405))
    : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35569 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60741 (p2027 p2252 p2264 p2750 p3093 p3319 p3551 p3947 p3954 p4621 p4849 : Prop)
    (h40810 : (¬ p2027))
    (h35582 : p2027 ∨ (¬ p2252) ∨ (¬ p2264) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3551) ∨ (¬ p3947) ∨ (¬ p3954) ∨ (¬ p4621) ∨ (¬ p4849))
    : (¬ p2252) ∨ (¬ p2264) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3551) ∨ (¬ p3947) ∨ (¬ p3954) ∨ (¬ p4621) ∨ (¬ p4849) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4849 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35582 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60745 (p2027 p2542 p2662 p3276 p3773 p4949 p5181 : Prop)
    (h40810 : (¬ p2027))
    (h35586 : p2027 ∨ (¬ p2542) ∨ (¬ p2662) ∨ (¬ p3276) ∨ (¬ p3773) ∨ (¬ p4949) ∨ (¬ p5181))
    : (¬ p2542) ∨ (¬ p2662) ∨ (¬ p3276) ∨ (¬ p3773) ∨ (¬ p4949) ∨ (¬ p5181) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35586 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60747 (p2027 p2577 p3389 p3564 p3946 p4711 : Prop)
    (h40810 : (¬ p2027))
    (h35588 : p2027 ∨ (¬ p2577) ∨ (¬ p3389) ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p4711))
    : (¬ p2577) ∨ (¬ p3389) ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p4711) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35588 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60748 (p1990 p2027 p2295 p3008 p3097 p3564 p4037 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h35589 : (¬ p1990) ∨ p2027 ∨ (¬ p2295) ∨ p3008 ∨ (¬ p3097) ∨ (¬ p3564) ∨ (¬ p4037))
    : (¬ p2295) ∨ (¬ p3097) ∨ (¬ p3564) ∨ (¬ p4037) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3008) := h40891;
    (Or.elim h35589 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60750 (p2027 p2960 p2962 p3654 p3744 p3952 : Prop)
    (h40810 : (¬ p2027))
    (h35591 : p2027 ∨ (¬ p2960) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p3952))
    : (¬ p2960) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2960 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35591 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60751 (p2027 p2589 p2922 p3347 p3569 p4320 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h35592 : p2027 ∨ (¬ p2589) ∨ (¬ p2922) ∨ (¬ p3347) ∨ (¬ p3569) ∨ (¬ p4320) ∨ (¬ p4702))
    : (¬ p2589) ∨ (¬ p2922) ∨ (¬ p3347) ∨ (¬ p3569) ∨ (¬ p4320) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35592 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60753 (p2027 p2498 p2542 p3319 p4037 p4194 p4715 : Prop)
    (h40810 : (¬ p2027))
    (h35596 : p2027 ∨ (¬ p2498) ∨ (¬ p2542) ∨ (¬ p3319) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4715))
    : (¬ p2498) ∨ (¬ p2542) ∨ (¬ p3319) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2498 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35596 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60756 (p2027 p2406 p2427 p2499 p3096 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h35600 : p2027 ∨ (¬ p2406) ∨ (¬ p2427) ∨ (¬ p2499) ∨ (¬ p3096) ∨ (¬ p4558))
    : (¬ p2406) ∨ (¬ p2427) ∨ (¬ p2499) ∨ (¬ p3096) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35600 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60760 (p2027 p2499 p2891 p3948 p4235 p4715 : Prop)
    (h40810 : (¬ p2027))
    (h35605 : p2027 ∨ (¬ p2499) ∨ (¬ p2891) ∨ (¬ p3948) ∨ (¬ p4235) ∨ (¬ p4715))
    : (¬ p2499) ∨ (¬ p2891) ∨ (¬ p3948) ∨ (¬ p4235) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35605 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60762 (p2020 p2027 p2088 p2409 p2922 p3575 p3941 p4348 p4590 : Prop)
    (h2180 : p2020)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h35607 : (¬ p2020) ∨ p2027 ∨ (¬ p2088) ∨ p2409 ∨ (¬ p2922) ∨ (¬ p3575) ∨ (¬ p3941) ∨ (¬ p4348) ∨ (¬ p4590))
    : (¬ p2088) ∨ (¬ p2922) ∨ (¬ p3575) ∨ (¬ p3941) ∨ (¬ p4348) ∨ (¬ p4590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2020 := h2180;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2409) := h40874;
    (Or.elim h35607 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step60765 (p2027 p2210 p2922 p3540 p4108 p4281 p4959 : Prop)
    (h40810 : (¬ p2027))
    (h35611 : p2027 ∨ (¬ p2210) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4108) ∨ (¬ p4281) ∨ (¬ p4959))
    : (¬ p2210) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4108) ∨ (¬ p4281) ∨ (¬ p4959) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35611 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60773 (p2010 p2027 p2497 p2622 p2797 p2922 p3567 p3654 p4026 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h35620 : (¬ p2010) ∨ p2027 ∨ (¬ p2497) ∨ p2622 ∨ (¬ p2797) ∨ (¬ p2922) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4026))
    : (¬ p2497) ∨ (¬ p2797) ∨ (¬ p2922) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4026) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2497 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2010 := h2170;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2622) := h40878;
    (Or.elim h35620 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step60774 (p2027 p2252 p2750 p2952 p3093 p3309 p3952 p3954 p3989 p4501 : Prop)
    (h40810 : (¬ p2027))
    (h35621 : p2027 ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p3989) ∨ (¬ p4501))
    : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p3989) ∨ (¬ p4501) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35621 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60798 (p2027 p2440 p3016 p3958 p4110 : Prop)
    (h40810 : (¬ p2027))
    (h35654 : p2027 ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3958) ∨ (¬ p4110))
    : (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3958) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2027) := h40810;
    (Or.elim h35654 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step60800 (p2027 p2440 p3016 p4173 p4203 p4629 : Prop)
    (h40810 : (¬ p2027))
    (h35656 : p2027 ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4173) ∨ (¬ p4203) ∨ (¬ p4629))
    : (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4173) ∨ (¬ p4203) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35656 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60810 (p2027 p2363 p2534 p2579 p3347 p3399 p3527 p3573 p3954 p4503 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h35668 : p2027 ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3573) ∨ (¬ p3954) ∨ (¬ p4503) ∨ (¬ p5216))
    : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3573) ∨ (¬ p3954) ∨ (¬ p4503) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35668 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60811 (p2027 p2088 p4066 p4348 p4391 p4590 p5559 : Prop)
    (h40810 : (¬ p2027))
    (h35669 : p2027 ∨ (¬ p2088) ∨ (¬ p4066) ∨ (¬ p4348) ∨ (¬ p4391) ∨ (¬ p4590) ∨ (¬ p5559))
    : (¬ p2088) ∨ (¬ p4066) ∨ (¬ p4348) ∨ (¬ p4391) ∨ (¬ p4590) ∨ (¬ p5559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35669 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60812 (p2027 p2241 p2579 p2641 p3125 p3347 p3954 p4137 p4564 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h35670 : p2027 ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2641) ∨ (¬ p3125) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p4137) ∨ (¬ p4564) ∨ (¬ p5216))
    : (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2641) ∨ (¬ p3125) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p4137) ∨ (¬ p4564) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35670 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60817 (p2027 p2299 p3097 p3399 p3631 p3645 p3646 p3954 p4668 p4877 : Prop)
    (h40810 : (¬ p2027))
    (h35676 : p2027 ∨ (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4668) ∨ (¬ p4877))
    : (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4668) ∨ (¬ p4877) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35676 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60819 (p2027 p2156 p3954 p4172 p4173 p4877 : Prop)
    (h40810 : (¬ p2027))
    (h35678 : p2027 ∨ (¬ p2156) ∨ (¬ p3954) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p4877))
    : (¬ p2156) ∨ (¬ p3954) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p4877) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35678 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60831 (p2027 p2532 p3115 p3497 p3857 p4529 : Prop)
    (h40810 : (¬ p2027))
    (h35696 : p2027 ∨ (¬ p2532) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p3857) ∨ (¬ p4529))
    : (¬ p2532) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p3857) ∨ (¬ p4529) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2532 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4529 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35696 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60832 (p2003 p2027 p2387 p2668 p2764 p4037 p4191 : Prop)
    (h2163 : p2003)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h35697 : (¬ p2003) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2668) ∨ p2764 ∨ (¬ p4037) ∨ (¬ p4191))
    : (¬ p2387) ∨ (¬ p2668) ∨ (¬ p4037) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2003 := h2163;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h35697 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60842 (p2027 p2387 p2581 p3083 p3574 p4157 : Prop)
    (h40810 : (¬ p2027))
    (h35707 : p2027 ∨ (¬ p2387) ∨ (¬ p2581) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p4157))
    : (¬ p2387) ∨ (¬ p2581) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p4157) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35707 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60843 (p2027 p2252 p2542 p2589 p2655 p2750 p3063 p3093 p3693 p3954 p4134 p4256 : Prop)
    (h40810 : (¬ p2027))
    (h35708 : p2027 ∨ (¬ p2252) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3693) ∨ (¬ p3954) ∨ (¬ p4134) ∨ (¬ p4256))
    : (¬ p2252) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3693) ∨ (¬ p3954) ∨ (¬ p4134) ∨ (¬ p4256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h35708 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step60846 (p1983 p2027 p2765 p2982 p3680 p4110 p4381 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h35711 : (¬ p1983) ∨ p2027 ∨ p2765 ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4110) ∨ (¬ p4381))
    : (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4110) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h35711 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60853 (p1987 p2027 p2534 p2589 p2608 p2662 p2699 p2707 p2717 p2810 p3146 p4607 p4905 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h35718 : (¬ p1987) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2662) ∨ p2699 ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2810) ∨ (¬ p3146) ∨ (¬ p4607) ∨ (¬ p4905))
    : (¬ p2534) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2662) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2810) ∨ (¬ p3146) ∨ (¬ p4607) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p1987 := h2147;
    let u11 : (¬ p2027) := h40810;
    let u12 : (¬ p2699) := h40881;
    (Or.elim h35718 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u12 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u8))) (fun r11 => (False.elim (r11 u9)))))))))))))))))))))))))))

theorem step60856 (p2027 p2717 p3146 p4324 p4445 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h35722 : p2027 ∨ (¬ p2717) ∨ (¬ p3146) ∨ (¬ p4324) ∨ (¬ p4445) ∨ (¬ p4905))
    : (¬ p2717) ∨ (¬ p3146) ∨ (¬ p4324) ∨ (¬ p4445) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35722 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60857 (p1989 p2027 p2169 p2210 p2363 p3692 p3860 p3906 : Prop)
    (h2149 : p1989)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h35723 : (¬ p1989) ∨ p2027 ∨ p2169 ∨ (¬ p2210) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p3860) ∨ (¬ p3906))
    : (¬ p2210) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p3860) ∨ (¬ p3906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1989 := h2149;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h35723 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60859 (p1987 p2027 p2589 p2662 p2764 p2810 p4322 p4948 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h35726 : (¬ p1987) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2662) ∨ p2764 ∨ (¬ p2810) ∨ (¬ p4322) ∨ (¬ p4948))
    : (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p4322) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h35726 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60861 (p2027 p2651 p2685 p2787 p2810 p3097 p3125 p3946 p4117 p4570 : Prop)
    (h40810 : (¬ p2027))
    (h35729 : p2027 ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2787) ∨ (¬ p2810) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4117) ∨ (¬ p4570))
    : (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2787) ∨ (¬ p2810) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4117) ∨ (¬ p4570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35729 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60865 (p1977 p2027 p2299 p2633 p3097 p3662 p3952 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35733 : (¬ p1977) ∨ p2027 ∨ (¬ p2299) ∨ p2633 ∨ (¬ p3097) ∨ (¬ p3662) ∨ (¬ p3952))
    : (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3662) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h35733 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60869 (p2027 p2750 p3073 p3449 p3662 p3744 p3952 p3954 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h35737 : p2027 ∨ (¬ p2750) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3662) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4604))
    : (¬ p2750) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3662) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2750 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35737 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60872 (p2003 p2027 p2187 p2284 p2387 p2938 p4320 : Prop)
    (h2163 : p2003)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h35740 : (¬ p2003) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2387) ∨ p2938 ∨ (¬ p4320))
    : (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2387) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2003 := h2163;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h35740 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60876 (p2027 p2313 p2598 p2742 p2778 p3309 p4752 p4759 : Prop)
    (h40810 : (¬ p2027))
    (h35745 : p2027 ∨ (¬ p2313) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p2778) ∨ (¬ p3309) ∨ (¬ p4752) ∨ (¬ p4759))
    : (¬ p2313) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p2778) ∨ (¬ p3309) ∨ (¬ p4752) ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35745 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60881 (p2027 p2373 p3347 p3399 p3631 p3904 p3951 p3954 p4120 p4948 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h35752 : p2027 ∨ (¬ p2373) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3904) ∨ (¬ p3951) ∨ (¬ p3954) ∨ (¬ p4120) ∨ (¬ p4948) ∨ (¬ p5216))
    : (¬ p2373) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3904) ∨ (¬ p3951) ∨ (¬ p3954) ∨ (¬ p4120) ∨ (¬ p4948) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35752 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60884 (p2000 p2027 p2274 p2476 p2765 p3083 p3742 p3921 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h35755 : (¬ p2000) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2476) ∨ p2765 ∨ (¬ p3083) ∨ (¬ p3742) ∨ (¬ p3921))
    : (¬ p2274) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p3742) ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2000 := h2160;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h35755 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60888 (p2027 p2274 p2313 p2563 p4198 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h35759 : p2027 ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2563) ∨ (¬ p4198) ∨ (¬ p4533))
    : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2563) ∨ (¬ p4198) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35759 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60892 (p2027 p2459 p3055 p3399 p3527 p3684 p4736 p4948 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h35763 : p2027 ∨ (¬ p2459) ∨ (¬ p3055) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3684) ∨ (¬ p4736) ∨ (¬ p4948) ∨ (¬ p5059))
    : (¬ p2459) ∨ (¬ p3055) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3684) ∨ (¬ p4736) ∨ (¬ p4948) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35763 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60895 (p2001 p2027 p2553 p3008 p3073 p3549 p3692 p4317 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h35767 : (¬ p2001) ∨ p2027 ∨ (¬ p2553) ∨ p3008 ∨ (¬ p3073) ∨ (¬ p3549) ∨ (¬ p3692) ∨ (¬ p4317))
    : (¬ p2553) ∨ (¬ p3073) ∨ (¬ p3549) ∨ (¬ p3692) ∨ (¬ p4317) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2001 := h2161;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3008) := h40891;
    (Or.elim h35767 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60898 (p2027 p2210 p2254 p2630 p2657 p2881 p2891 p3877 p4041 : Prop)
    (h40810 : (¬ p2027))
    (h35771 : p2027 ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3877) ∨ (¬ p4041))
    : (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3877) ∨ (¬ p4041) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35771 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60906 (p2027 p2284 p2497 p2553 p2696 p3136 p3452 p3549 p4718 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h35779 : p2027 ∨ (¬ p2284) ∨ (¬ p2497) ∨ (¬ p2553) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3452) ∨ (¬ p3549) ∨ (¬ p4718) ∨ (¬ p4733))
    : (¬ p2284) ∨ (¬ p2497) ∨ (¬ p2553) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3452) ∨ (¬ p3549) ∨ (¬ p4718) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35779 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60908 (p2027 p2264 p2312 p3309 p3570 p4155 p4204 p4518 : Prop)
    (h40810 : (¬ p2027))
    (h35781 : p2027 ∨ (¬ p2264) ∨ (¬ p2312) ∨ (¬ p3309) ∨ (¬ p3570) ∨ (¬ p4155) ∨ (¬ p4204) ∨ (¬ p4518))
    : (¬ p2264) ∨ (¬ p2312) ∨ (¬ p3309) ∨ (¬ p3570) ∨ (¬ p4155) ∨ (¬ p4204) ∨ (¬ p4518) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35781 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60922 (p2027 p2264 p2737 p2807 p2811 p2928 p3055 p4030 p4278 p4666 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h35797 : p2027 ∨ (¬ p2264) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p2928) ∨ (¬ p3055) ∨ (¬ p4030) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4734))
    : (¬ p2264) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p2928) ∨ (¬ p3055) ∨ (¬ p4030) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35797 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60925 (p1976 p2027 p2534 p2589 p2914 p3609 p3876 p3905 p4354 p4607 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h35800 : (¬ p1976) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2589) ∨ p2914 ∨ (¬ p3609) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4354) ∨ (¬ p4607))
    : (¬ p2534) ∨ (¬ p2589) ∨ (¬ p3609) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4354) ∨ (¬ p4607) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4354 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p1976 := h2136;
    let u8 : (¬ p2027) := h40810;
    let u9 : (¬ p2914) := h40887;
    (Or.elim h35800 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u9 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step60926 (p1998 p2027 p2264 p2611 p2696 p3434 p3947 p4781 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h35801 : (¬ p1998) ∨ p2027 ∨ (¬ p2264) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4781))
    : (¬ p2264) ∨ (¬ p2696) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h35801 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60931 (p1998 p2027 p2132 p2497 p2553 p2870 p3008 p3146 p3452 p3549 p3747 p4348 p4733 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h35806 : (¬ p1998) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2497) ∨ (¬ p2553) ∨ (¬ p2870) ∨ p3008 ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p3549) ∨ (¬ p3747) ∨ (¬ p4348) ∨ (¬ p4733))
    : (¬ p2132) ∨ (¬ p2497) ∨ (¬ p2553) ∨ (¬ p2870) ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p3549) ∨ (¬ p3747) ∨ (¬ p4348) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p1998 := h2158;
    let u11 : (¬ p2027) := h40810;
    let u12 : (¬ p3008) := h40891;
    (Or.elim h35806 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u12 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u8))) (fun r11 => (False.elim (r11 u9)))))))))))))))))))))))))))

theorem step60933 (p2027 p2246 p2476 p2534 p2662 p2751 p2810 p2901 p2946 p3246 p3950 : Prop)
    (h40810 : (¬ p2027))
    (h35808 : p2027 ∨ (¬ p2246) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3950))
    : (¬ p2246) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35808 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60936 (p2027 p2284 p2352 p3497 p4506 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h35815 : p2027 ∨ (¬ p2284) ∨ (¬ p2352) ∨ (¬ p3497) ∨ (¬ p4506) ∨ (¬ p4718))
    : (¬ p2284) ∨ (¬ p2352) ∨ (¬ p3497) ∨ (¬ p4506) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35815 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60945 (p2027 p2829 p3583 p3952 p4185 p5053 : Prop)
    (h40810 : (¬ p2027))
    (h35826 : p2027 ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3952) ∨ (¬ p4185) ∨ (¬ p5053))
    : (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3952) ∨ (¬ p4185) ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35826 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60947 (p2004 p2027 p2191 p2202 p2373 p3399 p3555 : Prop)
    (h2164 : p2004)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h35828 : (¬ p2004) ∨ p2027 ∨ (¬ p2191) ∨ p2202 ∨ (¬ p2373) ∨ (¬ p3399) ∨ (¬ p3555))
    : (¬ p2191) ∨ (¬ p2373) ∨ (¬ p3399) ∨ (¬ p3555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2004 := h2164;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h35828 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60950 (p1984 p2027 p2622 p2743 p2780 p3063 p3873 p4358 p4869 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h35831 : (¬ p1984) ∨ p2027 ∨ p2622 ∨ (¬ p2743) ∨ (¬ p2780) ∨ (¬ p3063) ∨ (¬ p3873) ∨ (¬ p4358) ∨ (¬ p4869))
    : (¬ p2743) ∨ (¬ p2780) ∨ (¬ p3063) ∨ (¬ p3873) ∨ (¬ p4358) ∨ (¬ p4869) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1984 := h2144;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2622) := h40878;
    (Or.elim h35831 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step60951 (p1976 p2027 p2765 p3055 p3367 p3583 p3698 p4110 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h35832 : (¬ p1976) ∨ p2027 ∨ p2765 ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4110))
    : (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h35832 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60955 (p2027 p2499 p3222 p3989 p4045 p4157 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h35840 : p2027 ∨ (¬ p2499) ∨ (¬ p3222) ∨ (¬ p3989) ∨ (¬ p4045) ∨ (¬ p4157) ∨ (¬ p4718))
    : (¬ p2499) ∨ (¬ p3222) ∨ (¬ p3989) ∨ (¬ p4045) ∨ (¬ p4157) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35840 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60957 (p2027 p2598 p3434 p3820 p3821 p4752 p4781 : Prop)
    (h40810 : (¬ p2027))
    (h35842 : p2027 ∨ (¬ p2598) ∨ (¬ p3434) ∨ (¬ p3820) ∨ (¬ p3821) ∨ (¬ p4752) ∨ (¬ p4781))
    : (¬ p2598) ∨ (¬ p3434) ∨ (¬ p3820) ∨ (¬ p3821) ∨ (¬ p4752) ∨ (¬ p4781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35842 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step60960 (p2027 p2518 p2531 p3238 p4120 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h35845 : p2027 ∨ (¬ p2518) ∨ (¬ p2531) ∨ (¬ p3238) ∨ (¬ p4120) ∨ (¬ p4533))
    : (¬ p2518) ∨ (¬ p2531) ∨ (¬ p3238) ∨ (¬ p4120) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35845 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step60963 (p1999 p2027 p2307 p2641 p2688 p3097 p3125 p3567 : Prop)
    (h2159 : p1999)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h35849 : (¬ p1999) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2641) ∨ p2688 ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3567))
    : (¬ p2307) ∨ (¬ p2641) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1999 := h2159;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h35849 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60974 (p1979 p2027 p2132 p2619 p2622 p3365 p3497 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h35860 : (¬ p1979) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2619) ∨ p2622 ∨ (¬ p3365) ∨ (¬ p3497))
    : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p3365) ∨ (¬ p3497) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1979 := h2139;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h35860 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step60975 (p2027 p2252 p2657 p2881 p3399 p3555 p3571 p3742 p4278 p4448 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h35861 : p2027 ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4448) ∨ (¬ p4666))
    : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4448) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4448 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35861 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step60977 (p1984 p2027 p2202 p2493 p2579 p3238 p3366 p3905 p3954 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h35863 : (¬ p1984) ∨ p2027 ∨ p2202 ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3238) ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p3954))
    : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3238) ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p3954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1984 := h2144;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2202) := h40867;
    (Or.elim h35863 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step60978 (p2027 p2248 p2509 p2534 p2958 p3212 p3452 p3680 p3950 p4381 : Prop)
    (h40810 : (¬ p2027))
    (h35864 : p2027 ∨ (¬ p2248) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2958) ∨ (¬ p3212) ∨ (¬ p3452) ∨ (¬ p3680) ∨ (¬ p3950) ∨ (¬ p4381))
    : (¬ p2248) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2958) ∨ (¬ p3212) ∨ (¬ p3452) ∨ (¬ p3680) ∨ (¬ p3950) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35864 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60981 (p2027 p2156 p2187 p2247 p3848 p3979 p4521 p5119 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h35867 : p2027 ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2247) ∨ (¬ p3848) ∨ (¬ p3979) ∨ (¬ p4521) ∨ (¬ p5119) ∨ (¬ p5284))
    : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2247) ∨ (¬ p3848) ∨ (¬ p3979) ∨ (¬ p4521) ∨ (¬ p5119) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35867 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60982 (p2027 p2210 p2254 p2657 p2881 p2891 p3742 p5503 p5559 : Prop)
    (h40810 : (¬ p2027))
    (h35869 : p2027 ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3742) ∨ (¬ p5503) ∨ (¬ p5559))
    : (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3742) ∨ (¬ p5503) ∨ (¬ p5559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35869 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step60984 (p2027 p2264 p2995 p3355 p3551 p3879 p4953 p5197 : Prop)
    (h40810 : (¬ p2027))
    (h35871 : p2027 ∨ (¬ p2264) ∨ (¬ p2995) ∨ (¬ p3355) ∨ (¬ p3551) ∨ (¬ p3879) ∨ (¬ p4953) ∨ (¬ p5197))
    : (¬ p2264) ∨ (¬ p2995) ∨ (¬ p3355) ∨ (¬ p3551) ∨ (¬ p3879) ∨ (¬ p4953) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35871 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60986 (p2027 p2459 p2608 p2881 p3051 p3193 p3370 p3452 p4377 p4697 : Prop)
    (h40810 : (¬ p2027))
    (h35874 : p2027 ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3193) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p4377) ∨ (¬ p4697))
    : (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3193) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p4377) ∨ (¬ p4697) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35874 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step60988 (p1981 p2027 p2190 p2307 p2344 p3097 p3146 p4347 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40871 : (¬ p2344))
    (h35876 : (¬ p1981) ∨ p2027 ∨ (¬ p2190) ∨ (¬ p2307) ∨ p2344 ∨ (¬ p3097) ∨ (¬ p3146) ∨ (¬ p4347))
    : (¬ p2190) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p3146) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1981 := h2141;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2344) := h40871;
    (Or.elim h35876 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step60989 (p2027 p2717 p3097 p3426 p3551 p3552 p4155 p4401 : Prop)
    (h40810 : (¬ p2027))
    (h35877 : p2027 ∨ (¬ p2717) ∨ (¬ p3097) ∨ (¬ p3426) ∨ (¬ p3551) ∨ (¬ p3552) ∨ (¬ p4155) ∨ (¬ p4401))
    : (¬ p2717) ∨ (¬ p3097) ∨ (¬ p3426) ∨ (¬ p3551) ∨ (¬ p3552) ∨ (¬ p4155) ∨ (¬ p4401) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35877 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step60995 (p1985 p2027 p2633 p2901 p2927 p3516 p3543 p3644 p4208 p4382 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h35884 : (¬ p1985) ∨ p2027 ∨ p2633 ∨ (¬ p2901) ∨ (¬ p2927) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p3644) ∨ (¬ p4208) ∨ (¬ p4382))
    : (¬ p2901) ∨ (¬ p2927) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p3644) ∨ (¬ p4208) ∨ (¬ p4382) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4382 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p1985 := h2145;
    let u8 : (¬ p2027) := h40810;
    let u9 : (¬ p2633) := h40879;
    (Or.elim h35884 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u9 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step61001 (p2027 p2493 p3238 p3646 p4203 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h35890 : p2027 ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3646) ∨ (¬ p4203) ∨ (¬ p4533))
    : (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3646) ∨ (¬ p4203) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35890 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61007 (p2027 p2187 p2230 p2563 p3365 p3366 p3519 p3553 p3572 p4133 p4376 : Prop)
    (h40810 : (¬ p2027))
    (h35899 : p2027 ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4133) ∨ (¬ p4376))
    : (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4133) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35899 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step61019 (p2027 p2156 p2373 p2608 p3519 p3548 p4110 p4366 p4376 p4399 p4902 : Prop)
    (h40810 : (¬ p2027))
    (h35914 : p2027 ∨ (¬ p2156) ∨ (¬ p2373) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3548) ∨ (¬ p4110) ∨ (¬ p4366) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p4902))
    : (¬ p2156) ∨ (¬ p2373) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3548) ∨ (¬ p4110) ∨ (¬ p4366) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35914 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step61020 (p2027 p2210 p2254 p2657 p2891 p3359 p4129 p4425 p4826 : Prop)
    (h40810 : (¬ p2027))
    (h35915 : p2027 ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2891) ∨ (¬ p3359) ∨ (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4826))
    : (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2891) ∨ (¬ p3359) ∨ (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4826) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h35915 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61022 (p1983 p2027 p2191 p2388 p2891 p3156 p3246 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h35918 : (¬ p1983) ∨ p2027 ∨ (¬ p2191) ∨ p2388 ∨ (¬ p2891) ∨ (¬ p3156) ∨ (¬ p3246))
    : (¬ p2191) ∨ (¬ p2891) ∨ (¬ p3156) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2388) := h40873;
    (Or.elim h35918 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61025 (p2027 p2252 p2657 p2750 p3073 p3449 p3742 p3954 p4278 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h35921 : p2027 ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3742) ∨ (¬ p3954) ∨ (¬ p4278) ∨ (¬ p4669))
    : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3742) ∨ (¬ p3954) ∨ (¬ p4278) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35921 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61026 (p2027 p2264 p2298 p2307 p3570 p4204 p4489 : Prop)
    (h40810 : (¬ p2027))
    (h35922 : p2027 ∨ (¬ p2264) ∨ (¬ p2298) ∨ (¬ p2307) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4489))
    : (¬ p2264) ∨ (¬ p2298) ∨ (¬ p2307) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4489) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4489 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35922 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61027 (p2027 p2138 p2598 p2743 p2839 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h35924 : p2027 ∨ (¬ p2138) ∨ (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p4752))
    : (¬ p2138) ∨ (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35924 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61033 (p2027 p2192 p2210 p3834 p4388 p5043 : Prop)
    (h40810 : (¬ p2027))
    (h35931 : p2027 ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3834) ∨ (¬ p4388) ∨ (¬ p5043))
    : (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3834) ∨ (¬ p4388) ∨ (¬ p5043) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4388 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35931 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61036 (p1982 p2027 p2202 p2220 p2427 p3146 p3556 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h35934 : (¬ p1982) ∨ p2027 ∨ p2202 ∨ (¬ p2220) ∨ (¬ p2427) ∨ (¬ p3146) ∨ (¬ p3556))
    : (¬ p2220) ∨ (¬ p2427) ∨ (¬ p3146) ∨ (¬ p3556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h35934 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61041 (p2027 p2136 p2192 p2598 p3646 p4313 p4418 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h35940 : p2027 ∨ (¬ p2136) ∨ (¬ p2192) ∨ (¬ p2598) ∨ (¬ p3646) ∨ (¬ p4313) ∨ (¬ p4418) ∨ (¬ p4752))
    : (¬ p2136) ∨ (¬ p2192) ∨ (¬ p2598) ∨ (¬ p3646) ∨ (¬ p4313) ∨ (¬ p4418) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35940 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step61045 (p2027 p2144 p2220 p2295 p2313 p2577 p3105 p3694 p4037 p4397 p4729 : Prop)
    (h40810 : (¬ p2027))
    (h35944 : p2027 ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4037) ∨ (¬ p4397) ∨ (¬ p4729))
    : (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4037) ∨ (¬ p4397) ∨ (¬ p4729) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4397 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h35944 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step61049 (p2027 p2307 p2797 p3567 p3877 p4501 p4769 : Prop)
    (h40810 : (¬ p2027))
    (h35950 : p2027 ∨ (¬ p2307) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3877) ∨ (¬ p4501) ∨ (¬ p4769))
    : (¬ p2307) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3877) ∨ (¬ p4501) ∨ (¬ p4769) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h35950 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61050 (p1976 p2027 p2169 p2810 p3365 p3574 p3956 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h35953 : (¬ p1976) ∨ p2027 ∨ p2169 ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3574) ∨ (¬ p3956))
    : (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3574) ∨ (¬ p3956) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h35953 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61053 (p2027 p2252 p2657 p3399 p3527 p3555 p3742 p4448 p5503 p5559 : Prop)
    (h40810 : (¬ p2027))
    (h35957 : p2027 ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3555) ∨ (¬ p3742) ∨ (¬ p4448) ∨ (¬ p5503) ∨ (¬ p5559))
    : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3555) ∨ (¬ p3742) ∨ (¬ p4448) ∨ (¬ p5503) ∨ (¬ p5559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4448 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35957 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61058 (p2027 p2295 p2313 p2785 p3497 p4185 p4336 p4507 : Prop)
    (h40810 : (¬ p2027))
    (h35965 : p2027 ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2785) ∨ (¬ p3497) ∨ (¬ p4185) ∨ (¬ p4336) ∨ (¬ p4507))
    : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2785) ∨ (¬ p3497) ∨ (¬ p4185) ∨ (¬ p4336) ∨ (¬ p4507) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h35965 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step61066 (p2027 p2307 p3549 p3860 p4994 p5020 : Prop)
    (h40810 : (¬ p2027))
    (h35974 : p2027 ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3860) ∨ (¬ p4994) ∨ (¬ p5020))
    : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3860) ∨ (¬ p4994) ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4994 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35974 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61079 (p1984 p2027 p2187 p2247 p2765 p3324 p3662 p4153 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h35989 : (¬ p1984) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2247) ∨ p2765 ∨ (¬ p3324) ∨ (¬ p3662) ∨ (¬ p4153))
    : (¬ p2187) ∨ (¬ p2247) ∨ (¬ p3324) ∨ (¬ p3662) ∨ (¬ p4153) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h35989 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61080 (p1984 p2027 p2202 p2247 p2563 p3662 p3952 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h35990 : (¬ p1984) ∨ p2027 ∨ p2202 ∨ (¬ p2247) ∨ (¬ p2563) ∨ (¬ p3662) ∨ (¬ p3952))
    : (¬ p2247) ∨ (¬ p2563) ∨ (¬ p3662) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h35990 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61081 (p2027 p2132 p2241 p2619 p2750 p2753 p3146 p3817 p4366 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h35991 : p2027 ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669))
    : (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h35991 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61082 (p2027 p2274 p2563 p3549 p4512 p4629 : Prop)
    (h40810 : (¬ p2027))
    (h35992 : p2027 ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p4629))
    : (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h35992 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61089 (p2027 p2088 p2657 p3005 p3171 p3266 p3742 p4787 p4831 p5503 : Prop)
    (h40810 : (¬ p2027))
    (h36001 : p2027 ∨ (¬ p2088) ∨ (¬ p2657) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3266) ∨ (¬ p3742) ∨ (¬ p4787) ∨ (¬ p4831) ∨ (¬ p5503))
    : (¬ p2088) ∨ (¬ p2657) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3266) ∨ (¬ p3742) ∨ (¬ p4787) ∨ (¬ p4831) ∨ (¬ p5503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36001 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61095 (p2027 p2132 p2241 p2619 p2750 p2753 p3146 p3591 p4026 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h36007 : p2027 ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4604))
    : (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36007 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61100 (p2027 p2657 p3093 p3309 p3366 p3742 p3860 p3920 p3956 p4236 p4501 p5312 : Prop)
    (h40810 : (¬ p2027))
    (h36013 : p2027 ∨ (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p3742) ∨ (¬ p3860) ∨ (¬ p3920) ∨ (¬ p3956) ∨ (¬ p4236) ∨ (¬ p4501) ∨ (¬ p5312))
    : (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p3742) ∨ (¬ p3860) ∨ (¬ p3920) ∨ (¬ p3956) ∨ (¬ p4236) ∨ (¬ p4501) ∨ (¬ p5312) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h36013 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step61101 (p2027 p2144 p2220 p2241 p2750 p2753 p3105 p3591 p3694 p4026 p4397 : Prop)
    (h40810 : (¬ p2027))
    (h36014 : p2027 ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p3591) ∨ (¬ p3694) ∨ (¬ p4026) ∨ (¬ p4397))
    : (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p3591) ∨ (¬ p3694) ∨ (¬ p4026) ∨ (¬ p4397) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4397 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h36014 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step61105 (p1987 p2027 p2169 p2696 p3055 p3574 p3956 p4343 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h36019 : (¬ p1987) ∨ p2027 ∨ p2169 ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4343))
    : (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h36019 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61110 (p1991 p2027 p2169 p2498 p2657 p3319 p3461 p3742 p3956 p4278 p4444 p4669 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h36025 : (¬ p1991) ∨ p2027 ∨ p2169 ∨ (¬ p2498) ∨ (¬ p2657) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3742) ∨ (¬ p3956) ∨ (¬ p4278) ∨ (¬ p4444) ∨ (¬ p4669))
    : (¬ p2498) ∨ (¬ p2657) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3742) ∨ (¬ p3956) ∨ (¬ p4278) ∨ (¬ p4444) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2498 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p1991 := h2151;
    let u10 : (¬ p2027) := h40810;
    let u11 : (¬ p2169) := h40866;
    (Or.elim h36025 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u11 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (False.elim (r10 u8)))))))))))))))))))))))))

theorem step61125 (p1988 p2027 p2114 p2839 p2860 p3125 p3461 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h36042 : (¬ p1988) ∨ p2027 ∨ p2114 ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3461))
    : (¬ p2839) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h36042 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61127 (p2027 p3097 p3399 p3547 p3591 p4518 : Prop)
    (h40810 : (¬ p2027))
    (h36044 : p2027 ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591) ∨ (¬ p4518))
    : (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591) ∨ (¬ p4518) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3097 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3547 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36044 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61128 (p2027 p2254 p2363 p2952 p3063 p3093 p3497 p5118 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h36045 : p2027 ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3497) ∨ (¬ p5118) ∨ (¬ p5568))
    : (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3497) ∨ (¬ p5118) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36045 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61129 (p2027 p2363 p2589 p3063 p3093 p3497 p4241 p5118 p5193 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h36047 : p2027 ∨ (¬ p2363) ∨ (¬ p2589) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3497) ∨ (¬ p4241) ∨ (¬ p5118) ∨ (¬ p5193) ∨ (¬ p5568))
    : (¬ p2363) ∨ (¬ p2589) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3497) ∨ (¬ p4241) ∨ (¬ p5118) ∨ (¬ p5193) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36047 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61130 (p1988 p2027 p2284 p2388 p3105 p3680 p3758 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h36048 : (¬ p1988) ∨ p2027 ∨ (¬ p2284) ∨ p2388 ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p3758))
    : (¬ p2284) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p3758) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2388) := h40873;
    (Or.elim h36048 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61131 (p2027 p2299 p3537 p3588 p4169 p4559 p4804 : Prop)
    (h40810 : (¬ p2027))
    (h36049 : p2027 ∨ (¬ p2299) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p4169) ∨ (¬ p4559) ∨ (¬ p4804))
    : (¬ p2299) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p4169) ∨ (¬ p4559) ∨ (¬ p4804) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4804 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36049 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61133 (p2027 p2717 p2737 p3366 p3551 p3820 p4778 : Prop)
    (h40810 : (¬ p2027))
    (h36051 : p2027 ∨ (¬ p2717) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4778))
    : (¬ p2717) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36051 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61135 (p2027 p2088 p2166 p3696 p4340 p4359 p4878 : Prop)
    (h40810 : (¬ p2027))
    (h36053 : p2027 ∨ (¬ p2088) ∨ (¬ p2166) ∨ (¬ p3696) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4878))
    : (¬ p2088) ∨ (¬ p2166) ∨ (¬ p3696) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4878) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36053 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61138 (p2027 p2934 p3238 p3631 p4278 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h36057 : p2027 ∨ (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3631) ∨ (¬ p4278) ∨ (¬ p4646))
    : (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3631) ∨ (¬ p4278) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2934 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36057 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61144 (p2027 p2137 p2187 p2748 p2839 p3051 p3365 p3568 p4154 p4204 p4405 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h36063 : p2027 ∨ (¬ p2137) ∨ (¬ p2187) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4204) ∨ (¬ p4405) ∨ (¬ p4734))
    : (¬ p2137) ∨ (¬ p2187) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4204) ∨ (¬ p4405) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h36063 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step61145 (p2027 p2318 p2499 p2922 p3575 p3822 p5222 : Prop)
    (h40810 : (¬ p2027))
    (h36064 : p2027 ∨ (¬ p2318) ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3575) ∨ (¬ p3822) ∨ (¬ p5222))
    : (¬ p2318) ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3575) ∨ (¬ p3822) ∨ (¬ p5222) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36064 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61149 (p1996 p2027 p2202 p2241 p2440 p3027 p3452 p4116 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h36069 : (¬ p1996) ∨ p2027 ∨ p2202 ∨ (¬ p2241) ∨ (¬ p2440) ∨ (¬ p3027) ∨ (¬ p3452) ∨ (¬ p4116))
    : (¬ p2241) ∨ (¬ p2440) ∨ (¬ p3027) ∨ (¬ p3452) ∨ (¬ p4116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1996 := h2156;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h36069 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61150 (p2027 p2241 p2440 p3452 p4116 p4210 p4448 : Prop)
    (h40810 : (¬ p2027))
    (h36070 : p2027 ∨ (¬ p2241) ∨ (¬ p2440) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4210) ∨ (¬ p4448))
    : (¬ p2241) ∨ (¬ p2440) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4210) ∨ (¬ p4448) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4448 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36070 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61153 (p2027 p2241 p2750 p2839 p2870 p3246 p3860 p3950 p4261 : Prop)
    (h40810 : (¬ p2027))
    (h36075 : p2027 ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261))
    : (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36075 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61154 (p2027 p2132 p2241 p2750 p2753 p2870 p3032 p3246 p3553 p4366 p4668 : Prop)
    (h40810 : (¬ p2027))
    (h36076 : p2027 ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3032) ∨ (¬ p3246) ∨ (¬ p3553) ∨ (¬ p4366) ∨ (¬ p4668))
    : (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3032) ∨ (¬ p3246) ∨ (¬ p3553) ∨ (¬ p4366) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h36076 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step61155 (p2027 p3355 p3540 p4324 p4451 p5083 : Prop)
    (h40810 : (¬ p2027))
    (h36078 : p2027 ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4324) ∨ (¬ p4451) ∨ (¬ p5083))
    : (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4324) ∨ (¬ p4451) ∨ (¬ p5083) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36078 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61160 (p2027 p2139 p2881 p3051 p3365 p3941 p4035 p5119 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h36083 : p2027 ∨ (¬ p2139) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3941) ∨ (¬ p4035) ∨ (¬ p5119) ∨ (¬ p5284))
    : (¬ p2139) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3941) ∨ (¬ p4035) ∨ (¬ p5119) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2139 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36083 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61172 (p2027 p2132 p2245 p2509 p2619 p2657 p3146 p3487 p4286 p4733 p5118 : Prop)
    (h40810 : (¬ p2027))
    (h36096 : p2027 ∨ (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2509) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3487) ∨ (¬ p4286) ∨ (¬ p4733) ∨ (¬ p5118))
    : (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2509) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3487) ∨ (¬ p4286) ∨ (¬ p4733) ∨ (¬ p5118) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h36096 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step61174 (p2027 p2440 p2573 p3343 p3346 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h36098 : p2027 ∨ (¬ p2440) ∨ (¬ p2573) ∨ (¬ p3343) ∨ (¬ p3346) ∨ (¬ p4717))
    : (¬ p2440) ∨ (¬ p2573) ∨ (¬ p3343) ∨ (¬ p3346) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36098 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61175 (p2027 p2608 p2761 p3019 p3359 p3516 p3543 p3591 p3918 p4337 p4444 p4697 p4793 : Prop)
    (h40810 : (¬ p2027))
    (h36099 : p2027 ∨ (¬ p2608) ∨ (¬ p2761) ∨ (¬ p3019) ∨ (¬ p3359) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4337) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p4793))
    : (¬ p2608) ∨ (¬ p2761) ∨ (¬ p3019) ∨ (¬ p3359) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4337) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p4793) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4793 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h36099 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step61180 (p2027 p2573 p2668 p3346 p3990 p4022 p4976 : Prop)
    (h40810 : (¬ p2027))
    (h36105 : p2027 ∨ (¬ p2573) ∨ (¬ p2668) ∨ (¬ p3346) ∨ (¬ p3990) ∨ (¬ p4022) ∨ (¬ p4976))
    : (¬ p2573) ∨ (¬ p2668) ∨ (¬ p3346) ∨ (¬ p3990) ∨ (¬ p4022) ∨ (¬ p4976) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36105 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61181 (p2027 p2440 p3019 p3918 p4053 p4337 p4717 p5514 : Prop)
    (h40810 : (¬ p2027))
    (h36106 : p2027 ∨ (¬ p2440) ∨ (¬ p3019) ∨ (¬ p3918) ∨ (¬ p4053) ∨ (¬ p4337) ∨ (¬ p4717) ∨ (¬ p5514))
    : (¬ p2440) ∨ (¬ p3019) ∨ (¬ p3918) ∨ (¬ p4053) ∨ (¬ p4337) ∨ (¬ p4717) ∨ (¬ p5514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h36106 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step61184 (p1981 p2027 p2187 p2307 p2622 p3097 p3136 p3567 p4336 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h36109 : (¬ p1981) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2307) ∨ p2622 ∨ (¬ p3097) ∨ (¬ p3136) ∨ (¬ p3567) ∨ (¬ p4336))
    : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p3136) ∨ (¬ p3567) ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1981 := h2141;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2622) := h40878;
    (Or.elim h36109 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step61190 (p2027 p2220 p3556 p3644 p4042 p4277 : Prop)
    (h40810 : (¬ p2027))
    (h36116 : p2027 ∨ (¬ p2220) ∨ (¬ p3556) ∨ (¬ p3644) ∨ (¬ p4042) ∨ (¬ p4277))
    : (¬ p2220) ∨ (¬ p3556) ∨ (¬ p3644) ∨ (¬ p4042) ∨ (¬ p4277) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36116 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61193 (p1982 p2027 p2156 p2187 p2363 p2622 p2951 p3136 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h36120 : (¬ p1982) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ p2622 ∨ (¬ p2951) ∨ (¬ p3136))
    : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2951) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h36120 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61194 (p2027 p2249 p2656 p2727 p2963 p3212 p3680 p3922 p3923 p4399 p5123 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h36121 : p2027 ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3212) ∨ (¬ p3680) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p4399) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3212) ∨ (¬ p3680) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p4399) ∨ (¬ p5123) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2249 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h36121 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step61206 (p2027 p2441 p2579 p3516 p4278 p4715 p5201 : Prop)
    (h40810 : (¬ p2027))
    (h36133 : p2027 ∨ (¬ p2441) ∨ (¬ p2579) ∨ (¬ p3516) ∨ (¬ p4278) ∨ (¬ p4715) ∨ (¬ p5201))
    : (¬ p2441) ∨ (¬ p2579) ∨ (¬ p3516) ∨ (¬ p4278) ∨ (¬ p4715) ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36133 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61211 (p1982 p2027 p2622 p2685 p3032 p3276 p3516 p3543 p4444 p4636 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h36138 : (¬ p1982) ∨ p2027 ∨ p2622 ∨ (¬ p2685) ∨ (¬ p3032) ∨ (¬ p3276) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p4444) ∨ (¬ p4636))
    : (¬ p2685) ∨ (¬ p3032) ∨ (¬ p3276) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p4444) ∨ (¬ p4636) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p1982 := h2142;
    let u8 : (¬ p2027) := h40810;
    let u9 : (¬ p2622) := h40878;
    (Or.elim h36138 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u9 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step61212 (p2027 p2177 p2807 p3172 p3579 p4276 p4548 : Prop)
    (h40810 : (¬ p2027))
    (h36139 : p2027 ∨ (¬ p2177) ∨ (¬ p2807) ∨ (¬ p3172) ∨ (¬ p3579) ∨ (¬ p4276) ∨ (¬ p4548))
    : (¬ p2177) ∨ (¬ p2807) ∨ (¬ p3172) ∨ (¬ p3579) ∨ (¬ p4276) ∨ (¬ p4548) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36139 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61215 (p2027 p2140 p3434 p3556 p3587 p3690 : Prop)
    (h40810 : (¬ p2027))
    (h36142 : p2027 ∨ (¬ p2140) ∨ (¬ p3434) ∨ (¬ p3556) ∨ (¬ p3587) ∨ (¬ p3690))
    : (¬ p2140) ∨ (¬ p3434) ∨ (¬ p3556) ∨ (¬ p3587) ∨ (¬ p3690) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2140 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3587 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36142 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61219 (p2027 p2598 p2850 p2982 p3549 p3591 p4107 p4395 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h36147 : p2027 ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4733))
    : (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36147 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61222 (p2027 p2396 p2761 p3571 p4321 p4556 p5357 : Prop)
    (h40810 : (¬ p2027))
    (h36150 : p2027 ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3571) ∨ (¬ p4321) ∨ (¬ p4556) ∨ (¬ p5357))
    : (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3571) ∨ (¬ p4321) ∨ (¬ p4556) ∨ (¬ p5357) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36150 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61225 (p2027 p2230 p2440 p2663 p3172 p5008 : Prop)
    (h40810 : (¬ p2027))
    (h36153 : p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p3172) ∨ (¬ p5008))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p3172) ∨ (¬ p5008) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5008 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36153 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61227 (p2027 p2341 p2396 p3553 p3821 p4570 : Prop)
    (h40810 : (¬ p2027))
    (h36156 : p2027 ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3553) ∨ (¬ p3821) ∨ (¬ p4570))
    : (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3553) ∨ (¬ p3821) ∨ (¬ p4570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36156 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61228 (p2027 p2299 p2313 p2598 p2850 p2982 p4348 p4450 p4733 p5015 : Prop)
    (h40810 : (¬ p2027))
    (h36157 : p2027 ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p4733) ∨ (¬ p5015))
    : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p4733) ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36157 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61231 (p2020 p2027 p2341 p2396 p2997 p3821 p3941 : Prop)
    (h2180 : p2020)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h36160 : (¬ p2020) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p2396) ∨ p2997 ∨ (¬ p3821) ∨ (¬ p3941))
    : (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3821) ∨ (¬ p3941) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2020 := h2180;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h36160 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61234 (p2027 p2245 p2598 p2963 p3641 p3922 p4026 p4149 p4191 p4733 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h36164 : p2027 ∨ (¬ p2245) ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p3641) ∨ (¬ p3922) ∨ (¬ p4026) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p4733) ∨ (¬ p5119))
    : (¬ p2245) ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p3641) ∨ (¬ p3922) ∨ (¬ p4026) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p4733) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h36164 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step61236 (p1985 p2027 p2656 p2688 p2727 p2870 p3212 p4385 p4399 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h36166 : (¬ p1985) ∨ p2027 ∨ (¬ p2656) ∨ p2688 ∨ (¬ p2727) ∨ (¬ p2870) ∨ (¬ p3212) ∨ (¬ p4385) ∨ (¬ p4399))
    : (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2870) ∨ (¬ p3212) ∨ (¬ p4385) ∨ (¬ p4399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2656 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1985 := h2145;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2688) := h40880;
    (Or.elim h36166 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step61237 (p2027 p2247 p2751 p3830 p3853 p4035 : Prop)
    (h40810 : (¬ p2027))
    (h36169 : p2027 ∨ (¬ p2247) ∨ (¬ p2751) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4035))
    : (¬ p2247) ∨ (¬ p2751) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4035) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36169 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61240 (p2005 p2027 p2241 p2727 p2873 p3016 p3555 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40886 : (¬ p2873))
    (h36172 : (¬ p2005) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2727) ∨ p2873 ∨ (¬ p3016) ∨ (¬ p3555))
    : (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3016) ∨ (¬ p3555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2873) := h40886;
    (Or.elim h36172 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61245 (p2010 p2027 p2341 p2622 p2707 p2743 p3577 p3644 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h36178 : (¬ p2010) ∨ p2027 ∨ (¬ p2341) ∨ p2622 ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3577) ∨ (¬ p3644))
    : (¬ p2341) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3577) ∨ (¬ p3644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2010 := h2170;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h36178 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61246 (p1997 p2027 p2177 p2542 p2997 p3570 p3742 p4001 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h36179 : (¬ p1997) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2542) ∨ p2997 ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4001))
    : (¬ p2177) ∨ (¬ p2542) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4001) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h36179 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61247 (p2027 p2177 p2315 p3246 p3570 p3821 : Prop)
    (h40810 : (¬ p2027))
    (h36180 : p2027 ∨ (¬ p2177) ∨ (¬ p2315) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3821))
    : (¬ p2177) ∨ (¬ p2315) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3821) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36180 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61248 (p1998 p2027 p2264 p2688 p2807 p2952 p2992 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h36181 : (¬ p1998) ∨ p2027 ∨ (¬ p2264) ∨ p2688 ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p2992))
    : (¬ p2264) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h36181 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61251 (p1988 p2027 p2323 p2946 p3662 p3680 p3842 p4039 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h36184 : (¬ p1988) ∨ p2027 ∨ p2323 ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3680) ∨ (¬ p3842) ∨ (¬ p4039))
    : (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3680) ∨ (¬ p3842) ∨ (¬ p4039) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4039 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h36184 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61253 (p1997 p2027 p2177 p2542 p2997 p3543 p3548 p3742 p4279 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h36187 : (¬ p1997) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2542) ∨ p2997 ∨ (¬ p3543) ∨ (¬ p3548) ∨ (¬ p3742) ∨ (¬ p4279))
    : (¬ p2177) ∨ (¬ p2542) ∨ (¬ p3543) ∨ (¬ p3548) ∨ (¬ p3742) ∨ (¬ p4279) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1997 := h2157;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2997) := h40890;
    (Or.elim h36187 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step61255 (p1995 p2027 p2396 p2997 p3379 p3817 p4366 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h36191 : (¬ p1995) ∨ p2027 ∨ (¬ p2396) ∨ p2997 ∨ (¬ p3379) ∨ (¬ p3817) ∨ (¬ p4366))
    : (¬ p2396) ∨ (¬ p3379) ∨ (¬ p3817) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h36191 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61256 (p1980 p2027 p2331 p2952 p3105 p3474 p4208 : Prop)
    (h2140 : p1980)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h36193 : (¬ p1980) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3105) ∨ p3474 ∨ (¬ p4208))
    : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3105) ∨ (¬ p4208) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1980 := h2140;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3474) := h40898;
    (Or.elim h36193 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61260 (p1998 p2997 p3527 p5142 : Prop)
    (h2158 : p1998)
    (h40890 : (¬ p2997))
    (h36197 : (¬ p1998) ∨ p2997 ∨ (¬ p3527) ∨ p5142)
    : (¬ p3527) ∨ p5142 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5142) := (fun h => hn (Or.inr h));
    let u2 : p1998 := h2158;
    let u3 : (¬ p2997) := h40890;
    (Or.elim h36197 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step61272 (p1980 p2027 p2331 p2545 p2952 p2992 p4111 : Prop)
    (h2140 : p1980)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h36211 : (¬ p1980) ∨ p2027 ∨ (¬ p2331) ∨ p2545 ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4111))
    : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1980 := h2140;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h36211 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61273 (p2027 p2145 p2177 p2437 p2630 p2696 p3570 p3646 p4204 p4276 : Prop)
    (h40810 : (¬ p2027))
    (h36213 : p2027 ∨ (¬ p2145) ∨ (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3570) ∨ (¬ p3646) ∨ (¬ p4204) ∨ (¬ p4276))
    : (¬ p2145) ∨ (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3570) ∨ (¬ p3646) ∨ (¬ p4204) ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36213 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61277 (p1990 p2027 p2299 p2396 p2441 p2563 p2633 p4278 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h36219 : (¬ p1990) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2441) ∨ (¬ p2563) ∨ p2633 ∨ (¬ p4278))
    : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2441) ∨ (¬ p2563) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h36219 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61278 (p2027 p2619 p3969 p4371 p4512 p4875 p5693 : Prop)
    (h40810 : (¬ p2027))
    (h36220 : p2027 ∨ (¬ p2619) ∨ (¬ p3969) ∨ (¬ p4371) ∨ (¬ p4512) ∨ (¬ p4875) ∨ (¬ p5693))
    : (¬ p2619) ∨ (¬ p3969) ∨ (¬ p4371) ∨ (¬ p4512) ∨ (¬ p4875) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36220 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61279 (p2027 p2299 p2396 p2534 p4420 p4443 : Prop)
    (h40810 : (¬ p2027))
    (h36221 : p2027 ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p4420) ∨ (¬ p4443))
    : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p4420) ∨ (¬ p4443) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36221 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61282 (p1996 p2027 p2247 p2685 p2688 p3830 p3853 p4035 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h36224 : (¬ p1996) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2685) ∨ p2688 ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4035))
    : (¬ p2247) ∨ (¬ p2685) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4035) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1996 := h2156;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h36224 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61284 (p1982 p2027 p2622 p2630 p2657 p3166 p3256 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h36227 : (¬ p1982) ∨ p2027 ∨ p2622 ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p3256))
    : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h36227 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61292 (p2000 p2027 p2476 p2766 p3979 p4286 p4347 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h36242 : (¬ p2000) ∨ p2027 ∨ (¬ p2476) ∨ p2766 ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p4347))
    : (¬ p2476) ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2000 := h2160;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h36242 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61293 (p2027 p2145 p2696 p3005 p3646 p3744 p4009 p4191 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h36243 : p2027 ∨ (¬ p2145) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4009) ∨ (¬ p4191) ∨ (¬ p5119))
    : (¬ p2145) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4009) ∨ (¬ p4191) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36243 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61294 (p2027 p2145 p2651 p2810 p2951 p3136 p4117 : Prop)
    (h40810 : (¬ p2027))
    (h36244 : p2027 ∨ (¬ p2145) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p4117))
    : (¬ p2145) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36244 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61295 (p2027 p2145 p2598 p3641 p3646 p3744 p4149 p4191 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h36245 : p2027 ∨ (¬ p2145) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p5119))
    : (¬ p2145) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36245 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61297 (p2027 p2352 p2387 p2577 p3422 p4727 : Prop)
    (h40810 : (¬ p2027))
    (h36247 : p2027 ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p3422) ∨ (¬ p4727))
    : (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p3422) ∨ (¬ p4727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36247 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61298 (p1995 p2027 p2509 p2766 p3979 p4286 p4347 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h36249 : (¬ p1995) ∨ p2027 ∨ (¬ p2509) ∨ p2766 ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p4347))
    : (¬ p2509) ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h36249 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61299 (p2005 p2027 p2396 p2997 p3016 p3742 p4278 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h36250 : (¬ p2005) ∨ p2027 ∨ (¬ p2396) ∨ p2997 ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p4278))
    : (¬ p2396) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h36250 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61300 (p2005 p2027 p2396 p2493 p2928 p2997 p4278 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h36251 : (¬ p2005) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2493) ∨ (¬ p2928) ∨ p2997 ∨ (¬ p4278))
    : (¬ p2396) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h36251 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61307 (p2027 p2241 p2992 p3115 p3266 p3946 p4191 p4450 p5021 : Prop)
    (h40810 : (¬ p2027))
    (h36258 : p2027 ∨ (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3266) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4450) ∨ (¬ p5021))
    : (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3266) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4450) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36258 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61310 (p2027 p2241 p2387 p2992 p4272 p4347 p4444 p5021 p5400 : Prop)
    (h40810 : (¬ p2027))
    (h36261 : p2027 ∨ (¬ p2241) ∨ (¬ p2387) ∨ (¬ p2992) ∨ (¬ p4272) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p5021) ∨ (¬ p5400))
    : (¬ p2241) ∨ (¬ p2387) ∨ (¬ p2992) ∨ (¬ p4272) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p5021) ∨ (¬ p5400) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4272 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36261 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61311 (p2027 p3016 p3727 p4700 p4717 p5740 : Prop)
    (h40810 : (¬ p2027))
    (h36262 : p2027 ∨ (¬ p3016) ∨ (¬ p3727) ∨ (¬ p4700) ∨ (¬ p4717) ∨ (¬ p5740))
    : (¬ p3016) ∨ (¬ p3727) ∨ (¬ p4700) ∨ (¬ p4717) ∨ (¬ p5740) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36262 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61312 (p1982 p2027 p2210 p2247 p2688 p3146 p3156 p4282 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h36263 : (¬ p1982) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2247) ∨ p2688 ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4282))
    : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4282) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h36263 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61313 (p2027 p3830 p3860 p4352 p4993 p5118 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h36264 : p2027 ∨ (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4352) ∨ (¬ p4993) ∨ (¬ p5118) ∨ (¬ p5580))
    : (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4352) ∨ (¬ p4993) ∨ (¬ p5118) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4993 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36264 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61315 (p2027 p2210 p2891 p3325 p3860 p4556 p4993 : Prop)
    (h40810 : (¬ p2027))
    (h36268 : p2027 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3325) ∨ (¬ p3860) ∨ (¬ p4556) ∨ (¬ p4993))
    : (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3325) ∨ (¬ p3860) ∨ (¬ p4556) ∨ (¬ p4993) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4993 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36268 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61318 (p2027 p2230 p2387 p2663 p2778 p2819 p3276 p3917 p4322 p4397 p4449 p4786 : Prop)
    (h40810 : (¬ p2027))
    (h36272 : p2027 ∨ (¬ p2230) ∨ (¬ p2387) ∨ (¬ p2663) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p3276) ∨ (¬ p3917) ∨ (¬ p4322) ∨ (¬ p4397) ∨ (¬ p4449) ∨ (¬ p4786))
    : (¬ p2230) ∨ (¬ p2387) ∨ (¬ p2663) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p3276) ∨ (¬ p3917) ∨ (¬ p4322) ∨ (¬ p4397) ∨ (¬ p4449) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4397 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h36272 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step61320 (p2027 p2122 p2230 p2246 p2313 p2663 p2744 p3146 p3156 p3204 p3879 p3917 p3953 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h36274 : p2027 ∨ (¬ p2122) ∨ (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3204) ∨ (¬ p3879) ∨ (¬ p3917) ∨ (¬ p3953) ∨ (¬ p4604))
    : (¬ p2122) ∨ (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3204) ∨ (¬ p3879) ∨ (¬ p3917) ∨ (¬ p3953) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : (¬ p2027) := h40810;
    (Or.elim h36274 (fun q0 => (False.elim (u13 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u11))) (fun r12 => (False.elim (r12 u12)))))))))))))))))))))))))))))

theorem step61332 (p2027 p2145 p2299 p2651 p2810 p3005 p3097 p3646 p4117 p4550 : Prop)
    (h40810 : (¬ p2027))
    (h36291 : p2027 ∨ (¬ p2145) ∨ (¬ p2299) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4117) ∨ (¬ p4550))
    : (¬ p2145) ∨ (¬ p2299) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4117) ∨ (¬ p4550) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36291 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61336 (p2027 p2246 p2608 p2744 p3286 p3506 p3817 p4366 p4444 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h36296 : p2027 ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4444) ∨ (¬ p4669))
    : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4444) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36296 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61344 (p1994 p2027 p2440 p2764 p3646 p3744 p4031 p4191 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h36306 : (¬ p1994) ∨ p2027 ∨ (¬ p2440) ∨ p2764 ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4031) ∨ (¬ p4191))
    : (¬ p2440) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4031) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h36306 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61346 (p2027 p2717 p3551 p3582 p3587 p3742 p4279 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h36308 : p2027 ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3582) ∨ (¬ p3587) ∨ (¬ p3742) ∨ (¬ p4279) ∨ (¬ p4753))
    : (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3582) ∨ (¬ p3587) ∨ (¬ p3742) ∨ (¬ p4279) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3587 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h36308 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step61354 (p2027 p2311 p2386 p2717 p3551 p3574 p4753 p5085 : Prop)
    (h40810 : (¬ p2027))
    (h36316 : p2027 ∨ (¬ p2311) ∨ (¬ p2386) ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3574) ∨ (¬ p4753) ∨ (¬ p5085))
    : (¬ p2311) ∨ (¬ p2386) ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3574) ∨ (¬ p4753) ∨ (¬ p5085) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2311 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5085 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h36316 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step61357 (p2027 p2230 p2630 p3519 p3879 p4315 p4814 : Prop)
    (h40810 : (¬ p2027))
    (h36319 : p2027 ∨ (¬ p2230) ∨ (¬ p2630) ∨ (¬ p3519) ∨ (¬ p3879) ∨ (¬ p4315) ∨ (¬ p4814))
    : (¬ p2230) ∨ (¬ p2630) ∨ (¬ p3519) ∨ (¬ p3879) ∨ (¬ p4315) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36319 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61358 (p2027 p2248 p2619 p2946 p3146 p3548 p4316 p4366 p5118 p5558 : Prop)
    (h40810 : (¬ p2027))
    (h36320 : p2027 ∨ (¬ p2248) ∨ (¬ p2619) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3548) ∨ (¬ p4316) ∨ (¬ p4366) ∨ (¬ p5118) ∨ (¬ p5558))
    : (¬ p2248) ∨ (¬ p2619) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3548) ∨ (¬ p4316) ∨ (¬ p4366) ∨ (¬ p5118) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36320 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61362 (p2027 p2341 p3570 p3631 p3821 p4914 : Prop)
    (h40810 : (¬ p2027))
    (h36326 : p2027 ∨ (¬ p2341) ∨ (¬ p3570) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4914))
    : (¬ p2341) ∨ (¬ p3570) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4914) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36326 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61363 (p1984 p2027 p2766 p3266 p3591 p4026 p4191 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h36327 : (¬ p1984) ∨ p2027 ∨ p2766 ∨ (¬ p3266) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4191))
    : (¬ p3266) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h36327 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61366 (p1997 p2027 p2299 p2396 p2633 p3690 p4110 p4204 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h36331 : (¬ p1997) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2396) ∨ p2633 ∨ (¬ p3690) ∨ (¬ p4110) ∨ (¬ p4204))
    : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3690) ∨ (¬ p4110) ∨ (¬ p4204) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h36331 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61368 (p2027 p2598 p2839 p3365 p3585 p5052 : Prop)
    (h40810 : (¬ p2027))
    (h36333 : p2027 ∨ (¬ p2598) ∨ (¬ p2839) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p5052))
    : (¬ p2598) ∨ (¬ p2839) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p5052) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36333 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61370 (p2027 p2608 p3097 p3537 p3609 p3646 p4107 p4524 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h36335 : p2027 ∨ (¬ p2608) ∨ (¬ p3097) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4524) ∨ (¬ p4669))
    : (¬ p2608) ∨ (¬ p3097) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4524) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4524 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36335 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61372 (p1994 p2027 p2177 p2311 p2386 p2462 p3551 p3574 p4107 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h36337 : (¬ p1994) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2386) ∨ p2462 ∨ (¬ p3551) ∨ (¬ p3574) ∨ (¬ p4107))
    : (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2386) ∨ (¬ p3551) ∨ (¬ p3574) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1994 := h2154;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2462) := h40875;
    (Or.elim h36337 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step61373 (p2027 p2958 p3767 p4035 p4207 p4790 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h36338 : p2027 ∨ (¬ p2958) ∨ (¬ p3767) ∨ (¬ p4035) ∨ (¬ p4207) ∨ (¬ p4790) ∨ (¬ p5284))
    : (¬ p2958) ∨ (¬ p3767) ∨ (¬ p4035) ∨ (¬ p4207) ∨ (¬ p4790) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2958 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36338 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61376 (p2027 p2248 p2928 p3286 p3452 p3506 p4278 p4322 p4395 : Prop)
    (h40810 : (¬ p2027))
    (h36341 : p2027 ∨ (¬ p2248) ∨ (¬ p2928) ∨ (¬ p3286) ∨ (¬ p3452) ∨ (¬ p3506) ∨ (¬ p4278) ∨ (¬ p4322) ∨ (¬ p4395))
    : (¬ p2248) ∨ (¬ p2928) ∨ (¬ p3286) ∨ (¬ p3452) ∨ (¬ p3506) ∨ (¬ p4278) ∨ (¬ p4322) ∨ (¬ p4395) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36341 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61379 (p2027 p2598 p2850 p3425 p4106 p4644 : Prop)
    (h40810 : (¬ p2027))
    (h36348 : p2027 ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3425) ∨ (¬ p4106) ∨ (¬ p4644))
    : (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3425) ∨ (¬ p4106) ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36348 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61381 (p2027 p2696 p2753 p3506 p3645 p3646 p3755 p3989 p4877 p5123 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h36350 : p2027 ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3506) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p3989) ∨ (¬ p4877) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3506) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p3989) ∨ (¬ p4877) ∨ (¬ p5123) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h36350 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step61382 (p1997 p2027 p2323 p2542 p2630 p3286 p4035 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h36351 : (¬ p1997) ∨ p2027 ∨ p2323 ∨ (¬ p2542) ∨ (¬ p2630) ∨ (¬ p3286) ∨ (¬ p4035))
    : (¬ p2542) ∨ (¬ p2630) ∨ (¬ p3286) ∨ (¬ p4035) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h36351 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61386 (p2027 p2136 p2247 p2449 p2744 p3037 p3366 p3399 p3646 p3950 p3989 p4347 : Prop)
    (h40810 : (¬ p2027))
    (h36356 : p2027 ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2449) ∨ (¬ p2744) ∨ (¬ p3037) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p4347))
    : (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2449) ∨ (¬ p2744) ∨ (¬ p3037) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h36356 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step61393 (p2027 p2230 p2440 p2579 p4375 p4390 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h36364 : p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p4375) ∨ (¬ p4390) ∨ (¬ p4753))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p4375) ∨ (¬ p4390) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36364 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61395 (p1994 p2027 p2230 p2440 p2764 p3346 p4322 p4947 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h36367 : (¬ p1994) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ p2764 ∨ (¬ p3346) ∨ (¬ p4322) ∨ (¬ p4947))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3346) ∨ (¬ p4322) ∨ (¬ p4947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h36367 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61396 (p2027 p2696 p2787 p3115 p3136 p3266 p3946 p4191 p4450 : Prop)
    (h40810 : (¬ p2027))
    (h36368 : p2027 ∨ (¬ p2696) ∨ (¬ p2787) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3266) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4450))
    : (¬ p2696) ∨ (¬ p2787) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3266) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36368 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61398 (p2027 p2230 p2440 p3343 p3591 p3923 p4332 p4347 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h36370 : p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3343) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3343) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36370 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61400 (p2027 p2417 p3556 p3690 p3741 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h36372 : p2027 ∨ (¬ p2417) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p3741) ∨ (¬ p4533))
    : (¬ p2417) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p3741) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36372 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61403 (p1983 p2027 p2230 p2233 p2417 p2437 p2440 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h36375 : (¬ p1983) ∨ p2027 ∨ (¬ p2230) ∨ p2233 ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2440))
    : (¬ p2230) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2233) := h40868;
    (Or.elim h36375 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61404 (p2027 p2470 p2663 p2761 p3343 p3425 p4256 p4638 p4786 p5228 p5387 : Prop)
    (h40810 : (¬ p2027))
    (h36376 : p2027 ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2761) ∨ (¬ p3343) ∨ (¬ p3425) ∨ (¬ p4256) ∨ (¬ p4638) ∨ (¬ p4786) ∨ (¬ p5228) ∨ (¬ p5387))
    : (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2761) ∨ (¬ p3343) ∨ (¬ p3425) ∨ (¬ p4256) ∨ (¬ p4638) ∨ (¬ p4786) ∨ (¬ p5228) ∨ (¬ p5387) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h36376 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step61405 (p2027 p2417 p3016 p3821 p4112 p4155 p4708 : Prop)
    (h40810 : (¬ p2027))
    (h36377 : p2027 ∨ (¬ p2417) ∨ (¬ p3016) ∨ (¬ p3821) ∨ (¬ p4112) ∨ (¬ p4155) ∨ (¬ p4708))
    : (¬ p2417) ∨ (¬ p3016) ∨ (¬ p3821) ∨ (¬ p4112) ∨ (¬ p4155) ∨ (¬ p4708) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4708 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36377 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61411 (p1982 p2027 p2248 p2313 p2633 p2946 p3146 p3156 p3434 p3659 p4107 p5015 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h36383 : (¬ p1982) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p2313) ∨ p2633 ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p4107) ∨ (¬ p5015))
    : (¬ p2248) ∨ (¬ p2313) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p4107) ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p1982 := h2142;
    let u10 : (¬ p2027) := h40810;
    let u11 : (¬ p2633) := h40879;
    (Or.elim h36383 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u11 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (False.elim (r10 u8)))))))))))))))))))))))))

theorem step61412 (p2027 p3016 p3878 p3998 p4109 p4238 p4717 p5600 : Prop)
    (h40810 : (¬ p2027))
    (h36384 : p2027 ∨ (¬ p3016) ∨ (¬ p3878) ∨ (¬ p3998) ∨ (¬ p4109) ∨ (¬ p4238) ∨ (¬ p4717) ∨ (¬ p5600))
    : (¬ p3016) ∨ (¬ p3878) ∨ (¬ p3998) ∨ (¬ p4109) ∨ (¬ p4238) ∨ (¬ p4717) ∨ (¬ p5600) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h36384 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step61414 (p1985 p2027 p2202 p2341 p2922 p3238 p3570 p3575 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h36386 : (¬ p1985) ∨ p2027 ∨ p2202 ∨ (¬ p2341) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3570) ∨ (¬ p3575))
    : (¬ p2341) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3570) ∨ (¬ p3575) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1985 := h2145;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h36386 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61415 (p1985 p2027 p2766 p3570 p4181 p4347 p4993 p5558 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h36387 : (¬ p1985) ∨ p2027 ∨ p2766 ∨ (¬ p3570) ∨ (¬ p4181) ∨ (¬ p4347) ∨ (¬ p4993) ∨ (¬ p5558))
    : (¬ p3570) ∨ (¬ p4181) ∨ (¬ p4347) ∨ (¬ p4993) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3570 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4993 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1985 := h2145;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h36387 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61417 (p2027 p2274 p2396 p3989 p4138 p4668 : Prop)
    (h40810 : (¬ p2027))
    (h36391 : p2027 ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3989) ∨ (¬ p4138) ∨ (¬ p4668))
    : (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3989) ∨ (¬ p4138) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36391 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61425 (p2027 p2685 p2753 p2946 p3379 p3549 p3591 p4117 p4315 p4570 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h36399 : p2027 ∨ (¬ p2685) ∨ (¬ p2753) ∨ (¬ p2946) ∨ (¬ p3379) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4570) ∨ (¬ p5216))
    : (¬ p2685) ∨ (¬ p2753) ∨ (¬ p2946) ∨ (¬ p3379) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4570) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h36399 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step61426 (p2027 p2241 p2449 p3027 p3055 p3584 p4137 p4625 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h36400 : p2027 ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4736))
    : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36400 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61429 (p2027 p2668 p2696 p2753 p2797 p3379 p3549 p3591 p4405 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h36403 : p2027 ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3379) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4405) ∨ (¬ p5216))
    : (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3379) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4405) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36403 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61431 (p2027 p2230 p2440 p2780 p3343 p3822 p4107 p4395 p4419 p4952 : Prop)
    (h40810 : (¬ p2027))
    (h36405 : p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2780) ∨ (¬ p3343) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4419) ∨ (¬ p4952))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2780) ∨ (¬ p3343) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4419) ∨ (¬ p4952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36405 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61434 (p2027 p2241 p2449 p3027 p3346 p3461 p4425 p4625 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h36408 : p2027 ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3346) ∨ (¬ p3461) ∨ (¬ p4425) ∨ (¬ p4625) ∨ (¬ p5193))
    : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3346) ∨ (¬ p3461) ∨ (¬ p4425) ∨ (¬ p4625) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36408 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61439 (p2027 p2230 p2780 p3276 p3822 p4107 p4322 p4395 p4419 p4449 : Prop)
    (h40810 : (¬ p2027))
    (h36413 : p2027 ∨ (¬ p2230) ∨ (¬ p2780) ∨ (¬ p3276) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4322) ∨ (¬ p4395) ∨ (¬ p4419) ∨ (¬ p4449))
    : (¬ p2230) ∨ (¬ p2780) ∨ (¬ p3276) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4322) ∨ (¬ p4395) ∨ (¬ p4419) ∨ (¬ p4449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36413 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61440 (p2027 p2449 p2696 p2742 p3027 p3583 p4322 p4385 p4394 p4625 p4737 p5252 : Prop)
    (h40810 : (¬ p2027))
    (h36414 : p2027 ∨ (¬ p2449) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3583) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4394) ∨ (¬ p4625) ∨ (¬ p4737) ∨ (¬ p5252))
    : (¬ p2449) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3583) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4394) ∨ (¬ p4625) ∨ (¬ p4737) ∨ (¬ p5252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4394 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h36414 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step61451 (p2027 p2246 p2608 p2744 p2946 p3156 p3834 p3969 p4321 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h36425 : p2027 ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3834) ∨ (¬ p3969) ∨ (¬ p4321) ∨ (¬ p5119))
    : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3834) ∨ (¬ p3969) ∨ (¬ p4321) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36425 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61452 (p2011 p2027 p2299 p2396 p2633 p2761 p4322 : Prop)
    (h2171 : p2011)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h36426 : (¬ p2011) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2396) ∨ p2633 ∨ (¬ p2761) ∨ (¬ p4322))
    : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2011 := h2171;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h36426 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61454 (p2027 p2210 p2598 p2753 p3641 p3860 p4149 p4261 p4877 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h36429 : p2027 ∨ (¬ p2210) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3641) ∨ (¬ p3860) ∨ (¬ p4149) ∨ (¬ p4261) ∨ (¬ p4877) ∨ (¬ p5122))
    : (¬ p2210) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3641) ∨ (¬ p3860) ∨ (¬ p4149) ∨ (¬ p4261) ∨ (¬ p4877) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36429 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61457 (p2027 p2470 p3346 p3609 p4440 p5375 : Prop)
    (h40810 : (¬ p2027))
    (h36432 : p2027 ∨ (¬ p2470) ∨ (¬ p3346) ∨ (¬ p3609) ∨ (¬ p4440) ∨ (¬ p5375))
    : (¬ p2470) ∨ (¬ p3346) ∨ (¬ p3609) ∨ (¬ p4440) ∨ (¬ p5375) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36432 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61458 (p1985 p2027 p2264 p2323 p2663 p3355 p3359 p3570 p3580 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h36434 : (¬ p1985) ∨ p2027 ∨ (¬ p2264) ∨ p2323 ∨ (¬ p2663) ∨ (¬ p3355) ∨ (¬ p3359) ∨ (¬ p3570) ∨ (¬ p3580))
    : (¬ p2264) ∨ (¬ p2663) ∨ (¬ p3355) ∨ (¬ p3359) ∨ (¬ p3570) ∨ (¬ p3580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1985 := h2145;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2323) := h40870;
    (Or.elim h36434 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step61467 (p2027 p2299 p3549 p3591 p4588 p5242 : Prop)
    (h40810 : (¬ p2027))
    (h36443 : p2027 ∨ (¬ p2299) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4588) ∨ (¬ p5242))
    : (¬ p2299) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4588) ∨ (¬ p5242) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36443 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61468 (p2027 p2177 p2696 p3115 p3136 p3551 p4107 p4395 p5260 : Prop)
    (h40810 : (¬ p2027))
    (h36444 : p2027 ∨ (¬ p2177) ∨ (¬ p2696) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5260))
    : (¬ p2177) ∨ (¬ p2696) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5260) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36444 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61472 (p1995 p2027 p3379 p3498 p3860 p4149 p5693 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40899 : (¬ p3498))
    (h36448 : (¬ p1995) ∨ p2027 ∨ (¬ p3379) ∨ p3498 ∨ (¬ p3860) ∨ (¬ p4149) ∨ (¬ p5693))
    : (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4149) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3379 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3498) := h40899;
    (Or.elim h36448 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61478 (p1976 p2027 p2764 p3055 p3876 p4278 p4381 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h36455 : (¬ p1976) ∨ p2027 ∨ p2764 ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4381))
    : (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h36455 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61480 (p1996 p2027 p2509 p2922 p3498 p3516 p3575 p3947 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40899 : (¬ p3498))
    (h36457 : (¬ p1996) ∨ p2027 ∨ (¬ p2509) ∨ (¬ p2922) ∨ p3498 ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p3947))
    : (¬ p2509) ∨ (¬ p2922) ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1996 := h2156;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3498) := h40899;
    (Or.elim h36457 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61485 (p2027 p2246 p2331 p2608 p2668 p2744 p3860 p3979 p4261 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h36462 : p2027 ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2608) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3860) ∨ (¬ p3979) ∨ (¬ p4261) ∨ (¬ p5122))
    : (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2608) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3860) ∨ (¬ p3979) ∨ (¬ p4261) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36462 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61488 (p2027 p2493 p2982 p4202 p4363 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h36465 : p2027 ∨ (¬ p2493) ∨ (¬ p2982) ∨ (¬ p4202) ∨ (¬ p4363) ∨ (¬ p4717))
    : (¬ p2493) ∨ (¬ p2982) ∨ (¬ p4202) ∨ (¬ p4363) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36465 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61490 (p2027 p3367 p3389 p3583 p3698 p3759 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h36467 : p2027 ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p3759) ∨ (¬ p4646))
    : (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p3759) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36467 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61491 (p2027 p2299 p2313 p2417 p2598 p2785 p2922 p3590 p3688 p4668 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h36468 : p2027 ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2785) ∨ (¬ p2922) ∨ (¬ p3590) ∨ (¬ p3688) ∨ (¬ p4668) ∨ (¬ p4737))
    : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2785) ∨ (¬ p2922) ∨ (¬ p3590) ∨ (¬ p3688) ∨ (¬ p4668) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h36468 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step61492 (p1995 p2027 p2177 p2997 p3379 p3548 p4366 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h36469 : (¬ p1995) ∨ p2027 ∨ (¬ p2177) ∨ p2997 ∨ (¬ p3379) ∨ (¬ p3548) ∨ (¬ p4366))
    : (¬ p2177) ∨ (¬ p3379) ∨ (¬ p3548) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h36469 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step61493 (p2027 p2829 p2850 p3238 p3475 p4257 p4845 : Prop)
    (h40810 : (¬ p2027))
    (h36470 : p2027 ∨ (¬ p2829) ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p3475) ∨ (¬ p4257) ∨ (¬ p4845))
    : (¬ p2829) ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p3475) ∨ (¬ p4257) ∨ (¬ p4845) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h36470 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step61494 (p1975 p2027 p2252 p2295 p2622 p2641 p2952 p3136 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h36473 : (¬ p1975) ∨ p2027 ∨ (¬ p2252) ∨ (¬ p2295) ∨ p2622 ∨ (¬ p2641) ∨ (¬ p2952) ∨ (¬ p3136))
    : (¬ p2252) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2952) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h36473 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61497 (p2027 p2717 p3347 p3487 p3551 p4315 p4701 p4781 p5197 : Prop)
    (h40810 : (¬ p2027))
    (h36476 : p2027 ∨ (¬ p2717) ∨ (¬ p3347) ∨ (¬ p3487) ∨ (¬ p3551) ∨ (¬ p4315) ∨ (¬ p4701) ∨ (¬ p4781) ∨ (¬ p5197))
    : (¬ p2717) ∨ (¬ p3347) ∨ (¬ p3487) ∨ (¬ p3551) ∨ (¬ p4315) ∨ (¬ p4701) ∨ (¬ p4781) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4701 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h36476 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step61499 (p1976 p2027 p2633 p3055 p3367 p3588 p3644 p4106 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h36478 : (¬ p1976) ∨ p2027 ∨ p2633 ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3644) ∨ (¬ p4106))
    : (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3644) ∨ (¬ p4106) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h36478 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step61500 (p2027 p2246 p2264 p2807 p3645 p3646 p3744 p3941 p4191 p4959 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h36479 : p2027 ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3941) ∨ (¬ p4191) ∨ (¬ p4959) ∨ (¬ p5119))
    : (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3941) ∨ (¬ p4191) ∨ (¬ p4959) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h36479 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step61502 (p2027 p2177 p2311 p2608 p2839 p3105 p3551 p4107 p4395 p5021 : Prop)
    (h40810 : (¬ p2027))
    (h36481 : p2027 ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5021))
    : (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h36481 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step61503 (p2027 p2449 p2881 p3553 p4277 p4278 : Prop)
    (h40810 : (¬ p2027))
    (h36482 : p2027 ∨ (¬ p2449) ∨ (¬ p2881) ∨ (¬ p3553) ∨ (¬ p4277) ∨ (¬ p4278))
    : (¬ p2449) ∨ (¬ p2881) ∨ (¬ p3553) ∨ (¬ p4277) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36482 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step61504 (p2027 p2177 p2449 p3553 p4276 p4278 : Prop)
    (h40810 : (¬ p2027))
    (h36483 : p2027 ∨ (¬ p2177) ∨ (¬ p2449) ∨ (¬ p3553) ∨ (¬ p4276) ∨ (¬ p4278))
    : (¬ p2177) ∨ (¬ p2449) ∨ (¬ p3553) ∨ (¬ p4276) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h36483 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

end ElevenRUP
