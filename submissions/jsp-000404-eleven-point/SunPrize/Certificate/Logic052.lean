import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step99557 (p2363 p2528 p2534 p2573 p2579 p2608 p3347 p3399 p3527 p3573 p3954 p4503 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73268 : p2534 ∨ p2528)
    (h73274 : p2579 ∨ p2573)
    (h72208 : (¬ p3573) ∨ (¬ p3399) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p2363) ∨ (¬ p4503) ∨ (¬ p3527) ∨ (¬ p2534) ∨ (¬ p2579))
    : p2608 ∨ p2528 ∨ (¬ p3399) ∨ (¬ p2363) ∨ p2573 ∨ (¬ p3347) ∨ (¬ p4503) ∨ (¬ p3573) ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h72208 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u11)))))))))))))))))))

theorem step99558 (p2528 p2534 p2630 p2696 p2810 p3083 p3365 p4256 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h73316 : p2810 ∨ p2630)
    (h73390 : p3365 ∨ p2696)
    (h42985 : (¬ p2534) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4256))
    : p2528 ∨ p3083 ∨ p2630 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42985 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step99559 (p2246 p2470 p2476 p2528 p2534 p2630 p2662 p2751 p2810 p2901 p2946 p3246 p3950 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73250 : p2476 ∨ p2470)
    (h73268 : p2534 ∨ p2528)
    (h60933 : (¬ p2246) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3950))
    : (¬ p2246) ∨ (¬ p3246) ∨ p2630 ∨ p2470 ∨ (¬ p2901) ∨ (¬ p2662) ∨ (¬ p2751) ∨ (¬ p3950) ∨ p2528 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h60933 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step99566 (p2459 p2528 p2534 p2598 p3055 p3641 p3874 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73484 : p3874 ∨ p3641)
    (h73350 : p3055 ∨ p2598)
    (h45762 : (¬ p2459) ∨ (¬ p2534) ∨ (¬ p3055) ∨ (¬ p3874))
    : p2528 ∨ p3641 ∨ p2598 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45762 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step99567 (p2459 p2509 p2528 p2534 p3379 p3452 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73394 : p3452 ∨ p3379)
    (h44640 : (¬ p2459) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3452))
    : (¬ p2509) ∨ p2528 ∨ p3379 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44640 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step99572 (p3266 p5120 p5122 : Prop)
    (h73928 : p5120 ∨ (¬ p3266))
    (h8653 : (¬ p5120) ∨ p5122)
    : (¬ p3266) ∨ p5122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5122) := (fun h => hn (Or.inr h));
    let u2 : p5120 := (Or.elim h73928 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8653 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99573 (p3266 p5120 p5123 : Prop)
    (h73928 : p5120 ∨ (¬ p3266))
    (h8654 : (¬ p5120) ∨ p5123)
    : (¬ p3266) ∨ p5123 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5123) := (fun h => hn (Or.inr h));
    let u2 : p5120 := (Or.elim h73928 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8654 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99576 (p2241 p2992 p3115 p3266 p3461 p3654 p3946 p4191 p4450 p5021 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73492 : p3946 ∨ p3654)
    (h61307 : (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3266) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4450) ∨ (¬ p5021))
    : p3461 ∨ (¬ p3266) ∨ (¬ p3115) ∨ (¬ p2992) ∨ p3654 ∨ (¬ p2241) ∨ (¬ p4450) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61307 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step99577 (p3266 p3276 p3422 p4425 p5160 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h53023 : (¬ p3266) ∨ (¬ p3422) ∨ (¬ p4425) ∨ (¬ p5160))
    : p3276 ∨ (¬ p3266) ∨ (¬ p3422) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53023 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step99578 (p2144 p2156 p2860 p3105 p3266 p3276 p3346 p3758 p4425 p4450 p4729 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73456 : p3758 ∨ p2860)
    (h62642 : (¬ p2144) ∨ (¬ p2156) ∨ (¬ p3105) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3758) ∨ (¬ p4425) ∨ (¬ p4450) ∨ (¬ p4729))
    : p3276 ∨ (¬ p3266) ∨ (¬ p2156) ∨ (¬ p4729) ∨ (¬ p3105) ∨ (¬ p2144) ∨ (¬ p3346) ∨ p2860 ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62642 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step99579 (p2685 p2807 p3266 p3276 p3346 p3572 p3755 p4117 p4425 p4729 p5109 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73420 : p3572 ∨ p2685)
    (h51349 : (¬ p2807) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3572) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p4425) ∨ (¬ p4729) ∨ (¬ p5109))
    : (¬ p3755) ∨ (¬ p5109) ∨ (¬ p4729) ∨ (¬ p3266) ∨ p3276 ∨ (¬ p3346) ∨ p2685 ∨ (¬ p2807) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51349 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step99585 (p2177 p2396 p2761 p3266 p4107 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73514 : p4107 ∨ p2396)
    (h45446 : (¬ p2177) ∨ (¬ p3266) ∨ (¬ p4107) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3266) ∨ (¬ p2177) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45446 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99587 (p3073 p3266 p3379 p3449 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h57894 : (¬ p3073) ∨ (¬ p3266) ∨ (¬ p3449) ∨ (¬ p3452))
    : (¬ p3073) ∨ (¬ p3266) ∨ p3379 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57894 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99592 (p2139 p2220 p2685 p2696 p3146 p3266 p3365 p3572 p4391 p4831 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h73390 : p3365 ∨ p2696)
    (h51160 : (¬ p2139) ∨ (¬ p2220) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p4391) ∨ (¬ p4831))
    : (¬ p4391) ∨ p2685 ∨ (¬ p2220) ∨ (¬ p4831) ∨ p2696 ∨ (¬ p2139) ∨ (¬ p3146) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4391 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51160 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step99594 (p2459 p3266 p3276 p4045 p4420 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h58567 : (¬ p2459) ∨ (¬ p3266) ∨ (¬ p4045) ∨ (¬ p4420) ∨ (¬ p4425))
    : p3276 ∨ (¬ p4045) ∨ (¬ p3266) ∨ (¬ p4420) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p4045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h58567 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99598 (p3266 p3286 p3292 p3366 p3379 p3399 p3452 p3631 p3950 p4236 p4376 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h73394 : p3452 ∨ p3379)
    (h54533 : (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5284))
    : (¬ p3399) ∨ (¬ p5284) ∨ (¬ p3266) ∨ (¬ p4376) ∨ p3286 ∨ p3379 ∨ (¬ p3631) ∨ (¬ p4236) ∨ (¬ p3950) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h54533 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step99607 (p3367 p5215 p5217 : Prop)
    (h73962 : p5215 ∨ (¬ p3367))
    (h8861 : (¬ p5215) ∨ p5217)
    : (¬ p3367) ∨ p5217 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5217) := (fun h => hn (Or.inr h));
    let u2 : p5215 := (Or.elim h73962 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8861 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99608 (p2839 p4418 p4873 : Prop)
    (h73802 : p4873 ∨ p2839)
    (h8016 : p4418 ∨ (¬ p4873))
    : p4418 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4418) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr h));
    let u2 : p4873 := (Or.elim h73802 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h8016 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step99609 (p2839 p4377 p4873 : Prop)
    (h73802 : p4873 ∨ p2839)
    (h8018 : p4377 ∨ (¬ p4873))
    : p4377 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4377) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr h));
    let u2 : p4873 := (Or.elim h73802 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h8018 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step99610 (p2839 p4873 p4875 : Prop)
    (h73802 : p4873 ∨ p2839)
    (h8019 : (¬ p4873) ∨ p4875)
    : p2839 ∨ p4875 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4875) := (fun h => hn (Or.inr h));
    let u2 : p4873 := (Or.elim h73802 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8019 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99611 (p2839 p4418 p5929 : Prop)
    (h74245 : p2839 ∨ (¬ p5929))
    (h12561 : p4418 ∨ p5929)
    : p4418 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4418) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5929) := (Or.elim h74245 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12561 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step99612 (p2252 p2373 p2459 p2598 p2750 p2753 p2850 p3166 p3172 p3256 p4118 p4902 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73520 : p4118 ∨ p3256)
    (h65194 : (¬ p2252) ∨ (¬ p2373) ∨ (¬ p2459) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4902))
    : p3166 ∨ p3256 ∨ (¬ p2598) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2373) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p4902) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h65194 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step99615 (p2598 p2641 p2696 p2748 p3365 p3683 p4154 p4972 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73526 : p4154 ∨ p2641)
    (h55285 : (¬ p2598) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3683) ∨ (¬ p4154) ∨ (¬ p4972))
    : (¬ p2598) ∨ p2696 ∨ (¬ p3683) ∨ p2641 ∨ (¬ p2748) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55285 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step99624 (p2449 p2598 p2685 p2737 p2743 p2911 p2922 p3572 p3590 p3947 p4666 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73420 : p3572 ∨ p2685)
    (h73298 : p2743 ∨ p2737)
    (h72211 : (¬ p3947) ∨ (¬ p2911) ∨ (¬ p3572) ∨ (¬ p2922) ∨ (¬ p4666) ∨ (¬ p2743) ∨ (¬ p3590) ∨ (¬ p2598))
    : p2449 ∨ (¬ p2911) ∨ p2685 ∨ (¬ p2598) ∨ (¬ p4666) ∨ (¬ p2922) ∨ (¬ p3590) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h72211 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step99627 (p2132 p2138 p2598 p2737 p3367 p3585 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73428 : p3585 ∨ p3367)
    (h42802 : (¬ p2138) ∨ (¬ p2598) ∨ (¬ p2737) ∨ (¬ p3585))
    : (¬ p2737) ∨ p2132 ∨ (¬ p2598) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42802 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step99628 (p2598 p2737 p3136 p3367 p3585 p3589 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h43179 : (¬ p2598) ∨ (¬ p2737) ∨ (¬ p3136) ∨ (¬ p3585) ∨ (¬ p3589))
    : (¬ p2737) ∨ (¬ p3136) ∨ p3367 ∨ (¬ p3589) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43179 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step99629 (p2598 p2737 p2797 p3367 p3585 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h48550 : (¬ p2598) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3585))
    : (¬ p2797) ∨ (¬ p2737) ∨ (¬ p2598) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48550 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99631 (p2553 p2598 p2829 p3367 p3585 p4390 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h42807 : (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p4390))
    : (¬ p2829) ∨ (¬ p2553) ∨ (¬ p4390) ∨ (¬ p2598) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42807 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99632 (p2417 p2598 p2707 p3367 p3585 p3658 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h42880 : (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658))
    : (¬ p3658) ∨ (¬ p2707) ∨ (¬ p2598) ∨ p3367 ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3658 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42880 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step99633 (p2598 p2707 p3367 p3434 p3585 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h58511 : (¬ p2598) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3585))
    : (¬ p2707) ∨ (¬ p3434) ∨ p3367 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58511 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99634 (p2254 p2331 p2363 p2598 p2668 p2707 p2717 p2963 p3324 p3367 p3585 p3589 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73386 : p3324 ∨ p2668)
    (h73428 : p3585 ∨ p3367)
    (h73338 : p2963 ∨ p2331)
    (h49295 : (¬ p2254) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4347))
    : (¬ p2717) ∨ p2363 ∨ (¬ p3589) ∨ p2668 ∨ (¬ p2707) ∨ (¬ p2598) ∨ (¬ p2254) ∨ p3367 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h49295 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step99635 (p2098 p2104 p2528 p2534 p2598 p3367 p3585 p5369 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h73268 : p2534 ∨ p2528)
    (h73428 : p3585 ∨ p3367)
    (h43018 : (¬ p2104) ∨ (¬ p2534) ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p5369))
    : p2098 ∨ p2528 ∨ p3367 ∨ (¬ p2598) ∨ (¬ p5369) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43018 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step99638 (p2850 p3698 p4880 : Prop)
    (h73806 : p4880 ∨ p2850)
    (h8033 : p3698 ∨ (¬ p4880))
    : p3698 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3698) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr h));
    let u2 : p4880 := (Or.elim h73806 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h8033 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step99639 (p2850 p4880 p4882 : Prop)
    (h73806 : p4880 ∨ p2850)
    (h8036 : (¬ p4880) ∨ p4882)
    : p2850 ∨ p4882 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4882) := (fun h => hn (Or.inr h));
    let u2 : p4880 := (Or.elim h73806 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8036 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99643 (p2598 p3363 p5882 : Prop)
    (h74183 : (¬ p2598) ∨ (¬ p5882))
    (h12282 : p3363 ∨ p5882)
    : p3363 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3363) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5882) := (Or.elim h74183 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12282 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step99646 (p2630 p2810 p4752 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h49245 : (¬ p2810) ∨ p4752)
    : p2630 ∨ p4752 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4752) := (fun h => hn (Or.inr h));
    let u2 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49245 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99647 (p2470 p2476 p2484 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h45967 : (¬ p2476) ∨ p2484)
    : p2470 ∨ p2484 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2484) := (fun h => hn (Or.inr h));
    let u2 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45967 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99649 (p2470 p2476 p4610 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h47381 : (¬ p2476) ∨ p4610)
    : p2470 ∨ p4610 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4610) := (fun h => hn (Or.inr h));
    let u2 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47381 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99654 (p2241 p2440 p2470 p2476 p3083 p4108 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h52621 : (¬ p2241) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p4108))
    : p2470 ∨ (¬ p2241) ∨ (¬ p4108) ∨ (¬ p2440) ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h52621 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99655 (p2839 p3583 p4878 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h48280 : (¬ p3583) ∨ p4878)
    : p2839 ∨ p4878 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4878) := (fun h => hn (Or.inr h));
    let u2 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48280 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99656 (p2839 p3583 p4877 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h48402 : (¬ p3583) ∨ p4877)
    : p2839 ∨ p4877 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4877) := (fun h => hn (Or.inr h));
    let u2 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48402 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99663 (p2284 p2707 p2839 p3583 p3952 p4316 p4344 p4558 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73496 : p3952 ∨ p2284)
    (h51569 : (¬ p2707) ∨ (¬ p3583) ∨ (¬ p3952) ∨ (¬ p4316) ∨ (¬ p4344) ∨ (¬ p4558))
    : (¬ p2707) ∨ (¬ p4558) ∨ (¬ p4316) ∨ p2839 ∨ p2284 ∨ (¬ p4344) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51569 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step99664 (p2284 p2829 p2839 p3583 p3952 p4185 p5053 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73424 : p3583 ∨ p2839)
    (h60945 : (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3952) ∨ (¬ p4185) ∨ (¬ p5053))
    : (¬ p2829) ∨ p2284 ∨ (¬ p4185) ∨ p2839 ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60945 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step99665 (p2707 p2839 p2901 p3583 p4320 p4344 p5053 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73424 : p3583 ∨ p2839)
    (h63652 : (¬ p2707) ∨ (¬ p3583) ∨ (¬ p4320) ∨ (¬ p4344) ∨ (¬ p5053))
    : (¬ p2707) ∨ p2901 ∨ (¬ p5053) ∨ p2839 ∨ (¬ p4344) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63652 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99668 (p2563 p2829 p2839 p3583 p4110 p4185 p4316 p4705 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73516 : p4110 ∨ p2563)
    (h42105 : (¬ p2829) ∨ (¬ p3583) ∨ (¬ p4110) ∨ (¬ p4185) ∨ (¬ p4316) ∨ (¬ p4705))
    : (¬ p2829) ∨ p2839 ∨ (¬ p4185) ∨ (¬ p4316) ∨ (¬ p4705) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42105 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step99669 (p2427 p2707 p2839 p3583 p4235 p4344 p4885 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73536 : p4235 ∨ p2427)
    (h48007 : (¬ p2707) ∨ (¬ p3583) ∨ (¬ p4235) ∨ (¬ p4344) ∨ (¬ p4885))
    : (¬ p2707) ∨ (¬ p4344) ∨ p2839 ∨ (¬ p4885) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48007 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step99670 (p2177 p2274 p2829 p2839 p3583 p4185 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h50266 : (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p4185))
    : (¬ p2829) ∨ (¬ p2274) ∨ (¬ p4185) ∨ p2839 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50266 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99671 (p2440 p2542 p2819 p2829 p2839 p3583 p3698 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73424 : p3583 ∨ p2839)
    (h55123 : (¬ p2542) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3698))
    : (¬ p2829) ∨ (¬ p2819) ∨ p2440 ∨ (¬ p3698) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55123 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step99672 (p2140 p2156 p2829 p2839 p3583 p3646 p4185 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73436 : p3646 ∨ p2156)
    (h53456 : (¬ p2140) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p4185))
    : (¬ p2829) ∨ (¬ p4185) ∨ p2839 ∨ p2156 ∨ (¬ p2140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53456 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step99675 (p2140 p2707 p2839 p3051 p3556 p3583 p4344 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73424 : p3583 ∨ p2839)
    (h50442 : (¬ p2140) ∨ (¬ p2707) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p4344))
    : (¬ p2707) ∨ p3051 ∨ (¬ p4344) ∨ p2839 ∨ (¬ p2140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50442 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99679 (p2518 p2839 p3364 p3541 p3583 p3641 p3874 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73484 : p3874 ∨ p3641)
    (h67263 : (¬ p3583) ∨ (¬ p3364) ∨ (¬ p2518) ∨ (¬ p3541) ∨ (¬ p3874))
    : (¬ p2518) ∨ (¬ p3541) ∨ p2839 ∨ p3641 ∨ (¬ p3364) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67263 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step99680 (p2187 p2839 p3125 p3583 p3917 p3989 p4193 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73502 : p3989 ∨ p2187)
    (h43857 : (¬ p3125) ∨ (¬ p3583) ∨ (¬ p3917) ∨ (¬ p3989) ∨ (¬ p4193))
    : (¬ p3125) ∨ (¬ p3917) ∨ (¬ p4193) ∨ p2839 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43857 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99681 (p2829 p2839 p3583 p3688 p4193 : Prop)
    (h73443 : (¬ p2829) ∨ (¬ p3688))
    (h73424 : p3583 ∨ p2839)
    (h25967 : (¬ p3583) ∨ p3688 ∨ (¬ p4193))
    : (¬ p2829) ∨ (¬ p4193) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3688) := (Or.elim h73443 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h25967 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step99687 (p2187 p2274 p2819 p2839 p3097 p3583 p4193 p4358 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73352 : p3097 ∨ p2274)
    (h73564 : p4358 ∨ p2819)
    (h45288 : (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p4193) ∨ (¬ p4358))
    : (¬ p4193) ∨ (¬ p2187) ∨ p2839 ∨ p2274 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45288 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step99688 (p2563 p2737 p2839 p2860 p3583 p3758 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h73424 : p3583 ∨ p2839)
    (h62068 : (¬ p2563) ∨ (¬ p2737) ∨ (¬ p3583) ∨ (¬ p3758))
    : (¬ p2737) ∨ p2860 ∨ p2839 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62068 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99689 (p2284 p2737 p2839 p2860 p3583 p3758 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73456 : p3758 ∨ p2860)
    (h45925 : (¬ p2284) ∨ (¬ p2737) ∨ (¬ p3583) ∨ (¬ p3758))
    : (¬ p2284) ∨ (¬ p2737) ∨ p2839 ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45925 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step99693 (p2132 p2598 p2737 p2839 p3055 p3583 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73350 : p3055 ∨ p2598)
    (h43395 : (¬ p2132) ∨ (¬ p2737) ∨ (¬ p3055) ∨ (¬ p3583))
    : (¬ p2132) ∨ p2839 ∨ (¬ p2737) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43395 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99697 (p2132 p2138 p2946 p2956 p3136 p5048 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73334 : p2956 ∨ (¬ p2946))
    (h73892 : p5048 ∨ p3136)
    (h66861 : (¬ p5048) ∨ (¬ p2138) ∨ (¬ p2956))
    : p2132 ∨ (¬ p2946) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p2956 := (Or.elim h73334 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u5 : p5048 := (Or.elim h73892 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h66861 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u4)))))))

theorem step99699 (p2132 p2138 p2284 p2696 p2860 p3758 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73456 : p3758 ∨ p2860)
    (h63359 : (¬ p2138) ∨ (¬ p2284) ∨ (¬ p2696) ∨ (¬ p3758))
    : (¬ p2284) ∨ p2132 ∨ (¬ p2696) ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63359 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step99700 (p2132 p2138 p2274 p2696 p2860 p3097 p3758 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73456 : p3758 ∨ p2860)
    (h73352 : p3097 ∨ p2274)
    (h56360 : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p3097) ∨ (¬ p3758))
    : p2132 ∨ p2860 ∨ p2274 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56360 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step99701 (p2132 p2138 p2696 p2737 p2743 p2860 p3758 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73298 : p2743 ∨ p2737)
    (h73456 : p3758 ∨ p2860)
    (h43078 : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3758))
    : p2132 ∨ p2737 ∨ (¬ p2696) ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43078 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step99702 (p2132 p2138 p2630 p2651 p2810 p4117 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73316 : p2810 ∨ p2630)
    (h67276 : (¬ p2810) ∨ (¬ p2138) ∨ (¬ p2651) ∨ (¬ p4117))
    : (¬ p2651) ∨ p2132 ∨ p2630 ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67276 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step99704 (p2132 p2138 p2241 p2247 p2744 p2870 p2881 p3366 p3399 p3570 p3631 p4244 p4668 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73226 : p2247 ∨ p2241)
    (h73418 : p3570 ∨ p2881)
    (h73540 : p4244 ∨ p2870)
    (h61701 : (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3570) ∨ (¬ p3631) ∨ (¬ p4244) ∨ (¬ p4668))
    : (¬ p3631) ∨ p2132 ∨ p2241 ∨ p2881 ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p4668) ∨ p2870 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h61701 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step99706 (p2132 p2138 p2241 p2247 p2619 p2744 p3146 p3366 p3399 p3631 p3692 p3694 p3950 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73214 : p2138 ∨ p2132)
    (h73450 : p3694 ∨ p2619)
    (h73448 : p3692 ∨ p3146)
    (h56822 : (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950))
    : (¬ p3399) ∨ p2241 ∨ p2132 ∨ (¬ p3950) ∨ p2619 ∨ p3146 ∨ (¬ p2744) ∨ (¬ p3631) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56822 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step99708 (p2132 p2138 p2870 p2881 p3366 p3379 p3399 p3452 p3570 p3631 p4244 p4376 p4668 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73394 : p3452 ∨ p3379)
    (h73540 : p4244 ∨ p2870)
    (h73418 : p3570 ∨ p2881)
    (h51072 : (¬ p2138) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3570) ∨ (¬ p3631) ∨ (¬ p4244) ∨ (¬ p4376) ∨ (¬ p4668))
    : (¬ p3631) ∨ p2132 ∨ p3379 ∨ p2870 ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p4668) ∨ p2881 ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51072 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step99709 (p2132 p2138 p2427 p2598 p3055 p3367 p3425 p4235 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73536 : p4235 ∨ p2427)
    (h73350 : p3055 ∨ p2598)
    (h66773 : p3425 ∨ (¬ p2138) ∨ (¬ p4235) ∨ (¬ p3367) ∨ (¬ p3055))
    : p2132 ∨ (¬ p3367) ∨ p2427 ∨ p3425 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h66773 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step99710 (p2132 p2138 p2241 p2247 p2744 p2870 p2881 p3083 p3366 p3379 p3487 p3570 p4244 p4420 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73226 : p2247 ∨ p2241)
    (h73418 : p3570 ∨ p2881)
    (h73540 : p4244 ∨ p2870)
    (h52907 : (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4420))
    : p2132 ∨ (¬ p3487) ∨ (¬ p4420) ∨ (¬ p2744) ∨ (¬ p3366) ∨ p2241 ∨ p2881 ∨ (¬ p3379) ∨ p2870 ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h52907 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step99712 (p2132 p2138 p2187 p2246 p2437 p2651 p2744 p2860 p2911 p3366 p3758 p3989 p4503 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73502 : p3989 ∨ p2187)
    (h73456 : p3758 ∨ p2860)
    (h64008 : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2911) ∨ (¬ p3366) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4503))
    : p2132 ∨ (¬ p3366) ∨ (¬ p2437) ∨ (¬ p2744) ∨ p2187 ∨ (¬ p2246) ∨ p2860 ∨ (¬ p4503) ∨ (¬ p2911) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64008 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step99713 (p2132 p2138 p2246 p2331 p2668 p2744 p3105 p3366 p3979 p4322 p4385 p5119 : Prop)
    (h73576 : p4385 ∨ p3105)
    (h73214 : p2138 ∨ p2132)
    (h52896 : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3979) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p5119))
    : (¬ p4322) ∨ (¬ p3979) ∨ (¬ p2246) ∨ (¬ p2668) ∨ (¬ p5119) ∨ p3105 ∨ (¬ p2744) ∨ (¬ p3366) ∨ p2132 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4385 := (Or.elim h73576 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h52896 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step99715 (p2132 p2138 p2274 p2284 p2696 p3097 p3952 p4316 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73352 : p3097 ∨ p2274)
    (h73496 : p3952 ∨ p2284)
    (h45301 : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p4316))
    : p2132 ∨ p2274 ∨ p2284 ∨ (¬ p4316) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45301 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step99717 (p2132 p2138 p2761 p2860 p3125 p3266 p3366 p3516 p3519 p3744 p3758 p4376 p4444 p4604 p5201 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73456 : p3758 ∨ p2860)
    (h73214 : p2138 ∨ p2132)
    (h73454 : p3744 ∨ p3125)
    (h59536 : (¬ p2138) ∨ (¬ p2761) ∨ (¬ p3366) ∨ (¬ p3516) ∨ (¬ p3519) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p5201))
    : p3266 ∨ (¬ p2761) ∨ p2860 ∨ (¬ p5201) ∨ (¬ p3519) ∨ (¬ p3366) ∨ p2132 ∨ (¬ p4376) ∨ (¬ p4604) ∨ p3125 ∨ (¬ p3516) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u13 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u14 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h59536 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u14))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step99719 (p2132 p2138 p2241 p2247 p2449 p2619 p2744 p3037 p3146 p3366 p3399 p3692 p3694 p3950 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73450 : p3694 ∨ p2619)
    (h73448 : p3692 ∨ p3146)
    (h73226 : p2247 ∨ p2241)
    (h63901 : (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2449) ∨ (¬ p2744) ∨ (¬ p3037) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950))
    : (¬ p3399) ∨ p2132 ∨ (¬ p3950) ∨ p2619 ∨ p3146 ∨ (¬ p2744) ∨ (¬ p2449) ∨ (¬ p3366) ∨ p2241 ∨ (¬ p3037) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h63901 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step99720 (p2132 p2138 p2241 p2247 p2619 p2744 p3093 p3146 p3319 p3366 p3692 p3694 p4330 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73450 : p3694 ∨ p2619)
    (h73214 : p2138 ∨ p2132)
    (h73226 : p2247 ∨ p2241)
    (h55640 : (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3366) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4330))
    : (¬ p3319) ∨ p3146 ∨ (¬ p2744) ∨ (¬ p4330) ∨ p2619 ∨ (¬ p3366) ∨ (¬ p3093) ∨ p2132 ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h55640 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step99726 (p2132 p2138 p2573 p3362 p3364 p3422 p3584 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73426 : p3584 ∨ p3422)
    (h67305 : (¬ p3364) ∨ (¬ p2138) ∨ (¬ p3584) ∨ (¬ p2573) ∨ (¬ p3362))
    : p2132 ∨ p3422 ∨ (¬ p2573) ∨ (¬ p3364) ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67305 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step99728 (p2132 p2138 p2470 p3362 p3364 p3641 p3874 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73214 : p2138 ∨ p2132)
    (h67272 : (¬ p3364) ∨ (¬ p2138) ∨ (¬ p3362) ∨ (¬ p2470) ∨ (¬ p3874))
    : p3641 ∨ (¬ p2470) ∨ p2132 ∨ (¬ p3362) ∨ (¬ p3364) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67272 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99730 (p2132 p2138 p2187 p2274 p2819 p3097 p4193 p4358 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73214 : p2138 ∨ p2132)
    (h73564 : p4358 ∨ p2819)
    (h45100 : (¬ p2138) ∨ (¬ p2187) ∨ (¬ p3097) ∨ (¬ p4193) ∨ (¬ p4358))
    : p2274 ∨ (¬ p2187) ∨ p2132 ∨ (¬ p4193) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45100 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step99731 (p2132 p2138 p2774 p2780 p4193 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73307 : (¬ p2774) ∨ (¬ p2780))
    (h6853 : (¬ p2138) ∨ p2780 ∨ (¬ p4193))
    : p2132 ∨ (¬ p4193) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p2780) := (Or.elim h73307 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h6853 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step99733 (p2132 p2138 p2829 p3366 p3688 p4193 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73443 : (¬ p2829) ∨ (¬ p3688))
    (h38301 : (¬ p2138) ∨ (¬ p3366) ∨ p3688 ∨ (¬ p4193))
    : p2132 ∨ (¬ p2829) ∨ (¬ p3366) ∨ (¬ p4193) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : (¬ p3688) := (Or.elim h73443 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h38301 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step99742 (p2132 p2138 p2774 p2860 p3758 p3958 p4390 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73456 : p3758 ∨ p2860)
    (h52656 : (¬ p2138) ∨ (¬ p2774) ∨ (¬ p3758) ∨ (¬ p3958) ∨ (¬ p4390))
    : p2132 ∨ p2860 ∨ (¬ p4390) ∨ (¬ p2774) ∨ (¬ p3958) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52656 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99744 (p2132 p2138 p2246 p2264 p2341 p2449 p2744 p2860 p3125 p3366 p3553 p3744 p3758 p4104 p4625 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73456 : p3758 ∨ p2860)
    (h73410 : p3553 ∨ p2264)
    (h73454 : p3744 ∨ p3125)
    (h63639 : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2341) ∨ (¬ p2449) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3553) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4104) ∨ (¬ p4625))
    : (¬ p2341) ∨ p2132 ∨ (¬ p3366) ∨ p2860 ∨ (¬ p4625) ∨ (¬ p4104) ∨ (¬ p2744) ∨ (¬ p2246) ∨ p2264 ∨ p3125 ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u14 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h63639 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u14))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (False.elim (r9 u4)))))))))))))))))))))))

theorem step99747 (p2132 p2138 p2696 p2751 p2992 p4316 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h42560 : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p2992) ∨ (¬ p4316))
    : p2132 ∨ (¬ p2992) ∨ (¬ p2751) ∨ (¬ p2696) ∨ (¬ p4316) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42560 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step99750 (p3367 p4030 p6047 : Prop)
    (h74387 : (¬ p3367) ∨ (¬ p6047))
    (h13282 : p4030 ∨ p6047)
    : p4030 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4030) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6047) := (Or.elim h74387 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13282 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step99761 (p2417 p2696 p2753 p2761 p2829 p3363 p3365 p3389 p3540 p3914 p4278 p4381 p4752 p5250 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73402 : p3540 ∨ p3389)
    (h73390 : p3365 ∨ p2696)
    (h73546 : p4278 ∨ p2417)
    (h62127 : p2753 ∨ (¬ p2829) ∨ (¬ p3363) ∨ (¬ p3365) ∨ (¬ p3540) ∨ (¬ p3914) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4752) ∨ (¬ p5250))
    : (¬ p3914) ∨ p2753 ∨ (¬ p5250) ∨ (¬ p3363) ∨ p2761 ∨ (¬ p2829) ∨ p3389 ∨ p2696 ∨ (¬ p4752) ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2753) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h62127 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step99769 (p2470 p2476 p2528 p2534 p2696 p2753 p2829 p3266 p3363 p3365 p3914 p4444 p4752 p5250 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73268 : p2534 ∨ p2528)
    (h73390 : p3365 ∨ p2696)
    (h73250 : p2476 ∨ p2470)
    (h62154 : (¬ p2476) ∨ (¬ p2534) ∨ p2753 ∨ (¬ p2829) ∨ (¬ p3363) ∨ (¬ p3365) ∨ (¬ p3914) ∨ (¬ p4444) ∨ (¬ p4752) ∨ (¬ p5250))
    : (¬ p3914) ∨ p3266 ∨ p2528 ∨ p2696 ∨ (¬ p2829) ∨ p2470 ∨ p2753 ∨ (¬ p3363) ∨ (¬ p4752) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2753) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h62154 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step99781 (p2230 p2427 p2696 p2753 p3005 p3365 p3519 p3877 p4129 p4376 p5560 p5600 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73488 : p3877 ∨ p3005)
    (h53529 : (¬ p2230) ∨ (¬ p2427) ∨ p2753 ∨ (¬ p3365) ∨ (¬ p3519) ∨ (¬ p3877) ∨ (¬ p4129) ∨ (¬ p4376) ∨ (¬ p5560) ∨ (¬ p5600))
    : p2753 ∨ (¬ p5600) ∨ (¬ p3519) ∨ p2696 ∨ (¬ p5560) ∨ (¬ p2427) ∨ p3005 ∨ (¬ p2230) ∨ (¬ p4129) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2753) := (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5560 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h53529 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step99783 (p2132 p2135 p2137 : Prop)
    (h73212 : p2135 ∨ p2132)
    (h2407 : (¬ p2135) ∨ p2137)
    : p2132 ∨ p2137 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2137) := (fun h => hn (Or.inr h));
    let u2 : p2135 := (Or.elim h73212 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h2407 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99784 (p2132 p2135 p2139 : Prop)
    (h73212 : p2135 ∨ p2132)
    (h2409 : (¬ p2135) ∨ p2139)
    : p2132 ∨ p2139 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2139) := (fun h => hn (Or.inr h));
    let u2 : p2135 := (Or.elim h73212 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h2409 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99785 (p2132 p2135 p2140 : Prop)
    (h73212 : p2135 ∨ p2132)
    (h2410 : (¬ p2135) ∨ p2140)
    : p2132 ∨ p2140 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2140) := (fun h => hn (Or.inr h));
    let u2 : p2135 := (Or.elim h73212 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h2410 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99791 (p3367 p3541 p6047 : Prop)
    (h74387 : (¬ p3367) ∨ (¬ p6047))
    (h13281 : p3541 ∨ p6047)
    : p3541 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3541) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6047) := (Or.elim h74387 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13281 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step99792 (p2598 p3016 p3055 p3343 p3574 p5160 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73422 : p3574 ∨ p3016)
    (h56211 : (¬ p3055) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p5160))
    : (¬ p3343) ∨ (¬ p5160) ∨ p2598 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56211 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step99796 (p2132 p2138 p3355 p3362 p3364 p5160 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h67273 : (¬ p5160) ∨ (¬ p3364) ∨ (¬ p3362) ∨ (¬ p3355) ∨ (¬ p2138))
    : (¬ p5160) ∨ p2132 ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3364) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5160 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67273 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99797 (p3136 p3343 p3364 p4704 p5160 : Prop)
    (h73046 : p4704)
    (h51849 : (¬ p3136) ∨ (¬ p3343) ∨ (¬ p3364) ∨ (¬ p4704) ∨ (¬ p5160))
    : (¬ p3343) ∨ (¬ p5160) ∨ (¬ p3136) ∨ (¬ p3364) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4704 := h73046;
    (Or.elim h51849 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step99799 (p2246 p2264 p2459 p2573 p2579 p2744 p2807 p3366 p3422 p3905 p4022 p4604 p5160 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h57777 : (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3366) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4022) ∨ (¬ p4604) ∨ (¬ p5160))
    : (¬ p3905) ∨ (¬ p2246) ∨ p2573 ∨ (¬ p5160) ∨ (¬ p4604) ∨ (¬ p2744) ∨ (¬ p3422) ∨ (¬ p4022) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p2459) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3905 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57777 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u4))) (fun r10 => (False.elim (r10 u3)))))))))))))))))))))))))

theorem step99802 (p2139 p2598 p2881 p3051 p3055 p3276 p3941 p4425 p5119 p5160 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73350 : p3055 ∨ p2598)
    (h42415 : (¬ p2139) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p3941) ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p5160))
    : p3276 ∨ (¬ p5160) ∨ (¬ p2139) ∨ (¬ p3941) ∨ (¬ p5119) ∨ (¬ p3051) ∨ (¬ p2881) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42415 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step99803 (p2241 p2598 p3055 p3189 p3276 p3979 p4417 p4425 p4736 p5119 p5160 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73350 : p3055 ∨ p2598)
    (h62913 : (¬ p2241) ∨ (¬ p3055) ∨ (¬ p3189) ∨ (¬ p3979) ∨ (¬ p4417) ∨ (¬ p4425) ∨ (¬ p4736) ∨ (¬ p5119) ∨ (¬ p5160))
    : p3276 ∨ (¬ p5119) ∨ (¬ p2241) ∨ (¬ p4417) ∨ p2598 ∨ (¬ p3979) ∨ (¬ p4736) ∨ (¬ p3189) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62913 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step99804 (p2331 p2598 p2668 p3055 p3276 p3979 p4425 p4786 p5119 p5160 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73350 : p3055 ∨ p2598)
    (h48200 : (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3055) ∨ (¬ p3979) ∨ (¬ p4425) ∨ (¬ p4786) ∨ (¬ p5119) ∨ (¬ p5160))
    : p3276 ∨ (¬ p2668) ∨ (¬ p5160) ∨ (¬ p5119) ∨ (¬ p2331) ∨ p2598 ∨ (¬ p3979) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48200 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step99807 (p2246 p2598 p2744 p2946 p3055 p3156 p3276 p3366 p3969 p4425 p5119 p5160 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73350 : p3055 ∨ p2598)
    (h54039 : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p5160))
    : (¬ p3969) ∨ p3276 ∨ (¬ p2946) ∨ (¬ p5160) ∨ (¬ p3156) ∨ p2598 ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h54039 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step99812 (p3233 p3276 p3707 p4425 p5160 p5217 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h51546 : (¬ p3233) ∨ (¬ p3707) ∨ (¬ p4425) ∨ (¬ p5160) ∨ (¬ p5217))
    : p3276 ∨ (¬ p3707) ∨ (¬ p5160) ∨ (¬ p3233) ∨ (¬ p5217) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51546 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step99813 (p2707 p3367 p3585 p3658 p4637 p5160 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h59249 : (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p4637) ∨ (¬ p5160))
    : (¬ p4637) ∨ (¬ p5160) ∨ (¬ p2707) ∨ p3367 ∨ (¬ p3658) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4637 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59249 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step99814 (p2608 p3589 p5885 : Prop)
    (h74187 : (¬ p2608) ∨ (¬ p5885))
    (h12301 : p3589 ∨ p5885)
    : p3589 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3589) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5885) := (Or.elim h74187 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12301 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step99815 (p2992 p3662 p5053 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h47215 : (¬ p3662) ∨ p5053)
    : p2992 ∨ p5053 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5053) := (fun h => hn (Or.inr h));
    let u2 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47215 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99816 (p2992 p3662 p4917 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h47674 : (¬ p3662) ∨ p4917)
    : p2992 ∨ p4917 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4917) := (fun h => hn (Or.inr h));
    let u2 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47674 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99817 (p2727 p2992 p3016 p3662 p3879 p4717 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h41375 : (¬ p2727) ∨ (¬ p3016) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4717))
    : p2992 ∨ (¬ p3016) ∨ (¬ p2727) ∨ (¬ p3879) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41375 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step99818 (p2727 p2992 p3343 p3662 p3879 p4953 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h41636 : (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4953))
    : p2992 ∨ (¬ p3343) ∨ (¬ p3879) ∨ (¬ p4953) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41636 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step99819 (p2727 p2992 p3016 p3136 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h42863 : (¬ p2727) ∨ (¬ p3016) ∨ (¬ p3136) ∨ (¬ p3662))
    : p2992 ∨ (¬ p3016) ∨ (¬ p2727) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42863 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99825 (p2748 p2992 p3136 p3662 p4315 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73549 : (¬ p3136) ∨ (¬ p4315))
    (h38119 : (¬ p2748) ∨ (¬ p3662) ∨ p4315)
    : p2992 ∨ (¬ p2748) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p4315) := (Or.elim h73549 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h38119 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u4 r1)))))))

theorem step99829 (p2727 p2946 p2992 p3016 p3662 p4117 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h53552 : (¬ p2727) ∨ (¬ p2946) ∨ (¬ p3016) ∨ (¬ p3662) ∨ (¬ p4117))
    : p2992 ∨ (¬ p2946) ∨ (¬ p2727) ∨ (¬ p3016) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53552 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step99831 (p2459 p2741 p2911 p2992 p3136 p3389 p3519 p3662 p3755 p4035 p4376 p5113 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73506 : p4035 ∨ p3755)
    (h58555 : (¬ p2459) ∨ (¬ p2741) ∨ (¬ p2911) ∨ (¬ p3136) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3662) ∨ (¬ p4035) ∨ (¬ p4376) ∨ (¬ p5113))
    : (¬ p2911) ∨ (¬ p5113) ∨ p2992 ∨ (¬ p3136) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2741) ∨ (¬ p2459) ∨ p3755 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h58555 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step99833 (p2253 p2608 p2750 p2946 p2992 p3662 p3954 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73498 : p3954 ∨ p2608)
    (h49229 : (¬ p2253) ∨ (¬ p2750) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3954))
    : p2992 ∨ p2608 ∨ (¬ p2946) ∨ (¬ p2750) ∨ (¬ p2253) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49229 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step99834 (p2253 p2741 p2946 p2992 p3379 p3452 p3662 p4376 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73394 : p3452 ∨ p3379)
    (h42205 : (¬ p2253) ∨ (¬ p2741) ∨ (¬ p2946) ∨ (¬ p3452) ∨ (¬ p3662) ∨ (¬ p4376))
    : p2992 ∨ p3379 ∨ (¬ p2741) ∨ (¬ p4376) ∨ (¬ p2946) ∨ (¬ p2253) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42205 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step99836 (p2727 p2992 p3083 p3662 p3879 p4610 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h62216 : (¬ p2727) ∨ (¬ p3083) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4610))
    : p2992 ∨ (¬ p3083) ∨ (¬ p2727) ∨ (¬ p4610) ∨ (¬ p3879) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h62216 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step99838 (p2253 p2449 p2946 p2992 p2996 p3027 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73340 : p3027 ∨ p2996)
    (h42867 : (¬ p2253) ∨ (¬ p2449) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3662))
    : p2992 ∨ p2996 ∨ (¬ p2946) ∨ (¬ p2253) ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42867 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99839 (p2284 p2685 p2992 p2996 p3027 p3572 p3662 p3952 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73440 : p3662 ∨ p2992)
    (h73420 : p3572 ∨ p2685)
    (h73496 : p3952 ∨ p2284)
    (h62537 : (¬ p3027) ∨ (¬ p3572) ∨ (¬ p3662) ∨ (¬ p3952))
    : p2996 ∨ p2992 ∨ p2685 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62537 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u7)))))))))

theorem step99840 (p2295 p2331 p2946 p2963 p2992 p3568 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73338 : p2963 ∨ p2331)
    (h73416 : p3568 ∨ p2295)
    (h45416 : (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p3662))
    : p2992 ∨ p2331 ∨ (¬ p2946) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45416 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99842 (p2946 p2992 p3146 p3166 p3172 p3662 p3692 p4312 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73448 : p3692 ∨ p3146)
    (h73356 : p3172 ∨ p3166)
    (h48288 : (¬ p2946) ∨ (¬ p3172) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p4312))
    : p2992 ∨ p3146 ∨ (¬ p4312) ∨ (¬ p2946) ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48288 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99843 (p2177 p2274 p2284 p2299 p2992 p3097 p3662 p3952 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73496 : p3952 ∨ p2284)
    (h73234 : p2299 ∨ p2177)
    (h73352 : p3097 ∨ p2274)
    (h60865 : (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3662) ∨ (¬ p3952))
    : p2992 ∨ p2284 ∨ p2177 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60865 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step99856 (p2761 p3434 p3461 p4025 p4191 p4477 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h41192 : (¬ p2761) ∨ (¬ p3434) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4477))
    : p3461 ∨ (¬ p2761) ∨ (¬ p4477) ∨ (¬ p4025) ∨ (¬ p3434) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41192 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99857 (p2417 p2761 p3461 p4025 p4191 p4712 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h49248 : (¬ p2417) ∨ (¬ p2761) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4712))
    : p3461 ∨ (¬ p2761) ∨ (¬ p4712) ∨ (¬ p4025) ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49248 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99858 (p2761 p2901 p3051 p3212 p3556 p4135 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h55162 : (¬ p2761) ∨ (¬ p2901) ∨ (¬ p3212) ∨ (¬ p3556) ∨ (¬ p4135))
    : (¬ p2761) ∨ (¬ p4135) ∨ p3051 ∨ (¬ p2901) ∨ (¬ p3212) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55162 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step99861 (p2230 p2563 p2761 p3125 p3286 p3292 p4236 p4419 p4621 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h51142 : (¬ p2230) ∨ (¬ p2563) ∨ (¬ p2761) ∨ (¬ p3125) ∨ (¬ p3292) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p4621) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p2761) ∨ (¬ p4236) ∨ (¬ p2563) ∨ (¬ p2230) ∨ p3286 ∨ (¬ p3125) ∨ (¬ p4419) ∨ (¬ p4621) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51142 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step99864 (p2449 p2707 p2737 p2743 p2761 p4325 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h45502 : (¬ p2449) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2761) ∨ (¬ p4325))
    : (¬ p2707) ∨ p2737 ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p4325) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45502 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step99867 (p2707 p2737 p2743 p2761 p3434 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h58754 : (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2761) ∨ (¬ p3434))
    : (¬ p2707) ∨ p2737 ∨ (¬ p3434) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h58754 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step99870 (p2707 p2761 p3367 p3516 p3577 p3585 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h46352 : (¬ p2707) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p3577) ∨ (¬ p3585))
    : (¬ p3577) ∨ (¬ p2761) ∨ (¬ p2707) ∨ p3367 ∨ (¬ p3516) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46352 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99871 (p2598 p2608 p2753 p2761 p3461 p3654 p3946 p4166 p4191 p4638 p5021 p5126 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73492 : p3946 ∨ p3654)
    (h53286 : (¬ p2598) ∨ (¬ p2608) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3946) ∨ (¬ p4166) ∨ (¬ p4191) ∨ (¬ p4638) ∨ (¬ p5021) ∨ (¬ p5126))
    : (¬ p4166) ∨ p3461 ∨ (¬ p2608) ∨ (¬ p5021) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p5126) ∨ (¬ p2598) ∨ p3654 ∨ (¬ p4638) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5126 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h53286 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step99872 (p2761 p3193 p3222 p3807 p4638 p5127 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h49346 : (¬ p2761) ∨ (¬ p3222) ∨ (¬ p3807) ∨ (¬ p4638) ∨ (¬ p5127))
    : (¬ p3807) ∨ (¬ p5127) ∨ (¬ p4638) ∨ p3193 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5127 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49346 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step99873 (p2241 p2247 p2761 p2996 p4429 p5284 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h46226 : (¬ p2247) ∨ (¬ p2761) ∨ (¬ p2996) ∨ (¬ p4429) ∨ (¬ p5284))
    : (¬ p5284) ∨ p2241 ∨ (¬ p2761) ∨ (¬ p2996) ∨ (¬ p4429) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4429 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46226 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step99874 (p2145 p2156 p2352 p2761 p3425 p3434 p3471 p3646 p3956 p4203 p5123 p5580 : Prop)
    (h73396 : p3471 ∨ p3425)
    (h73436 : p3646 ∨ p2156)
    (h73500 : p3956 ∨ p2352)
    (h56997 : (¬ p2145) ∨ (¬ p2761) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3646) ∨ (¬ p3956) ∨ (¬ p4203) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p2761) ∨ (¬ p3434) ∨ (¬ p5123) ∨ p3425 ∨ p2156 ∨ (¬ p2145) ∨ (¬ p4203) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h56997 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step99876 (p2284 p2761 p2946 p2952 p3125 p3266 p3516 p3744 p3819 p3952 p4444 p4604 p4789 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73454 : p3744 ∨ p3125)
    (h73496 : p3952 ∨ p2284)
    (h73330 : p2952 ∨ p2946)
    (h65144 : (¬ p2761) ∨ (¬ p2952) ∨ (¬ p3516) ∨ (¬ p3744) ∨ (¬ p3819) ∨ (¬ p3952) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p4789))
    : p3266 ∨ (¬ p2761) ∨ p3125 ∨ (¬ p4604) ∨ (¬ p4789) ∨ (¬ p3516) ∨ (¬ p3819) ∨ p2284 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h65144 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step99878 (p2761 p2785 p2829 p3461 p3654 p3688 p3946 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73492 : p3946 ∨ p3654)
    (h73444 : p3688 ∨ p2829)
    (h53923 : (¬ p2761) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p3946) ∨ (¬ p4191))
    : p3461 ∨ p3654 ∨ (¬ p2785) ∨ (¬ p2761) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53923 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99881 (p2641 p2667 p2761 p3461 p3654 p3946 p4154 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73492 : p3946 ∨ p3654)
    (h73526 : p4154 ∨ p2641)
    (h43647 : (¬ p2667) ∨ (¬ p2761) ∨ (¬ p3946) ∨ (¬ p4154) ∨ (¬ p4191))
    : p3461 ∨ p3654 ∨ p2641 ∨ (¬ p2667) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43647 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99884 (p2331 p2761 p2963 p3323 p3461 p4037 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73508 : p4037 ∨ p3323)
    (h73338 : p2963 ∨ p2331)
    (h45319 : (¬ p2761) ∨ (¬ p2963) ∨ (¬ p4037) ∨ (¬ p4191))
    : p3461 ∨ (¬ p2761) ∨ p3323 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45319 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99887 (p2761 p2797 p3051 p3136 p3246 p3370 p3953 p4228 p4315 p4377 p4435 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h64565 : (¬ p2761) ∨ (¬ p2797) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3370) ∨ (¬ p3953) ∨ (¬ p4228) ∨ (¬ p4315) ∨ (¬ p4377) ∨ (¬ p4435))
    : (¬ p4228) ∨ (¬ p4435) ∨ (¬ p3953) ∨ (¬ p2761) ∨ (¬ p3370) ∨ (¬ p3051) ∨ (¬ p2797) ∨ p3136 ∨ (¬ p3246) ∨ (¬ p4377) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64565 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step99888 (p2761 p3093 p3125 p3425 p3471 p3516 p3591 p3737 p3744 p4066 p4325 p4435 p4733 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73396 : p3471 ∨ p3425)
    (h73432 : p3591 ∨ p3093)
    (h51572 : (¬ p2761) ∨ (¬ p3471) ∨ (¬ p3516) ∨ (¬ p3591) ∨ (¬ p3737) ∨ (¬ p3744) ∨ (¬ p4066) ∨ (¬ p4325) ∨ (¬ p4435) ∨ (¬ p4733))
    : (¬ p3737) ∨ (¬ p4435) ∨ (¬ p4325) ∨ p3125 ∨ (¬ p3516) ∨ p3425 ∨ (¬ p4066) ∨ (¬ p2761) ∨ p3093 ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h51572 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step99895 (p2254 p2651 p2657 p2761 p3016 p3399 p3574 p3631 p5254 p5514 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73288 : p2657 ∨ p2651)
    (h49091 : (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3574) ∨ (¬ p3631) ∨ (¬ p5254) ∨ (¬ p5514))
    : (¬ p3631) ∨ (¬ p5514) ∨ (¬ p5254) ∨ (¬ p2254) ∨ (¬ p3399) ∨ p3016 ∨ (¬ p2761) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49091 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step99897 (p2352 p2363 p2573 p2761 p3286 p3292 p4236 p4419 p4669 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h52106 : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2761) ∨ (¬ p3292) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p4669) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p2352) ∨ p3286 ∨ (¬ p2573) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p2761) ∨ (¬ p4669) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52106 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step99898 (p2449 p2598 p2761 p2807 p3055 p3422 p3584 p4786 p5254 p5514 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73350 : p3055 ∨ p2598)
    (h63964 : (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p4786) ∨ (¬ p5254) ∨ (¬ p5514))
    : (¬ p5514) ∨ p3422 ∨ (¬ p4786) ∨ (¬ p2807) ∨ (¬ p2449) ∨ (¬ p5254) ∨ (¬ p2761) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5514 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63964 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step99899 (p2598 p2761 p3055 p3399 p3422 p3584 p3631 p4736 p5254 p5514 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73350 : p3055 ∨ p2598)
    (h63870 : (¬ p2761) ∨ (¬ p3055) ∨ (¬ p3399) ∨ (¬ p3584) ∨ (¬ p3631) ∨ (¬ p4736) ∨ (¬ p5254) ∨ (¬ p5514))
    : (¬ p5514) ∨ p3422 ∨ (¬ p4736) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p2761) ∨ (¬ p5254) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5514 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63870 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step99907 (p2427 p2761 p2982 p3051 p4135 p4235 p4399 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h50932 : (¬ p2761) ∨ (¬ p2982) ∨ (¬ p3051) ∨ (¬ p4135) ∨ (¬ p4235) ∨ (¬ p4399))
    : (¬ p3051) ∨ (¬ p4135) ∨ (¬ p4399) ∨ (¬ p2761) ∨ (¬ p2982) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50932 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step99910 (p2761 p4827 p4831 : Prop)
    (h73780 : p4827 ∨ (¬ p2761))
    (h7910 : (¬ p4827) ∨ p4831)
    : (¬ p2761) ∨ p4831 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4831) := (fun h => hn (Or.inr h));
    let u2 : p4827 := (Or.elim h73780 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7910 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99911 (p2727 p2807 p2946 p2952 p2996 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h69696 : (¬ p2996) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p2727))
    : p2946 ∨ (¬ p2996) ∨ (¬ p2807) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h69696 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step99913 (p2396 p2449 p2992 p2996 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h61578 : (¬ p2396) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3947))
    : p2449 ∨ (¬ p2992) ∨ (¬ p2396) ∨ (¬ p2996) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h61578 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99914 (p2177 p2341 p2992 p2996 p3551 p4155 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h55006 : (¬ p2177) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155))
    : p2341 ∨ (¬ p2992) ∨ (¬ p4155) ∨ (¬ p2996) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55006 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99915 (p2264 p2946 p2952 p2992 p2996 p3553 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73410 : p3553 ∨ p2264)
    (h44972 : (¬ p2952) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3553))
    : (¬ p2992) ∨ p2946 ∨ (¬ p2996) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44972 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step99917 (p2651 p2946 p2952 p2992 p2996 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h52432 : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p2996))
    : p2946 ∨ (¬ p2996) ∨ (¬ p2992) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h52432 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step99926 (p2341 p2727 p2911 p2996 p3551 p4155 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h62931 : (¬ p2727) ∨ (¬ p2911) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155))
    : p2341 ∨ (¬ p2996) ∨ (¬ p2727) ∨ (¬ p4155) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h62931 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step99929 (p2341 p2459 p2992 p2996 p3551 p4155 p4348 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73562 : p4348 ∨ p2459)
    (h43770 : (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4348))
    : p2341 ∨ (¬ p2996) ∨ (¬ p2992) ∨ (¬ p4155) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43770 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step99930 (p2137 p2220 p2449 p2696 p2748 p2839 p2996 p3146 p3365 p3947 p4669 p4734 : Prop)
    (h72735 : p4734)
    (h73390 : p3365 ∨ p2696)
    (h73494 : p3947 ∨ p2449)
    (h52002 : (¬ p2137) ∨ (¬ p2220) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p2996) ∨ (¬ p3146) ∨ (¬ p3365) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4734))
    : (¬ p2839) ∨ (¬ p3146) ∨ (¬ p2220) ∨ (¬ p2996) ∨ (¬ p2137) ∨ p2696 ∨ p2449 ∨ (¬ p2748) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4734 := h72735;
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52002 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step99932 (p2685 p2748 p2996 p3572 : Prop)
    (h73419 : (¬ p2685) ∨ (¬ p3572))
    (h6636 : (¬ p2748) ∨ (¬ p2996) ∨ p3572)
    : (¬ p2748) ∨ (¬ p2996) ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2748 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3572) := (Or.elim h73419 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h6636 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step99935 (p2241 p2247 p2685 p2797 p2996 p4195 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73532 : p4195 ∨ p2797)
    (h47368 : (¬ p2247) ∨ (¬ p2685) ∨ (¬ p2996) ∨ (¬ p4195))
    : p2241 ∨ (¬ p2996) ∨ (¬ p2685) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47368 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step99936 (p2230 p2373 p2685 p2741 p2996 p3146 p3519 p3755 p4035 p4376 p5113 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h42381 : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2685) ∨ (¬ p2741) ∨ (¬ p2996) ∨ (¬ p3146) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4376) ∨ (¬ p5113))
    : (¬ p3519) ∨ p3755 ∨ (¬ p2373) ∨ (¬ p5113) ∨ (¬ p2741) ∨ (¬ p2685) ∨ (¬ p2996) ∨ (¬ p2230) ∨ (¬ p4376) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3519 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42381 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step99937 (p2696 p2745 p2996 p3365 p3425 p3471 p4325 : Prop)
    (h73396 : p3471 ∨ p3425)
    (h73390 : p3365 ∨ p2696)
    (h48341 : (¬ p2745) ∨ (¬ p2996) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p4325))
    : p3425 ∨ (¬ p2996) ∨ (¬ p4325) ∨ (¬ p2745) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48341 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99938 (p2245 p2449 p2651 p2657 p2727 p2996 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73288 : p2657 ∨ p2651)
    (h44680 : (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3947))
    : (¬ p2996) ∨ (¬ p2727) ∨ p2449 ∨ p2651 ∨ (¬ p2245) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44680 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99939 (p2253 p2741 p2807 p2996 p3379 p3452 p4376 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h42387 : (¬ p2253) ∨ (¬ p2741) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p3452) ∨ (¬ p4376))
    : (¬ p2996) ∨ (¬ p2253) ∨ (¬ p2741) ∨ (¬ p4376) ∨ (¬ p2807) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42387 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step99940 (p2255 p2449 p2958 p2996 p3516 p3947 p4988 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h49154 : (¬ p2255) ∨ (¬ p2958) ∨ (¬ p2996) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4988))
    : (¬ p3516) ∨ (¬ p2996) ∨ (¬ p2958) ∨ p2449 ∨ (¬ p4988) ∨ (¬ p2255) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49154 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step99941 (p2255 p2449 p2996 p3516 p3947 p4104 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h59081 : (¬ p2255) ∨ (¬ p2996) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4104))
    : (¬ p3516) ∨ (¬ p2996) ∨ (¬ p2255) ∨ (¬ p4104) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59081 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step99943 (p2177 p2449 p2641 p2996 p3945 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h47511 : (¬ p2177) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3945) ∨ (¬ p3947))
    : (¬ p2641) ∨ p2449 ∨ (¬ p2996) ∨ (¬ p2177) ∨ (¬ p3945) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47511 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99944 (p2417 p2449 p2727 p2996 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h47527 : (¬ p2417) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3947))
    : (¬ p2996) ∨ (¬ p2417) ∨ p2449 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47527 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99945 (p2449 p2745 p2996 p3434 p3947 p4781 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h56256 : (¬ p2745) ∨ (¬ p2996) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4781))
    : (¬ p3434) ∨ (¬ p2996) ∨ (¬ p2745) ∨ (¬ p4781) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56256 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step99947 (p2253 p2608 p2750 p2807 p2996 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h42611 : (¬ p2253) ∨ (¬ p2750) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p3954))
    : p2608 ∨ (¬ p2253) ∨ (¬ p2807) ∨ (¬ p2750) ∨ (¬ p2996) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42611 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99952 (p2122 p2177 p2241 p2247 p2449 p2774 p2996 p3947 p4666 p4733 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73494 : p3947 ∨ p2449)
    (h62556 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2774) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4666) ∨ (¬ p4733))
    : (¬ p2996) ∨ p2241 ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p4666) ∨ (¬ p4733) ∨ p2449 ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62556 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step99953 (p2132 p2241 p2247 p2449 p2870 p2881 p2996 p3947 p4666 p4733 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73494 : p3947 ∨ p2449)
    (h50635 : (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4666) ∨ (¬ p4733))
    : (¬ p2996) ∨ p2241 ∨ (¬ p2132) ∨ (¬ p4733) ∨ (¬ p4666) ∨ (¬ p2870) ∨ p2449 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50635 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step99954 (p2241 p2247 p2449 p2761 p2996 p3947 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73226 : p2247 ∨ p2241)
    (h73494 : p3947 ∨ p2449)
    (h47938 : (¬ p2247) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4381))
    : p2761 ∨ p2241 ∨ p2449 ∨ (¬ p2996) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47938 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99964 (p2449 p2641 p2761 p2996 p3947 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73494 : p3947 ∨ p2449)
    (h47512 : (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4381))
    : p2761 ∨ (¬ p2641) ∨ (¬ p2996) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47512 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99967 (p2177 p2341 p2641 p2996 p3551 p4155 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h43823 : (¬ p2177) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155))
    : (¬ p2641) ∨ p2341 ∨ (¬ p4155) ∨ (¬ p2996) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43823 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step99968 (p2331 p2797 p2807 p2963 p2996 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h45622 : (¬ p2797) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p2996))
    : (¬ p2996) ∨ (¬ p2797) ∨ p2331 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45622 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step99969 (p2331 p2641 p2946 p2963 p2996 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h44039 : (¬ p2641) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p2996))
    : (¬ p2641) ∨ p2331 ∨ (¬ p2946) ∨ (¬ p2996) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44039 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step99970 (p2341 p2459 p2641 p2996 p3551 p4155 p4348 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73562 : p4348 ∨ p2459)
    (h43875 : (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4348))
    : (¬ p2641) ∨ p2341 ∨ (¬ p4155) ∨ (¬ p2996) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43875 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step99971 (p2341 p2459 p2727 p2996 p3551 p4155 p4348 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73562 : p4348 ∨ p2459)
    (h59881 : (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4348))
    : p2341 ∨ (¬ p2996) ∨ (¬ p2727) ∨ (¬ p4155) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59881 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step99973 (p2449 p2881 p2996 p3246 p3570 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73418 : p3570 ∨ p2881)
    (h56816 : (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3947))
    : (¬ p3246) ∨ (¬ p2996) ∨ p2449 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56816 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99974 (p2449 p2727 p2996 p3246 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h43098 : (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3947))
    : (¬ p2996) ∨ p2449 ∨ (¬ p3246) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43098 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99976 (p2807 p2996 p3286 p3292 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h46933 : (¬ p2807) ∨ (¬ p2996) ∨ (¬ p3292) ∨ (¬ p5284))
    : p3286 ∨ (¬ p5284) ∨ (¬ p2996) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46933 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step99984 (p3389 p3540 p4653 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h46046 : (¬ p3540) ∨ p4653)
    : p3389 ∨ p4653 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4653) := (fun h => hn (Or.inr h));
    let u2 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46046 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99985 (p3389 p3540 p5203 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h48722 : (¬ p3540) ∨ p5203)
    : p3389 ∨ p5203 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5203) := (fun h => hn (Or.inr h));
    let u2 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48722 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step99986 (p2177 p2630 p2662 p2810 p2911 p3389 p3540 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73402 : p3540 ∨ p3389)
    (h73316 : p2810 ∨ p2630)
    (h46000 : (¬ p2177) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3540) ∨ (¬ p3644))
    : p2911 ∨ (¬ p2177) ∨ (¬ p2662) ∨ p3389 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46000 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99987 (p2630 p2662 p2810 p2881 p2911 p3389 p3540 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73316 : p2810 ∨ p2630)
    (h73402 : p3540 ∨ p3389)
    (h53488 : (¬ p2662) ∨ (¬ p2810) ∨ (¬ p2881) ∨ (¬ p3540) ∨ (¬ p3644))
    : p2911 ∨ (¬ p2881) ∨ (¬ p2662) ∨ p2630 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53488 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99988 (p2156 p2246 p2284 p2744 p2958 p3156 p3201 p3366 p3389 p3540 p3641 p3874 p3905 p3952 p4434 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73402 : p3540 ∨ p3389)
    (h73484 : p3874 ∨ p3641)
    (h52836 : (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3156) ∨ (¬ p3201) ∨ (¬ p3366) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p3952) ∨ (¬ p4434))
    : (¬ p3156) ∨ p2284 ∨ (¬ p2156) ∨ p3389 ∨ (¬ p2246) ∨ (¬ p2958) ∨ (¬ p4434) ∨ (¬ p2744) ∨ (¬ p3201) ∨ p3641 ∨ (¬ p3905) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u14 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h52836 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u14))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u12))) (fun r10 => (False.elim (r10 u6)))))))))))))))))))))))))

theorem step99989 (p2255 p2363 p2662 p2727 p2911 p3166 p3256 p3389 p3540 p3644 p4111 p4133 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73434 : p3644 ∨ p2911)
    (h73402 : p3540 ∨ p3389)
    (h73518 : p4111 ∨ p2727)
    (h60303 : (¬ p2255) ∨ (¬ p2662) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4111) ∨ (¬ p4133) ∨ (¬ p4347))
    : (¬ p3256) ∨ p2363 ∨ p2911 ∨ (¬ p3166) ∨ p3389 ∨ (¬ p4133) ∨ (¬ p2255) ∨ p2727 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h60303 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step99990 (p2187 p2192 p2255 p2662 p2727 p2911 p2946 p3389 p3412 p3540 p3644 p4111 p4133 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73518 : p4111 ∨ p2727)
    (h73402 : p3540 ∨ p3389)
    (h48518 : (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2255) ∨ (¬ p2662) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4111) ∨ (¬ p4133))
    : p2911 ∨ p2727 ∨ (¬ p2187) ∨ (¬ p3412) ∨ (¬ p2255) ∨ (¬ p2192) ∨ (¬ p4133) ∨ (¬ p2946) ∨ (¬ p2662) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h48518 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step99991 (p2177 p2573 p2911 p3389 p3540 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73402 : p3540 ∨ p3389)
    (h48536 : (¬ p2177) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3644))
    : p2911 ∨ (¬ p2177) ∨ (¬ p2573) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48536 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step99992 (p2459 p2696 p2753 p2797 p2911 p3323 p3347 p3389 p3540 p3644 p4330 p4348 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73562 : p4348 ∨ p2459)
    (h73402 : p3540 ∨ p3389)
    (h72216 : (¬ p3644) ∨ (¬ p4348) ∨ (¬ p3540) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3347) ∨ (¬ p4330) ∨ (¬ p2753))
    : p2911 ∨ (¬ p2753) ∨ (¬ p3347) ∨ p2459 ∨ (¬ p2696) ∨ (¬ p3323) ∨ (¬ p2797) ∨ (¬ p4330) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h72216 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step99994 (p2459 p2662 p2727 p2911 p3389 p3540 p3644 p4111 p4348 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73562 : p4348 ∨ p2459)
    (h73402 : p3540 ∨ p3389)
    (h73518 : p4111 ∨ p2727)
    (h43585 : (¬ p2662) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4111) ∨ (¬ p4348))
    : p2911 ∨ p2459 ∨ p3389 ∨ p2727 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43585 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step99995 (p2230 p2881 p2933 p3389 p3527 p3540 p3548 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73402 : p3540 ∨ p3389)
    (h56626 : (¬ p2230) ∨ (¬ p2881) ∨ (¬ p2933) ∨ (¬ p3540) ∨ (¬ p3548))
    : (¬ p2933) ∨ p3527 ∨ (¬ p2230) ∨ (¬ p2881) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2933 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56626 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step99997 (p2241 p2396 p2417 p2901 p2992 p3389 p3540 p4278 p4556 p5193 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73402 : p3540 ∨ p3389)
    (h50153 : (¬ p2241) ∨ (¬ p2396) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4556) ∨ (¬ p5193))
    : (¬ p2901) ∨ (¬ p2992) ∨ p2417 ∨ (¬ p5193) ∨ (¬ p2396) ∨ p3389 ∨ (¬ p2241) ∨ (¬ p4556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50153 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step99999 (p2177 p2299 p2493 p2499 p2573 p3389 p3540 p3921 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73260 : p2499 ∨ p2493)
    (h73234 : p2299 ∨ p2177)
    (h50875 : (¬ p2299) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921))
    : p3389 ∨ (¬ p3921) ∨ p2493 ∨ (¬ p2573) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50875 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step100004 (p2253 p2651 p3379 p3452 p4116 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h6144 : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p3452) ∨ (¬ p4116))
    : (¬ p2253) ∨ (¬ p4116) ∨ p3379 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6144 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step100005 (p2210 p2253 p2741 p3166 p3189 p3555 p4360 p4377 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73412 : p3555 ∨ p2210)
    (h63529 : (¬ p2253) ∨ (¬ p2741) ∨ (¬ p3166) ∨ (¬ p3555) ∨ (¬ p4360) ∨ (¬ p4377))
    : (¬ p2253) ∨ (¬ p3166) ∨ p3189 ∨ p2210 ∨ (¬ p4377) ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63529 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step100006 (p2210 p2253 p2651 p2727 p2741 p3555 p4111 p4377 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73412 : p3555 ∨ p2210)
    (h49576 : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (¬ p3555) ∨ (¬ p4111) ∨ (¬ p4377))
    : p2727 ∨ p2210 ∨ (¬ p4377) ∨ (¬ p2741) ∨ (¬ p2253) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49576 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step100008 (p2253 p2741 p3166 p3189 p3379 p3452 p4360 p4376 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73394 : p3452 ∨ p3379)
    (h42230 : (¬ p2253) ∨ (¬ p2741) ∨ (¬ p3166) ∨ (¬ p3452) ∨ (¬ p4360) ∨ (¬ p4376))
    : p3189 ∨ (¬ p3166) ∨ (¬ p2253) ∨ p3379 ∨ (¬ p4376) ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42230 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step100010 (p2253 p2608 p2750 p3166 p3189 p3954 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73498 : p3954 ∨ p2608)
    (h54343 : (¬ p2253) ∨ (¬ p2750) ∨ (¬ p3166) ∨ (¬ p3954) ∨ (¬ p4360))
    : p3189 ∨ p2608 ∨ (¬ p2750) ∨ (¬ p2253) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54343 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100012 (p2253 p2608 p2651 p2727 p2750 p3954 p4111 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73518 : p4111 ∨ p2727)
    (h51595 : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p4111))
    : p2608 ∨ (¬ p2253) ∨ p2727 ∨ (¬ p2651) ∨ (¬ p2750) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51595 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step100014 (p2253 p2331 p2608 p2641 p2750 p3954 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73498 : p3954 ∨ p2608)
    (h41422 : (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p4154))
    : p2641 ∨ p2608 ∨ (¬ p2253) ∨ (¬ p2750) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41422 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100021 (p2253 p2331 p3093 p3591 p4319 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h20279 : (¬ p2253) ∨ (¬ p2331) ∨ (¬ p3591) ∨ (¬ p4319))
    : (¬ p4319) ∨ p3093 ∨ (¬ p2253) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20279 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step100024 (p2253 p3166 p3449 p3860 p5074 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h40317 : (¬ p2253) ∨ (¬ p3166) ∨ (¬ p3860) ∨ (¬ p5074))
    : p3449 ∨ (¬ p5074) ∨ (¬ p2253) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p5074 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h40317 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step100034 (p2417 p4278 p4640 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h47100 : (¬ p4278) ∨ p4640)
    : p2417 ∨ p4640 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4640) := (fun h => hn (Or.inr h));
    let u2 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47100 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100035 (p2177 p2299 p2396 p2417 p2922 p2928 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73234 : p2299 ∨ p2177)
    (h73320 : p2928 ∨ p2922)
    (h43512 : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2928) ∨ (¬ p4278))
    : (¬ p2396) ∨ p2417 ∨ p2177 ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43512 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100041 (p2331 p2363 p2417 p2598 p2668 p3055 p3201 p3876 p4278 p4669 p4786 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h52114 : (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4786))
    : p2417 ∨ (¬ p2668) ∨ (¬ p2331) ∨ p3201 ∨ (¬ p4669) ∨ (¬ p4786) ∨ p2598 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52114 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step100042 (p2417 p2696 p2742 p3189 p3256 p3363 p3367 p3389 p3540 p3585 p4278 p4669 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73428 : p3585 ∨ p3367)
    (h73402 : p3540 ∨ p3389)
    (h72218 : (¬ p4278) ∨ (¬ p3585) ∨ (¬ p2742) ∨ (¬ p3256) ∨ (¬ p4669) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p2696) ∨ (¬ p3189))
    : (¬ p3256) ∨ (¬ p3189) ∨ (¬ p2696) ∨ p2417 ∨ (¬ p4669) ∨ (¬ p3363) ∨ p3367 ∨ (¬ p2742) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h72218 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step100043 (p2177 p2299 p2396 p2417 p2881 p4277 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73234 : p2299 ∨ p2177)
    (h50110 : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2881) ∨ (¬ p4277) ∨ (¬ p4278))
    : p2417 ∨ (¬ p2396) ∨ p2177 ∨ (¬ p4277) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50110 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100046 (p2417 p2437 p3016 p3422 p3584 p3742 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73452 : p3742 ∨ p2437)
    (h73426 : p3584 ∨ p3422)
    (h44339 : (¬ p3016) ∨ (¬ p3584) ∨ (¬ p3742) ∨ (¬ p4278))
    : p2417 ∨ p2437 ∨ (¬ p3016) ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44339 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100047 (p2230 p2406 p2417 p2437 p2656 p3238 p3742 p4278 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73452 : p3742 ∨ p2437)
    (h73546 : p4278 ∨ p2417)
    (h59510 : (¬ p2230) ∨ (¬ p2656) ∨ (¬ p3238) ∨ (¬ p3742) ∨ (¬ p4278))
    : (¬ p2230) ∨ (¬ p2656) ∨ p2406 ∨ p2437 ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59510 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step100050 (p2132 p2417 p2860 p2922 p2928 p3125 p3379 p3452 p4278 p4621 p4733 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73546 : p4278 ∨ p2417)
    (h73394 : p3452 ∨ p3379)
    (h49259 : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p2928) ∨ (¬ p3125) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4733))
    : p2922 ∨ p2417 ∨ (¬ p2132) ∨ (¬ p4621) ∨ (¬ p3125) ∨ p3379 ∨ (¬ p2860) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49259 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step100051 (p2241 p2417 p2437 p3379 p3452 p3742 p4116 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73394 : p3452 ∨ p3379)
    (h73452 : p3742 ∨ p2437)
    (h44798 : (¬ p2241) ∨ (¬ p3452) ∨ (¬ p3742) ∨ (¬ p4116) ∨ (¬ p4278))
    : (¬ p2241) ∨ p2417 ∨ p3379 ∨ p2437 ∨ (¬ p4116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44798 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100058 (p2417 p2437 p2573 p2579 p3016 p3742 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73452 : p3742 ∨ p2437)
    (h73274 : p2579 ∨ p2573)
    (h44289 : (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p4278))
    : p2417 ∨ p2437 ∨ p2573 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44289 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100061 (p2177 p2299 p2396 p2417 p2441 p2563 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73234 : p2299 ∨ p2177)
    (h61277 : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2441) ∨ (¬ p2563) ∨ (¬ p4278))
    : (¬ p2396) ∨ p2417 ∨ p2177 ∨ (¬ p2563) ∨ (¬ p2441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61277 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100062 (p2210 p2417 p2651 p2657 p3146 p3201 p3366 p3449 p3555 p3683 p3876 p4236 p4278 p4377 p4446 p4669 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73412 : p3555 ∨ p2210)
    (h73486 : p3876 ∨ p3201)
    (h73546 : p4278 ∨ p2417)
    (h52132 : (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p3683) ∨ (¬ p3876) ∨ (¬ p4236) ∨ (¬ p4278) ∨ (¬ p4377) ∨ (¬ p4446) ∨ (¬ p4669))
    : (¬ p4236) ∨ (¬ p3449) ∨ (¬ p4446) ∨ p2651 ∨ p2210 ∨ (¬ p3146) ∨ (¬ p3683) ∨ p3201 ∨ p2417 ∨ (¬ p4377) ∨ (¬ p4669) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4446 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u14 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u15 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h52132 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u14))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u15))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u2))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step100067 (p2252 p2417 p2437 p2651 p2657 p2750 p3212 p3370 p3371 p3461 p3680 p3742 p4191 p4278 p4621 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73452 : p3742 ∨ p2437)
    (h73546 : p4278 ∨ p2417)
    (h73288 : p2657 ∨ p2651)
    (h55334 : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3212) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3680) ∨ (¬ p3742) ∨ (¬ p4191) ∨ (¬ p4278) ∨ (¬ p4621))
    : (¬ p3370) ∨ p3461 ∨ (¬ p2750) ∨ p2437 ∨ (¬ p2252) ∨ (¬ p3371) ∨ (¬ p3212) ∨ p2417 ∨ p2651 ∨ (¬ p3680) ∨ (¬ p4621) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u14 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h55334 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u13))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step100068 (p2363 p2417 p2911 p4278 p4445 p4503 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h65035 : (¬ p2363) ∨ (¬ p2911) ∨ (¬ p4278) ∨ (¬ p4445) ∨ (¬ p4503))
    : p2417 ∨ (¬ p2911) ∨ (¬ p4503) ∨ (¬ p4445) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h65035 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100072 (p2341 p2417 p2662 p2727 p2911 p3551 p4111 p4278 p5197 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73408 : p3551 ∨ p2341)
    (h73518 : p4111 ∨ p2727)
    (h43635 : (¬ p2662) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p5197))
    : p2417 ∨ p2341 ∨ (¬ p2662) ∨ p2727 ∨ (¬ p2911) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43635 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step100073 (p2249 p2417 p2641 p2651 p2657 p2922 p2928 p3461 p3487 p3506 p4191 p4278 p4421 p4621 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73530 : p4191 ∨ p3461)
    (h73288 : p2657 ∨ p2651)
    (h73320 : p2928 ∨ p2922)
    (h57019 : (¬ p2249) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2928) ∨ (¬ p3487) ∨ (¬ p3506) ∨ (¬ p4191) ∨ (¬ p4278) ∨ (¬ p4421) ∨ (¬ p4621))
    : p2417 ∨ p3461 ∨ p2651 ∨ (¬ p2249) ∨ (¬ p2641) ∨ (¬ p4421) ∨ (¬ p3506) ∨ (¬ p3487) ∨ (¬ p4621) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u13 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h57019 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step100074 (p2396 p2417 p2573 p2579 p2630 p2662 p2810 p3581 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73274 : p2579 ∨ p2573)
    (h73316 : p2810 ∨ p2630)
    (h44930 : (¬ p2396) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3581) ∨ (¬ p4278))
    : p2417 ∨ (¬ p2396) ∨ p2573 ∨ p2630 ∨ (¬ p3581) ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44930 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step100076 (p2417 p2441 p2850 p2881 p3246 p3570 p3684 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73418 : p3570 ∨ p2881)
    (h73442 : p3684 ∨ p2850)
    (h49751 : (¬ p2441) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3684) ∨ (¬ p4278))
    : p2417 ∨ (¬ p3246) ∨ p2881 ∨ p2850 ∨ (¬ p2441) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49751 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100078 (p2210 p2417 p2598 p3055 p3201 p3707 p3876 p4278 p4322 p4395 p4736 p4942 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73546 : p4278 ∨ p2417)
    (h73350 : p3055 ∨ p2598)
    (h50523 : (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3707) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4322) ∨ (¬ p4395) ∨ (¬ p4736) ∨ (¬ p4942))
    : (¬ p3707) ∨ (¬ p4322) ∨ (¬ p4942) ∨ p3201 ∨ (¬ p2210) ∨ p2417 ∨ (¬ p4395) ∨ p2598 ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4942 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50523 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step100079 (p2248 p2417 p2922 p2928 p3286 p3379 p3452 p3506 p4278 p4322 p4395 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73394 : p3452 ∨ p3379)
    (h73320 : p2928 ∨ p2922)
    (h61376 : (¬ p2248) ∨ (¬ p2928) ∨ (¬ p3286) ∨ (¬ p3452) ∨ (¬ p3506) ∨ (¬ p4278) ∨ (¬ p4322) ∨ (¬ p4395))
    : (¬ p4322) ∨ p2417 ∨ (¬ p3286) ∨ (¬ p4395) ∨ p3379 ∨ (¬ p3506) ∨ p2922 ∨ (¬ p2248) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h61376 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step100080 (p2248 p2417 p2881 p2901 p2922 p2928 p2946 p3379 p3452 p4278 p4666 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73546 : p4278 ∨ p2417)
    (h73394 : p3452 ∨ p3379)
    (h53665 : (¬ p2248) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2928) ∨ (¬ p2946) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4666))
    : p2922 ∨ p2417 ∨ p3379 ∨ (¬ p2248) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p4666) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53665 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step100084 (p2241 p2247 p2417 p2598 p2744 p3055 p3073 p3201 p3366 p3449 p3876 p4278 p4669 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h73546 : p4278 ∨ p2417)
    (h61838 : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669))
    : p2241 ∨ p3201 ∨ (¬ p4669) ∨ p2598 ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3073) ∨ p2417 ∨ (¬ p2744) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h61838 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step100085 (p2210 p2417 p2598 p3055 p3146 p3201 p3366 p3449 p3555 p3876 p4278 p4377 p4446 p4669 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h73546 : p4278 ∨ p2417)
    (h63554 : (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4377) ∨ (¬ p4446) ∨ (¬ p4669))
    : p2210 ∨ p3201 ∨ (¬ p4669) ∨ (¬ p4446) ∨ p2598 ∨ (¬ p3449) ∨ (¬ p3366) ∨ p2417 ∨ (¬ p3146) ∨ (¬ p4377) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4446 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63554 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step100088 (p2177 p2248 p2295 p2331 p2417 p2922 p2928 p3379 p3452 p4278 p4666 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73546 : p4278 ∨ p2417)
    (h73394 : p3452 ∨ p3379)
    (h48861 : (¬ p2177) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4666))
    : p2922 ∨ p2417 ∨ (¬ p2331) ∨ p3379 ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p4666) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48861 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step100089 (p2417 p2437 p2630 p2696 p2810 p3365 p3742 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73452 : p3742 ∨ p2437)
    (h73390 : p3365 ∨ p2696)
    (h73316 : p2810 ∨ p2630)
    (h43021 : (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3742) ∨ (¬ p4278))
    : p2417 ∨ p2437 ∨ p2696 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43021 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100093 (p2417 p2936 p3399 p3830 p4278 p4366 p5362 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73546 : p4278 ∨ p2417)
    (h42639 : (¬ p2936) ∨ (¬ p3830) ∨ (¬ p4278) ∨ (¬ p4366) ∨ (¬ p5362))
    : (¬ p5362) ∨ p3399 ∨ (¬ p3830) ∨ p2417 ∨ (¬ p2936) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5362 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2936 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42639 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step100096 (p2417 p2911 p3941 p4278 p4445 p5122 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h48044 : (¬ p2911) ∨ (¬ p3941) ∨ (¬ p4278) ∨ (¬ p4445) ∨ (¬ p5122))
    : p2417 ∨ (¬ p2911) ∨ (¬ p5122) ∨ (¬ p3941) ∨ (¬ p4445) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48044 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100097 (p2417 p2911 p2926 p3379 p3452 p3527 p3548 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73404 : p3548 ∨ p3527)
    (h73394 : p3452 ∨ p3379)
    (h44249 : (¬ p2911) ∨ (¬ p2926) ∨ (¬ p3452) ∨ (¬ p3548) ∨ (¬ p4278))
    : p2417 ∨ p3527 ∨ (¬ p2911) ∨ (¬ p2926) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2926 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44249 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100099 (p2417 p3051 p3212 p3556 p4135 p4277 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73414 : p3556 ∨ p3051)
    (h50243 : (¬ p3212) ∨ (¬ p3556) ∨ (¬ p4135) ∨ (¬ p4277) ∨ (¬ p4278))
    : (¬ p4135) ∨ p2417 ∨ p3051 ∨ (¬ p3212) ∨ (¬ p4277) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4135 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50243 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100100 (p2417 p2901 p3115 p4135 p4277 p4278 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73546 : p4278 ∨ p2417)
    (h52304 : (¬ p3115) ∨ (¬ p4135) ∨ (¬ p4277) ∨ (¬ p4278) ∨ (¬ p4320))
    : (¬ p4135) ∨ (¬ p3115) ∨ p2901 ∨ p2417 ∨ (¬ p4277) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4135 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52304 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100101 (p2341 p2417 p2911 p2996 p3551 p4155 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73408 : p3551 ∨ p2341)
    (h60150 : (¬ p2911) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4278))
    : p2417 ∨ p2341 ∨ (¬ p2911) ∨ (¬ p2996) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60150 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100105 (p2417 p4634 p4638 : Prop)
    (h73680 : p4634 ∨ p2417)
    (h7414 : (¬ p4634) ∨ p4638)
    : p2417 ∨ p4638 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4638) := (fun h => hn (Or.inr h));
    let u2 : p4634 := (Or.elim h73680 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7414 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100110 (p2449 p2630 p2685 p3516 p3572 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73420 : p3572 ∨ p2685)
    (h56505 : (¬ p2630) ∨ (¬ p3516) ∨ (¬ p3572) ∨ (¬ p3947))
    : p2449 ∨ (¬ p3516) ∨ p2685 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56505 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100111 (p2449 p3166 p3172 p3516 p3947 p4104 p4386 p5062 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73494 : p3947 ∨ p2449)
    (h45558 : (¬ p3172) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4104) ∨ (¬ p4386) ∨ (¬ p5062))
    : (¬ p3516) ∨ p3166 ∨ (¬ p5062) ∨ (¬ p4386) ∨ p2449 ∨ (¬ p4104) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5062 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45558 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step100114 (p2449 p2630 p2685 p3246 p3572 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73420 : p3572 ∨ p2685)
    (h44083 : (¬ p2630) ∨ (¬ p3246) ∨ (¬ p3572) ∨ (¬ p3947))
    : p2449 ∨ (¬ p3246) ∨ (¬ p2630) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44083 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100116 (p2264 p2449 p2696 p3434 p3947 p4781 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h60926 : (¬ p2264) ∨ (¬ p2696) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4781))
    : p2449 ∨ (¬ p3434) ∨ (¬ p4781) ∨ (¬ p2696) ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h60926 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100117 (p2264 p2352 p2363 p2449 p2573 p2579 p2696 p3434 p3589 p3947 p3956 p4347 p4781 p5193 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73560 : p4347 ∨ p2363)
    (h73274 : p2579 ∨ p2573)
    (h73500 : p3956 ∨ p2352)
    (h51407 : (¬ p2264) ∨ (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3434) ∨ (¬ p3589) ∨ (¬ p3947) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4781) ∨ (¬ p5193))
    : (¬ p3434) ∨ p2449 ∨ p2363 ∨ (¬ p2696) ∨ (¬ p2264) ∨ p2573 ∨ (¬ p5193) ∨ (¬ p3589) ∨ (¬ p4781) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h51407 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step100120 (p2449 p2761 p3680 p3947 p4192 p4280 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73494 : p3947 ∨ p2449)
    (h41087 : (¬ p3680) ∨ (¬ p3947) ∨ (¬ p4192) ∨ (¬ p4280) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3680) ∨ (¬ p4192) ∨ p2449 ∨ (¬ p4280) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41087 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100122 (p2417 p2449 p2911 p2996 p3644 p3947 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73494 : p3947 ∨ p2449)
    (h52376 : (¬ p2417) ∨ (¬ p2996) ∨ (¬ p3644) ∨ (¬ p3947))
    : (¬ p2417) ∨ (¬ p2996) ∨ p2911 ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52376 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100124 (p2417 p2449 p3016 p3741 p3947 p4112 p4717 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h56763 : (¬ p2417) ∨ (¬ p3016) ∨ (¬ p3741) ∨ (¬ p3947) ∨ (¬ p4112) ∨ (¬ p4717))
    : p2449 ∨ (¬ p2417) ∨ (¬ p4717) ∨ (¬ p3016) ∨ (¬ p4112) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h56763 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step100125 (p2449 p2761 p3192 p3276 p3947 p4327 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73494 : p3947 ∨ p2449)
    (h41100 : (¬ p3192) ∨ (¬ p3276) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3276) ∨ (¬ p4327) ∨ p2449 ∨ (¬ p3192) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4327 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41100 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100128 (p2264 p2363 p2449 p3947 p4445 p4503 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h54024 : (¬ p2264) ∨ (¬ p2363) ∨ (¬ p3947) ∨ (¬ p4445) ∨ (¬ p4503))
    : p2449 ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p4445) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h54024 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step100129 (p2177 p2449 p2911 p3192 p3644 p3947 p4451 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73434 : p3644 ∨ p2911)
    (h72220 : (¬ p3947) ∨ (¬ p2177) ∨ (¬ p4451) ∨ (¬ p3192) ∨ (¬ p3644))
    : p2449 ∨ (¬ p3192) ∨ (¬ p2177) ∨ (¬ p4451) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h72220 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step100130 (p2417 p2449 p2727 p2911 p3644 p3947 p4111 p4112 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73434 : p3644 ∨ p2911)
    (h73518 : p4111 ∨ p2727)
    (h58899 : (¬ p2417) ∨ (¬ p3644) ∨ (¬ p3947) ∨ (¬ p4111) ∨ (¬ p4112))
    : p2449 ∨ (¬ p2417) ∨ (¬ p4112) ∨ p2911 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58899 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100131 (p2417 p2449 p2807 p2911 p3414 p3644 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73434 : p3644 ∨ p2911)
    (h73392 : p3414 ∨ p2807)
    (h47139 : (¬ p2417) ∨ (¬ p3414) ∨ (¬ p3644) ∨ (¬ p3947))
    : p2449 ∨ (¬ p2417) ∨ p2911 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47139 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100136 (p2264 p2449 p3553 p3945 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73409 : (¬ p2264) ∨ (¬ p3553))
    (h23266 : p3553 ∨ (¬ p3945) ∨ (¬ p3947))
    : p2449 ∨ (¬ p2264) ∨ (¬ p3945) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3553) := (Or.elim h73409 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h23266 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step100143 (p2427 p2449 p2982 p3947 p4135 p4235 p4280 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73494 : p3947 ∨ p2449)
    (h41460 : (¬ p2982) ∨ (¬ p3947) ∨ (¬ p4135) ∨ (¬ p4235) ∨ (¬ p4280))
    : (¬ p4135) ∨ (¬ p2982) ∨ p2427 ∨ (¬ p4280) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4135 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41460 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100149 (p2449 p2807 p2946 p3136 p3414 p3947 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73494 : p3947 ∨ p2449)
    (h73392 : p3414 ∨ p2807)
    (h46390 : (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4315))
    : p3136 ∨ p2449 ∨ (¬ p2946) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46390 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100150 (p2449 p2608 p2685 p2737 p2743 p3572 p3947 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73298 : p2743 ∨ p2737)
    (h73420 : p3572 ∨ p2685)
    (h73494 : p3947 ∨ p2449)
    (h44431 : (¬ p2743) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p3954))
    : p2608 ∨ p2737 ∨ p2685 ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44431 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100153 (p2449 p2685 p2946 p2952 p3136 p3572 p3947 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73494 : p3947 ∨ p2449)
    (h73420 : p3572 ∨ p2685)
    (h42753 : (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p3947))
    : p2946 ∨ (¬ p3136) ∨ p2449 ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42753 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100156 (p2166 p2210 p2449 p2685 p2696 p3146 p3365 p3572 p3947 p4669 p4736 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73420 : p3572 ∨ p2685)
    (h73390 : p3365 ∨ p2696)
    (h52137 : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3146) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4736))
    : p2449 ∨ p2685 ∨ p2696 ∨ (¬ p3146) ∨ (¬ p2210) ∨ (¬ p2166) ∨ (¬ p4736) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52137 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step100158 (p2449 p2685 p2696 p3193 p3222 p3266 p3276 p3365 p3366 p3572 p3947 p4376 p4444 p4669 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73580 : p4444 ∨ p3266)
    (h73390 : p3365 ∨ p2696)
    (h73420 : p3572 ∨ p2685)
    (h73494 : p3947 ∨ p2449)
    (h58805 : (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p4669))
    : p3193 ∨ p3266 ∨ p2696 ∨ p2685 ∨ (¬ p4669) ∨ (¬ p3276) ∨ (¬ p3366) ∨ p2449 ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58805 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step100160 (p2449 p2685 p3005 p3572 p3947 p4378 p4666 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73420 : p3572 ∨ p2685)
    (h60110 : (¬ p3005) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4378) ∨ (¬ p4666))
    : (¬ p3005) ∨ (¬ p4378) ∨ (¬ p4666) ∨ p2449 ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60110 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100161 (p2352 p2363 p2449 p2573 p2685 p2696 p3365 p3366 p3519 p3572 p3947 p4376 p4669 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h73390 : p3365 ∨ p2696)
    (h73494 : p3947 ∨ p2449)
    (h52104 : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4376) ∨ (¬ p4669))
    : p2685 ∨ (¬ p2352) ∨ p2696 ∨ (¬ p4376) ∨ (¬ p3519) ∨ (¬ p3366) ∨ (¬ p4669) ∨ (¬ p2363) ∨ (¬ p2573) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h52104 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step100164 (p2210 p2449 p2685 p2696 p2881 p2891 p3365 p3572 p3947 p4666 p4736 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73390 : p3365 ∨ p2696)
    (h73420 : p3572 ∨ p2685)
    (h49546 : (¬ p2210) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4666) ∨ (¬ p4736))
    : p2449 ∨ (¬ p2881) ∨ (¬ p4736) ∨ (¬ p2891) ∨ p2696 ∨ p2685 ∨ (¬ p2210) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49546 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step100165 (p2331 p2449 p2685 p2797 p2963 p3572 p3947 p4236 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73420 : p3572 ∨ p2685)
    (h73494 : p3947 ∨ p2449)
    (h45264 : (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4236))
    : p2331 ∨ (¬ p4236) ∨ p2685 ∨ p2449 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45264 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step100167 (p2166 p2210 p2254 p2449 p2761 p2807 p3414 p3947 p3969 p4381 p5119 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73392 : p3414 ∨ p2807)
    (h73494 : p3947 ∨ p2449)
    (h54247 : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p3969) ∨ (¬ p4381) ∨ (¬ p5119))
    : p2761 ∨ (¬ p3969) ∨ (¬ p2166) ∨ p2807 ∨ p2449 ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54247 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step100170 (p2132 p2449 p2761 p2807 p2860 p3414 p3737 p3947 p4381 p4789 p5250 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73574 : p4381 ∨ p2761)
    (h73494 : p3947 ∨ p2449)
    (h65102 : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3414) ∨ (¬ p3737) ∨ (¬ p3947) ∨ (¬ p4381) ∨ (¬ p4789) ∨ (¬ p5250))
    : (¬ p3737) ∨ p2807 ∨ (¬ p2132) ∨ (¬ p2860) ∨ p2761 ∨ (¬ p5250) ∨ p2449 ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h65102 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step100172 (p2449 p2685 p2696 p2761 p3365 p3572 p3947 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73494 : p3947 ∨ p2449)
    (h73420 : p3572 ∨ p2685)
    (h73390 : p3365 ∨ p2696)
    (h46215 : (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4381))
    : p2761 ∨ p2449 ∨ p2685 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46215 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100173 (p2383 p2417 p2449 p3567 p3921 p3947 p4067 p4405 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h57111 : (¬ p2383) ∨ (¬ p2417) ∨ (¬ p3567) ∨ (¬ p3921) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4405))
    : (¬ p2417) ∨ p2449 ∨ (¬ p3921) ∨ (¬ p2383) ∨ (¬ p3567) ∨ (¬ p4067) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57111 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step100175 (p2230 p2427 p2449 p2685 p2696 p2881 p3365 p3572 p3947 p4419 p4666 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73390 : p3365 ∨ p2696)
    (h73420 : p3572 ∨ p2685)
    (h42598 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4419) ∨ (¬ p4666))
    : p2449 ∨ (¬ p2881) ∨ p2696 ∨ (¬ p4419) ∨ p2685 ∨ (¬ p2427) ∨ (¬ p2230) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42598 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step100176 (p2449 p3246 p3947 p4009 p4044 p5558 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h61975 : (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4009) ∨ (¬ p4044) ∨ (¬ p5558))
    : (¬ p4009) ∨ p2449 ∨ (¬ p5558) ∨ (¬ p3246) ∨ (¬ p4044) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61975 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100177 (p2449 p2870 p3105 p3947 p4135 p4244 p4280 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73494 : p3947 ∨ p2449)
    (h60017 : (¬ p3105) ∨ (¬ p3947) ∨ (¬ p4135) ∨ (¬ p4244) ∨ (¬ p4280))
    : (¬ p3105) ∨ (¬ p4135) ∨ p2870 ∨ (¬ p4280) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60017 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100179 (p2264 p2449 p2707 p3434 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h46094 : (¬ p2264) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3947))
    : (¬ p3434) ∨ p2449 ∨ (¬ p2264) ∨ (¬ p2707) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46094 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100180 (p2449 p2707 p2737 p2743 p3434 p3947 p4112 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73298 : p2743 ∨ p2737)
    (h57228 : (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4112))
    : (¬ p3434) ∨ p2449 ∨ (¬ p4112) ∨ p2737 ∨ (¬ p2707) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57228 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100181 (p2187 p2383 p2449 p2685 p2696 p2781 p3125 p3365 p3572 p3947 p3989 p4621 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73420 : p3572 ∨ p2685)
    (h73502 : p3989 ∨ p2187)
    (h73390 : p3365 ∨ p2696)
    (h51146 : (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p3989) ∨ (¬ p4621))
    : p2449 ∨ p2685 ∨ (¬ p3125) ∨ p2187 ∨ (¬ p4621) ∨ (¬ p2383) ∨ (¬ p2781) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51146 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step100183 (p2449 p3516 p3947 p4066 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h6051 : (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4066))
    : (¬ p3516) ∨ (¬ p4066) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6051 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step100184 (p2881 p2911 p3569 p3570 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73417 : (¬ p2881) ∨ (¬ p3570))
    (h40275 : (¬ p3569) ∨ p3570 ∨ (¬ p3644))
    : (¬ p3569) ∨ p2911 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3569 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p3570) := (Or.elim h73417 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h40275 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step100193 (p3201 p3422 p3569 p3584 p4140 p5472 p5514 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h42606 : (¬ p3201) ∨ (¬ p3569) ∨ (¬ p3584) ∨ (¬ p4140) ∨ (¬ p5472) ∨ (¬ p5514))
    : (¬ p3201) ∨ (¬ p5514) ∨ p3422 ∨ (¬ p4140) ∨ (¬ p3569) ∨ (¬ p5472) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42606 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step100198 (p2727 p3402 p4809 : Prop)
    (h73770 : p4809 ∨ p2727)
    (h7855 : p3402 ∨ (¬ p4809))
    : p3402 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3402) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr h));
    let u2 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7855 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step100200 (p2727 p4809 p4811 : Prop)
    (h73770 : p4809 ∨ p2727)
    (h7859 : (¬ p4809) ∨ p4811)
    : p2727 ∨ p4811 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4811) := (fun h => hn (Or.inr h));
    let u2 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7859 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100201 (p2727 p4111 p4650 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h43562 : (¬ p4111) ∨ p4650)
    : p2727 ∨ p4650 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4650) := (fun h => hn (Or.inr h));
    let u2 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43562 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100203 (p2727 p4111 p4814 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h48299 : (¬ p4111) ∨ p4814)
    : p2727 ∨ p4814 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4814) := (fun h => hn (Or.inr h));
    let u2 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48299 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100204 (p2727 p2751 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h54649 : p2751 ∨ (¬ p4111))
    : p2751 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2751) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr h));
    let u2 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54649 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step100205 (p2459 p2470 p2476 p2528 p2534 p2662 p2727 p4111 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73518 : p4111 ∨ p2727)
    (h73250 : p2476 ∨ p2470)
    (h43646 : (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p4111))
    : p2528 ∨ p2727 ∨ (¬ p2459) ∨ p2470 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43646 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step100206 (p2528 p2534 p2651 p2727 p3166 p3172 p4111 p4437 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73356 : p3172 ∨ p3166)
    (h73518 : p4111 ∨ p2727)
    (h54993 : (¬ p2534) ∨ (¬ p2651) ∨ (¬ p3172) ∨ (¬ p4111) ∨ (¬ p4437))
    : p2528 ∨ p3166 ∨ (¬ p2651) ∨ (¬ p4437) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54993 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100216 (p2727 p2748 p3136 p3343 p3359 p4111 p4241 p4949 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73388 : p3359 ∨ p3343)
    (h41359 : (¬ p2748) ∨ (¬ p3136) ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4949))
    : (¬ p2748) ∨ p2727 ∨ (¬ p3136) ∨ p3343 ∨ (¬ p4949) ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2748 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41359 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step100219 (p2630 p2707 p2727 p2741 p4111 p4782 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h48017 : (¬ p2630) ∨ (¬ p2707) ∨ (¬ p2741) ∨ (¬ p4111) ∨ (¬ p4782))
    : (¬ p2707) ∨ p2727 ∨ (¬ p2630) ∨ (¬ p2741) ∨ (¬ p4782) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48017 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step100223 (p2651 p2727 p2741 p2811 p2829 p4111 p4845 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h42514 : (¬ p2651) ∨ (¬ p2741) ∨ (¬ p2811) ∨ (¬ p2829) ∨ (¬ p4111) ∨ (¬ p4845))
    : (¬ p2741) ∨ (¬ p2811) ∨ (¬ p2829) ∨ (¬ p4845) ∨ (¬ p2651) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2741 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42514 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step100225 (p2630 p2727 p2741 p2829 p4111 p4845 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h42060 : (¬ p2630) ∨ (¬ p2741) ∨ (¬ p2829) ∨ (¬ p4111) ∨ (¬ p4845))
    : (¬ p2741) ∨ p2727 ∨ (¬ p2630) ∨ (¬ p4845) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2741 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42060 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100226 (p2651 p2727 p2745 p2946 p2952 p3136 p4111 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73518 : p4111 ∨ p2727)
    (h48147 : (¬ p2651) ∨ (¬ p2745) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4111))
    : (¬ p2651) ∨ p2946 ∨ (¬ p2745) ∨ p2727 ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48147 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step100232 (p2241 p2247 p2727 p3449 p4111 p4288 p5011 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73226 : p2247 ∨ p2241)
    (h42000 : (¬ p2247) ∨ (¬ p3449) ∨ (¬ p4111) ∨ (¬ p4288) ∨ (¬ p5011))
    : p2727 ∨ p2241 ∨ (¬ p3449) ∨ (¬ p5011) ∨ (¬ p4288) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5011 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42000 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100236 (p2241 p2247 p2630 p2727 p3136 p4111 p4315 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73226 : p2247 ∨ p2241)
    (h73550 : p4315 ∨ p3136)
    (h44656 : (¬ p2247) ∨ (¬ p2630) ∨ (¬ p4111) ∨ (¬ p4315))
    : p2727 ∨ p2241 ∨ (¬ p2630) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44656 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step100237 (p2241 p2247 p2630 p2727 p2797 p4111 p4195 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73226 : p2247 ∨ p2241)
    (h73532 : p4195 ∨ p2797)
    (h55057 : (¬ p2247) ∨ (¬ p2630) ∨ (¬ p4111) ∨ (¬ p4195))
    : p2727 ∨ p2241 ∨ p2797 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55057 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step100240 (p2331 p2641 p2727 p2946 p2963 p4111 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73518 : p4111 ∨ p2727)
    (h45006 : (¬ p2641) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p4111))
    : (¬ p2641) ∨ p2331 ∨ p2727 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45006 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100242 (p2241 p2247 p2727 p2819 p3083 p3654 p3917 p4111 p4256 p4384 p5017 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73518 : p4111 ∨ p2727)
    (h73542 : p4256 ∨ p3083)
    (h53781 : (¬ p2247) ∨ (¬ p2819) ∨ (¬ p3654) ∨ (¬ p3917) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p5017))
    : (¬ p3917) ∨ (¬ p5017) ∨ p2241 ∨ p2727 ∨ (¬ p3654) ∨ (¬ p2819) ∨ p3083 ∨ (¬ p4384) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3917 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h53781 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step100245 (p2230 p2255 p2440 p2727 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h67867 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2255) ∨ (¬ p4111))
    : (¬ p2230) ∨ p2727 ∨ (¬ p2255) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67867 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100247 (p2553 p2588 p2727 p2741 p3323 p3564 p4037 p4111 p4194 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73518 : p4111 ∨ p2727)
    (h73508 : p4037 ∨ p3323)
    (h42997 : (¬ p2588) ∨ (¬ p2741) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4111) ∨ (¬ p4194))
    : (¬ p3564) ∨ (¬ p4194) ∨ (¬ p2741) ∨ p2553 ∨ p2727 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42997 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step100248 (p2274 p2440 p2553 p2588 p2590 p2727 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73282 : p2588 ∨ p2553)
    (h56837 : (¬ p2274) ∨ (¬ p2440) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p4111))
    : (¬ p2440) ∨ p2727 ∨ (¬ p2590) ∨ (¬ p2274) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56837 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100250 (p2253 p2651 p2727 p3276 p3707 p3833 p4111 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73518 : p4111 ∨ p2727)
    (h51699 : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p3707) ∨ (¬ p3833) ∨ (¬ p4111) ∨ (¬ p4425))
    : p3276 ∨ (¬ p3707) ∨ (¬ p2651) ∨ (¬ p3833) ∨ (¬ p2253) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3833 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51699 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step100254 (p2241 p2247 p2761 p3189 p3256 p3276 p3355 p3950 p4118 p4360 p4381 p5190 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73566 : p4360 ∨ p3189)
    (h73574 : p4381 ∨ p2761)
    (h73520 : p4118 ∨ p3256)
    (h62305 : (¬ p2247) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4381) ∨ (¬ p5190))
    : p2241 ∨ p3189 ∨ (¬ p3276) ∨ p2761 ∨ (¬ p5190) ∨ (¬ p3355) ∨ (¬ p3950) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62305 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step100256 (p2440 p3266 p3276 p3343 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h53790 : (¬ p2440) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53790 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100257 (p2651 p2761 p3276 p3343 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h46568 : (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3276) ∨ (¬ p2651) ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46568 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100258 (p2440 p2761 p3276 p3343 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h59921 : (¬ p2440) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3276) ∨ (¬ p2440) ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h59921 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100259 (p2437 p2761 p3276 p3343 p3742 p3921 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73452 : p3742 ∨ p2437)
    (h52483 : (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3742) ∨ (¬ p3921) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3276) ∨ p2437 ∨ (¬ p3343) ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52483 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100262 (p2295 p2750 p2753 p3276 p3309 p3323 p3355 p3362 p3549 p4037 p4245 p4322 p4397 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73406 : p3549 ∨ p3309)
    (h64626 : (¬ p2295) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3549) ∨ (¬ p4037) ∨ (¬ p4245) ∨ (¬ p4322) ∨ (¬ p4397))
    : (¬ p4322) ∨ (¬ p3276) ∨ (¬ p2295) ∨ (¬ p2753) ∨ (¬ p4245) ∨ (¬ p3362) ∨ (¬ p2750) ∨ (¬ p4397) ∨ p3323 ∨ (¬ p3355) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4397 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u12 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h64626 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step100264 (p3016 p3266 p3276 p3343 p3574 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73422 : p3574 ∨ p3016)
    (h44153 : (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4444))
    : (¬ p3343) ∨ p3266 ∨ p3016 ∨ (¬ p3276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44153 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100265 (p2630 p2656 p2761 p3276 p3355 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h46765 : (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p4381))
    : (¬ p3276) ∨ p2761 ∨ (¬ p3355) ∨ (¬ p2630) ∨ (¬ p2656) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46765 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100266 (p2122 p2246 p2651 p2744 p2774 p2780 p3276 p3343 p3366 p3822 p4260 p4831 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h52884 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p4260) ∨ (¬ p4831))
    : (¬ p4260) ∨ p2774 ∨ (¬ p3276) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p4831) ∨ (¬ p2246) ∨ (¬ p3343) ∨ p2122 ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h52884 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step100271 (p2248 p2651 p3093 p3276 p3343 p3591 p3923 p5123 p5580 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h58579 : (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p3343) ∨ (¬ p5123) ∨ p3093 ∨ (¬ p2651) ∨ (¬ p3923) ∨ (¬ p3276) ∨ (¬ p2248) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58579 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step100275 (p2352 p3276 p3461 p3956 p4025 p4191 p4422 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73500 : p3956 ∨ p2352)
    (h72222 : (¬ p4191) ∨ (¬ p3276) ∨ (¬ p3956) ∨ (¬ p4422) ∨ (¬ p4025))
    : p3461 ∨ (¬ p3276) ∨ p2352 ∨ (¬ p4422) ∨ (¬ p4025) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72222 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step100277 (p3276 p3461 p3917 p4191 p4422 p5222 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h41307 : (¬ p3276) ∨ (¬ p3917) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p5222))
    : p3461 ∨ (¬ p3276) ∨ (¬ p4422) ∨ (¬ p5222) ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41307 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100278 (p3276 p3323 p3461 p4037 p4191 p4422 p4973 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73508 : p4037 ∨ p3323)
    (h49421 : (¬ p3276) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p4973))
    : (¬ p3276) ∨ p3461 ∨ (¬ p4422) ∨ (¬ p4973) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49421 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100282 (p2241 p2247 p2761 p3189 p3192 p3256 p3276 p3389 p3950 p4118 p4360 p4381 p5190 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73520 : p4118 ∨ p3256)
    (h73226 : p2247 ∨ p2241)
    (h73566 : p4360 ∨ p3189)
    (h62310 : (¬ p2247) ∨ (¬ p3192) ∨ (¬ p3276) ∨ (¬ p3389) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4381) ∨ (¬ p5190))
    : p2761 ∨ (¬ p3192) ∨ p3256 ∨ (¬ p3276) ∨ p2241 ∨ (¬ p5190) ∨ (¬ p3950) ∨ p3189 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62310 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step100283 (p2563 p3276 p4110 p4322 p4449 p5046 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h49625 : (¬ p3276) ∨ (¬ p4110) ∨ (¬ p4322) ∨ (¬ p4449) ∨ (¬ p5046))
    : (¬ p4322) ∨ (¬ p3276) ∨ p2563 ∨ (¬ p5046) ∨ (¬ p4449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49625 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100288 (p3461 p3990 p4191 p5117 p5580 : Prop)
    (h73529 : (¬ p3461) ∨ (¬ p4191))
    (h36265 : (¬ p3990) ∨ p4191 ∨ (¬ p5117) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p5117) ∨ (¬ p3990) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4191) := (Or.elim h73529 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    (Or.elim h36265 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step100291 (p2252 p2741 p3073 p3286 p3292 p3379 p3449 p3452 p3461 p4376 p4604 p5284 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73378 : p3292 ∨ p3286)
    (h42386 : (¬ p2252) ∨ (¬ p2741) ∨ (¬ p3073) ∨ (¬ p3292) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3461) ∨ (¬ p4376) ∨ (¬ p4604) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3073) ∨ (¬ p4604) ∨ p3379 ∨ (¬ p4376) ∨ (¬ p3461) ∨ (¬ p2252) ∨ p3286 ∨ (¬ p2741) ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42386 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step100293 (p3146 p3266 p3461 p3692 p3990 p4433 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73448 : p3692 ∨ p3146)
    (h41794 : (¬ p3461) ∨ (¬ p3692) ∨ (¬ p3990) ∨ (¬ p4433) ∨ (¬ p4444))
    : p3266 ∨ p3146 ∨ (¬ p3990) ∨ (¬ p3461) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41794 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100295 (p2459 p3266 p3461 p3990 p4348 p4444 p4503 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73562 : p4348 ∨ p2459)
    (h48030 : (¬ p3461) ∨ (¬ p3990) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p4503))
    : p3266 ∨ (¬ p3461) ∨ (¬ p3990) ∨ p2459 ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48030 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step100300 (p2331 p2641 p2963 p3286 p3461 p4367 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h44057 : (¬ p2641) ∨ (¬ p2963) ∨ (¬ p3286) ∨ (¬ p3461) ∨ (¬ p4367))
    : (¬ p3286) ∨ (¬ p4367) ∨ (¬ p2641) ∨ (¬ p3461) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44057 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step100303 (p2573 p3016 p3343 p3461 p3574 p4331 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h64386 : (¬ p2573) ∨ (¬ p3343) ∨ (¬ p3461) ∨ (¬ p3574) ∨ (¬ p4331))
    : (¬ p3343) ∨ (¬ p3461) ∨ p3016 ∨ (¬ p2573) ∨ (¬ p4331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64386 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step100304 (p2761 p3434 p3461 p4187 p4324 p4381 p4473 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73556 : p4324 ∨ p3434)
    (h41042 : (¬ p3461) ∨ (¬ p4187) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4473))
    : p2761 ∨ (¬ p4187) ∨ p3434 ∨ (¬ p4473) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p4187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41042 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100308 (p2264 p2459 p2807 p3276 p3346 p3461 p3905 p4425 p4604 p4786 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h63435 : (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3346) ∨ (¬ p3461) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p4604) ∨ (¬ p4786))
    : p3276 ∨ (¬ p3461) ∨ (¬ p4604) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3346) ∨ (¬ p2264) ∨ (¬ p3905) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63435 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step100309 (p2761 p3246 p3461 p3690 p4187 p4381 p4556 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73446 : p3690 ∨ p3246)
    (h48022 : (¬ p3461) ∨ (¬ p3690) ∨ (¬ p4187) ∨ (¬ p4381) ∨ (¬ p4556))
    : p2761 ∨ (¬ p4187) ∨ (¬ p3461) ∨ p3246 ∨ (¬ p4556) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p4187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48022 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step100310 (p2315 p2761 p3461 p3516 p3821 p4187 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73470 : p3821 ∨ p3516)
    (h61619 : (¬ p2315) ∨ (¬ p3461) ∨ (¬ p3821) ∨ (¬ p4187) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3461) ∨ (¬ p2315) ∨ p3516 ∨ (¬ p4187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61619 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100311 (p2254 p2417 p2922 p3286 p3292 p3379 p3461 p4625 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h49083 : (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3292) ∨ (¬ p3379) ∨ (¬ p3461) ∨ (¬ p4625) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3461) ∨ (¬ p3379) ∨ (¬ p4625) ∨ p3286 ∨ (¬ p2417) ∨ (¬ p2254) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49083 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step100312 (p2341 p2911 p3246 p3286 p3292 p3366 p3461 p3519 p3569 p3644 p4236 p4376 p4399 p4625 p4988 p5284 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73378 : p3292 ∨ p3286)
    (h56968 : (¬ p2341) ∨ (¬ p3246) ∨ (¬ p3292) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p3519) ∨ (¬ p3569) ∨ (¬ p3644) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p4625) ∨ (¬ p4988) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p2341) ∨ (¬ p3461) ∨ (¬ p3519) ∨ (¬ p3569) ∨ (¬ p4988) ∨ p2911 ∨ p3286 ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p3246) ∨ (¬ p4399) ∨ (¬ p4625) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u15 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h56968 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u14))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u12))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u5))) (fun r12 => (False.elim (r12 u0)))))))))))))))))))))))))))))

theorem step100313 (p2797 p3461 p3755 p4035 p5284 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h55634 : (¬ p2797) ∨ (¬ p3461) ∨ (¬ p4035) ∨ (¬ p5284))
    : (¬ p5284) ∨ p3755 ∨ (¬ p2797) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h55634 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step100314 (p3136 p3461 p3755 p4035 p5284 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h46482 : (¬ p3136) ∨ (¬ p3461) ∨ (¬ p4035) ∨ (¬ p5284))
    : (¬ p5284) ∨ p3755 ∨ (¬ p3461) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46482 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step100315 (p2132 p2138 p2252 p2748 p3286 p3292 p3425 p3434 p3461 p3471 p4625 p5284 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73378 : p3292 ∨ p3286)
    (h73396 : p3471 ∨ p3425)
    (h67293 : (¬ p2748) ∨ (¬ p3461) ∨ (¬ p2252) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p2138) ∨ (¬ p5284) ∨ (¬ p3292) ∨ (¬ p4625))
    : p2132 ∨ (¬ p2748) ∨ (¬ p3434) ∨ (¬ p4625) ∨ (¬ p5284) ∨ (¬ p3461) ∨ p3286 ∨ p3425 ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h67293 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step100322 (p3631 p3817 p3950 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h42825 : (¬ p3817) ∨ p3950)
    : p3631 ∨ p3950 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3950) := (fun h => hn (Or.inr h));
    let u2 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42825 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100326 (p2745 p2797 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h49600 : p2745 ∨ (¬ p4195))
    : p2745 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2745) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr h));
    let u2 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49600 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step100329 (p3125 p3744 p5046 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h48287 : (¬ p3744) ∨ p5046)
    : p3125 ∨ p5046 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5046) := (fun h => hn (Or.inr h));
    let u2 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48287 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100331 (p2274 p3125 p3461 p3670 p3744 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73454 : p3744 ∨ p3125)
    (h43252 : (¬ p2274) ∨ (¬ p3670) ∨ (¬ p3744) ∨ (¬ p4191))
    : (¬ p3670) ∨ p3461 ∨ p3125 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43252 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100332 (p2230 p2459 p2563 p2589 p3125 p3399 p3527 p3744 p4110 p4604 p5193 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h62898 : (¬ p2459) ∨ (¬ p2589) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4604) ∨ (¬ p5193))
    : (¬ p3527) ∨ p3125 ∨ (¬ p4604) ∨ (¬ p2459) ∨ (¬ p5193) ∨ p2563 ∨ p2230 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62898 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step100333 (p2187 p2459 p3125 p3744 p4133 p4171 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h49275 : (¬ p2187) ∨ (¬ p2459) ∨ (¬ p3744) ∨ (¬ p4133) ∨ (¬ p4171))
    : p3125 ∨ (¬ p4171) ∨ (¬ p4133) ∨ (¬ p2459) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49275 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step100335 (p3016 p3125 p3343 p3574 p3744 p4331 p4718 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73454 : p3744 ∨ p3125)
    (h56889 : (¬ p3343) ∨ (¬ p3574) ∨ (¬ p3744) ∨ (¬ p4331) ∨ (¬ p4718))
    : (¬ p4331) ∨ (¬ p3343) ∨ p3016 ∨ (¬ p4718) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56889 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100338 (p2440 p2563 p3125 p3461 p3744 p4110 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73454 : p3744 ∨ p3125)
    (h73516 : p4110 ∨ p2563)
    (h63913 : (¬ p2440) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4191))
    : p3461 ∨ p3125 ∨ p2563 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h63913 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100339 (p2427 p3125 p3564 p3660 p3744 p4235 p4555 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73536 : p4235 ∨ p2427)
    (h41114 : (¬ p3564) ∨ (¬ p3660) ∨ (¬ p3744) ∨ (¬ p4235) ∨ (¬ p4555))
    : (¬ p3564) ∨ p3125 ∨ (¬ p3660) ∨ p2427 ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41114 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step100340 (p2230 p2589 p2850 p3096 p3125 p3422 p3584 p3744 p3905 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73454 : p3744 ∨ p3125)
    (h73284 : p2589 ∨ p2230)
    (h44300 : (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3584) ∨ (¬ p3744) ∨ (¬ p3905))
    : p3422 ∨ (¬ p2850) ∨ (¬ p3096) ∨ p3125 ∨ (¬ p3905) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h44300 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step100341 (p2187 p3125 p3744 p3989 p3990 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73501 : (¬ p2187) ∨ (¬ p3989))
    (h29759 : (¬ p3744) ∨ p3989 ∨ (¬ p3990))
    : p3125 ∨ (¬ p2187) ∨ (¬ p3990) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3989) := (Or.elim h73501 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h29759 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step100357 (p2662 p2727 p3276 p3346 p3680 p4111 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73518 : p4111 ∨ p2727)
    (h43610 : (¬ p2662) ∨ (¬ p3346) ∨ (¬ p3680) ∨ (¬ p4111) ∨ (¬ p4425))
    : p3276 ∨ (¬ p3680) ∨ (¬ p3346) ∨ p2727 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43610 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100360 (p3246 p4402 p6010 : Prop)
    (h74345 : p3246 ∨ (¬ p6010))
    (h13055 : p4402 ∨ p6010)
    : p4402 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4402) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6010) := (Or.elim h74345 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13055 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step100361 (p2274 p4204 p5818 : Prop)
    (h74101 : p2274 ∨ (¬ p5818))
    (h11907 : p4204 ∨ p5818)
    : p4204 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4204) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5818) := (Or.elim h74101 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11907 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step100363 (p2440 p4700 p5872 : Prop)
    (h74169 : (¬ p2440) ∨ (¬ p5872))
    (h12224 : p4700 ∨ p5872)
    : p4700 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4700) := (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5872) := (Or.elim h74169 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12224 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step100365 (p2440 p3879 p5872 : Prop)
    (h74169 : (¬ p2440) ∨ (¬ p5872))
    (h12222 : p3879 ∨ p5872)
    : p3879 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3879) := (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5872) := (Or.elim h74169 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12222 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step100367 (p2696 p4788 p4789 : Prop)
    (h73760 : p4788 ∨ (¬ p2696))
    (h7812 : (¬ p4788) ∨ p4789)
    : (¬ p2696) ∨ p4789 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4789) := (fun h => hn (Or.inr h));
    let u2 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7812 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100368 (p2696 p4788 p4790 : Prop)
    (h73760 : p4788 ∨ (¬ p2696))
    (h7813 : (¬ p4788) ∨ p4790)
    : (¬ p2696) ∨ p4790 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4790) := (fun h => hn (Or.inr h));
    let u2 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7813 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100369 (p2737 p2747 p2750 : Prop)
    (h73302 : p2747 ∨ (¬ p2737))
    (h3623 : (¬ p2747) ∨ p2750)
    : (¬ p2737) ∨ p2750 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2750) := (fun h => hn (Or.inr h));
    let u2 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h3623 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100370 (p2737 p2747 p2751 : Prop)
    (h73302 : p2747 ∨ (¬ p2737))
    (h3624 : (¬ p2747) ∨ p2751)
    : (¬ p2737) ∨ p2751 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2751) := (fun h => hn (Or.inr h));
    let u2 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h3624 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100372 (p2440 p2696 p2737 p3365 p3367 p3585 p4343 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73390 : p3365 ∨ p2696)
    (h57262 : (¬ p2440) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p4343))
    : (¬ p2737) ∨ p3367 ∨ p2696 ∨ (¬ p4343) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57262 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100375 (p2737 p3083 p3367 p3585 p3641 p3874 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73428 : p3585 ∨ p3367)
    (h46512 : (¬ p2737) ∨ (¬ p3083) ∨ (¬ p3585) ∨ (¬ p3874))
    : p3641 ∨ (¬ p2737) ∨ p3367 ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46512 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100377 (p2737 p3016 p3367 p3422 p3584 p3585 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73428 : p3585 ∨ p3367)
    (h45478 : (¬ p2737) ∨ (¬ p3016) ∨ (¬ p3584) ∨ (¬ p3585))
    : (¬ p2737) ∨ p3422 ∨ p3367 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45478 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100378 (p2166 p2191 p2619 p2737 p4874 : Prop)
    (h73222 : p2191 ∨ p2166)
    (h67324 : (¬ p2737) ∨ (¬ p2619) ∨ (¬ p2191) ∨ (¬ p4874))
    : (¬ p2619) ∨ (¬ p2737) ∨ (¬ p4874) ∨ p2166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67324 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step100380 (p2136 p2220 p2619 p2737 p3366 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h67271 : (¬ p2737) ∨ (¬ p2619) ∨ (¬ p2136) ∨ (¬ p3366) ∨ (¬ p4120))
    : (¬ p2619) ∨ (¬ p2136) ∨ p2220 ∨ (¬ p3366) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67271 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100381 (p2651 p2737 p2811 p2839 p3583 p4316 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h69698 : (¬ p3583) ∨ (¬ p4316) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2651))
    : (¬ p2737) ∨ p2839 ∨ (¬ p2811) ∨ (¬ p2651) ∨ (¬ p4316) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69698 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100383 (p2331 p2641 p2737 p2750 p2811 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h51678 : (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2750) ∨ (¬ p2811) ∨ (¬ p4154))
    : p2641 ∨ (¬ p2811) ∨ (¬ p2750) ∨ (¬ p2737) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51678 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100384 (p2737 p2972 p3105 p4363 p4874 : Prop)
    (h73568 : p4363 ∨ p2972)
    (h67321 : (¬ p2737) ∨ (¬ p3105) ∨ (¬ p4363) ∨ (¬ p4874))
    : (¬ p3105) ∨ p2972 ∨ (¬ p2737) ∨ (¬ p4874) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2972) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4363 := (Or.elim h73568 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67321 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step100387 (p2737 p3319 p3483 p3953 p4026 p4842 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h41834 : (¬ p2737) ∨ (¬ p3483) ∨ (¬ p3953) ∨ (¬ p4026) ∨ (¬ p4842))
    : (¬ p3483) ∨ p3319 ∨ (¬ p4842) ∨ (¬ p2737) ∨ (¬ p3953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41834 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100388 (p2137 p2307 p2737 p2962 p3309 p3549 p3953 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h67266 : (¬ p2737) ∨ (¬ p3549) ∨ (¬ p2962) ∨ (¬ p2137) ∨ (¬ p2307) ∨ (¬ p3953))
    : (¬ p2137) ∨ (¬ p3953) ∨ (¬ p2737) ∨ (¬ p2307) ∨ p3309 ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67266 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step100390 (p2737 p2839 p2946 p3583 p4316 p4790 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h53090 : (¬ p2737) ∨ (¬ p2946) ∨ (¬ p3583) ∨ (¬ p4316) ∨ (¬ p4790))
    : (¬ p2737) ∨ p2839 ∨ (¬ p4790) ∨ (¬ p2946) ∨ (¬ p4316) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53090 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100391 (p2331 p2737 p2829 p3688 p4337 p4790 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h53054 : (¬ p2331) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4337) ∨ (¬ p4790))
    : (¬ p4337) ∨ p2829 ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4337 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53054 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step100393 (p2737 p2811 p3276 p3286 p3506 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h45096 : (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p4425))
    : p3276 ∨ (¬ p2811) ∨ (¬ p3286) ∨ (¬ p2737) ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45096 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100394 (p2737 p2839 p3115 p3583 p4208 p4316 p4322 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73534 : p4208 ∨ p3115)
    (h45289 : (¬ p2737) ∨ (¬ p3583) ∨ (¬ p4208) ∨ (¬ p4316) ∨ (¬ p4322))
    : (¬ p4322) ∨ (¬ p2737) ∨ (¬ p4316) ∨ p2839 ∨ p3115 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45289 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step100395 (p2177 p2553 p2573 p2696 p2737 p3365 p3537 p3873 p4041 p4242 p4963 p5190 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h73390 : p3365 ∨ p2696)
    (h42090 : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4041) ∨ (¬ p4242) ∨ (¬ p4963) ∨ (¬ p5190))
    : p3537 ∨ p2696 ∨ (¬ p3873) ∨ (¬ p4041) ∨ (¬ p2177) ∨ (¬ p2573) ∨ (¬ p5190) ∨ (¬ p2553) ∨ (¬ p4963) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42090 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step100399 (p2992 p3368 p5959 : Prop)
    (h74285 : p2992 ∨ (¬ p5959))
    (h12737 : p3368 ∨ p5959)
    : p3368 ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3368) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5959) := (Or.elim h74285 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12737 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step100401 (p2241 p2247 p2761 p3707 p3830 p4381 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73574 : p4381 ∨ p2761)
    (h54919 : (¬ p2247) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4381))
    : p2241 ∨ (¬ p3830) ∨ (¬ p3707) ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54919 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100402 (p2241 p2247 p3461 p3707 p3830 p4191 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73530 : p4191 ∨ p3461)
    (h64382 : (¬ p2247) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4191))
    : (¬ p3707) ∨ p2241 ∨ p3461 ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64382 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100403 (p2241 p2247 p3276 p3707 p3830 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73226 : p2247 ∨ p2241)
    (h64393 : (¬ p2247) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4425))
    : p3276 ∨ (¬ p3707) ∨ (¬ p3830) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64393 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100404 (p2254 p2417 p2437 p2651 p2657 p3266 p3707 p3742 p3830 p4278 p4444 p4669 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73288 : p2657 ∨ p2651)
    (h73452 : p3742 ∨ p2437)
    (h73546 : p4278 ∨ p2417)
    (h48713 : (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3707) ∨ (¬ p3742) ∨ (¬ p3830) ∨ (¬ p4278) ∨ (¬ p4444) ∨ (¬ p4669))
    : (¬ p3707) ∨ p3266 ∨ (¬ p3830) ∨ p2651 ∨ p2437 ∨ (¬ p2254) ∨ p2417 ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48713 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step100405 (p2608 p3266 p3707 p3830 p3954 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73498 : p3954 ∨ p2608)
    (h43983 : (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3707) ∨ (¬ p3830) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43983 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100408 (p2630 p2810 p3707 p3830 p5170 p5284 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h45835 : (¬ p2810) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p5170) ∨ (¬ p5284))
    : (¬ p3707) ∨ (¬ p5284) ∨ p2630 ∨ (¬ p3830) ∨ (¬ p5170) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45835 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step100414 (p2797 p3707 p3755 p4035 p5284 p5333 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h46488 : (¬ p2797) ∨ (¬ p3707) ∨ (¬ p4035) ∨ (¬ p5284) ∨ (¬ p5333))
    : (¬ p5284) ∨ (¬ p3707) ∨ (¬ p5333) ∨ (¬ p2797) ∨ p3755 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46488 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100415 (p2751 p3707 p3755 p4035 p4759 p5153 p5284 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h41915 : (¬ p2751) ∨ (¬ p3707) ∨ (¬ p4035) ∨ (¬ p4759) ∨ (¬ p5153) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3707) ∨ p3755 ∨ (¬ p2751) ∨ (¬ p4759) ∨ (¬ p5153) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41915 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step100417 (p2249 p3038 p3286 p3292 p3707 p5284 p5363 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h64554 : (¬ p2249) ∨ (¬ p3038) ∨ (¬ p3292) ∨ (¬ p3707) ∨ (¬ p5284) ∨ (¬ p5363))
    : (¬ p5284) ∨ (¬ p3707) ∨ (¬ p5363) ∨ p3286 ∨ (¬ p2249) ∨ (¬ p3038) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64554 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step100424 (p2982 p3707 p3830 p4322 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h46570 : (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4322) ∨ (¬ p4948))
    : (¬ p4322) ∨ (¬ p3707) ∨ (¬ p3830) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46570 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100425 (p2417 p2598 p3055 p3201 p3461 p3707 p3830 p3876 p4191 p4278 p4621 p4736 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73546 : p4278 ∨ p2417)
    (h73350 : p3055 ∨ p2598)
    (h73486 : p3876 ∨ p3201)
    (h63301 : (¬ p3055) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3876) ∨ (¬ p4191) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4736))
    : (¬ p3707) ∨ p3461 ∨ p2417 ∨ p2598 ∨ (¬ p3830) ∨ (¬ p4736) ∨ p3201 ∨ (¬ p4621) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63301 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step100426 (p2252 p2295 p2331 p2608 p2750 p2963 p3568 p3707 p3830 p3954 p4260 p4831 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73498 : p3954 ∨ p2608)
    (h73416 : p3568 ∨ p2295)
    (h63158 : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4260) ∨ (¬ p4831))
    : (¬ p3707) ∨ (¬ p4260) ∨ (¬ p4831) ∨ p2331 ∨ (¬ p3830) ∨ (¬ p2252) ∨ (¬ p2750) ∨ p2608 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u11 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h63158 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step100436 (p2156 p2553 p2588 p2608 p3347 p3646 p3707 p3830 p3904 p3954 p4203 p4260 p4831 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73282 : p2588 ∨ p2553)
    (h73436 : p3646 ∨ p2156)
    (h72227 : (¬ p4260) ∨ (¬ p3954) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4203) ∨ (¬ p2588) ∨ (¬ p3904) ∨ (¬ p4831) ∨ (¬ p3646) ∨ (¬ p3347))
    : (¬ p3830) ∨ p2608 ∨ (¬ p3347) ∨ (¬ p4260) ∨ (¬ p3904) ∨ (¬ p4203) ∨ p2553 ∨ (¬ p3707) ∨ p2156 ∨ (¬ p4831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h72227 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step100439 (p2241 p2247 p3707 p3830 p4314 p5284 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h59491 : (¬ p2247) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4314) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3707) ∨ p2241 ∨ (¬ p3830) ∨ (¬ p4314) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4314 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h59491 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step100445 (p2774 p2780 p2819 p3366 p3379 p3452 p3707 p3830 p4358 p4376 p5123 p5580 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h73394 : p3452 ∨ p3379)
    (h42595 : (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4358) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p3707) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p3366) ∨ p2774 ∨ p2819 ∨ (¬ p3830) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h42595 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step100454 (p3146 p4335 p5995 : Prop)
    (h74329 : p3146 ∨ (¬ p5995))
    (h12959 : p4335 ∨ p5995)
    : p4335 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4335) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5995) := (Or.elim h74329 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12959 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step100455 (p2972 p4942 p5954 : Prop)
    (h74279 : (¬ p2972) ∨ (¬ p5954))
    (h12708 : p4942 ∨ p5954)
    : p4942 ∨ (¬ p2972) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4942) := (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5954) := (Or.elim h74279 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12708 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step100456 (p2860 p4185 p4890 : Prop)
    (h73812 : p4890 ∨ (¬ p2860))
    (h8055 : p4185 ∨ (¬ p4890))
    : p4185 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4185) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4890 := (Or.elim h73812 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h8055 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step100457 (p2860 p3985 p4890 : Prop)
    (h73812 : p4890 ∨ (¬ p2860))
    (h8056 : p3985 ∨ (¬ p4890))
    : p3985 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3985) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4890 := (Or.elim h73812 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h8056 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step100459 (p2860 p4401 p4890 : Prop)
    (h73812 : p4890 ∨ (¬ p2860))
    (h8059 : p4401 ∨ (¬ p4890))
    : p4401 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4401) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4890 := (Or.elim h73812 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h8059 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step100460 (p2331 p2641 p2696 p2745 p2774 p4154 p4582 p4785 : Prop)
    (h73650 : p4582 ∨ (¬ p2331))
    (h73526 : p4154 ∨ p2641)
    (h73758 : p4785 ∨ p2696)
    (h67209 : (¬ p4785) ∨ (¬ p2745) ∨ (¬ p2774) ∨ (¬ p4154) ∨ (¬ p4582))
    : (¬ p2331) ∨ p2641 ∨ (¬ p2745) ∨ (¬ p2774) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4582 := (Or.elim h73650 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4785 := (Or.elim h73758 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67209 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100461 (p2331 p2641 p2651 p2727 p2737 p2740 p2774 p4111 p4154 p4582 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73296 : p2740 ∨ p2737)
    (h73518 : p4111 ∨ p2727)
    (h73650 : p4582 ∨ (¬ p2331))
    (h72231 : (¬ p2774) ∨ (¬ p4154) ∨ (¬ p4111) ∨ (¬ p2740) ∨ (¬ p4582) ∨ (¬ p2651))
    : p2641 ∨ p2737 ∨ (¬ p2774) ∨ p2727 ∨ (¬ p2331) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2740 := (Or.elim h73296 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4582 := (Or.elim h73650 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h72231 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step100463 (p2641 p2748 p2797 p4154 p4195 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73531 : (¬ p2797) ∨ (¬ p4195))
    (h23625 : (¬ p2748) ∨ (¬ p4154) ∨ p4195)
    : p2641 ∨ (¬ p2748) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p4195) := (Or.elim h73531 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h23625 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u4 r1)))))))

theorem step100465 (p2641 p2748 p2797 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h33848 : (¬ p2748) ∨ (¬ p2797) ∨ (¬ p4154))
    : p2641 ∨ (¬ p2797) ∨ (¬ p2748) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h33848 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step100466 (p2641 p2667 p2727 p2946 p2952 p3987 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73330 : p2952 ∨ p2946)
    (h69699 : (¬ p2667) ∨ (¬ p3987) ∨ (¬ p2952) ∨ (¬ p2727) ∨ (¬ p4154))
    : p2641 ∨ p2946 ∨ (¬ p2727) ∨ (¬ p3987) ∨ (¬ p2667) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69699 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100467 (p2641 p2696 p2745 p2774 p3365 p4154 p4328 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73390 : p3365 ∨ p2696)
    (h40925 : (¬ p2745) ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p4154) ∨ (¬ p4328))
    : p2641 ∨ (¬ p4328) ∨ (¬ p2774) ∨ (¬ p2745) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h40925 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step100469 (p2396 p2553 p2578 p2588 p2641 p2667 p2727 p4107 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73514 : p4107 ∨ p2396)
    (h73282 : p2588 ∨ p2553)
    (h47603 : (¬ p2578) ∨ (¬ p2588) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p4107) ∨ (¬ p4154))
    : p2641 ∨ p2396 ∨ (¬ p2727) ∨ p2553 ∨ (¬ p2667) ∨ (¬ p2578) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47603 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step100470 (p2641 p2667 p2727 p3461 p3654 p3946 p4154 p4191 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73530 : p4191 ∨ p3461)
    (h73492 : p3946 ∨ p3654)
    (h43996 : (¬ p2667) ∨ (¬ p2727) ∨ (¬ p3946) ∨ (¬ p4154) ∨ (¬ p4191))
    : p2641 ∨ p3461 ∨ p3654 ∨ (¬ p2667) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43996 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step100471 (p2331 p2641 p2811 p3461 p3755 p4035 p4154 p4190 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73526 : p4154 ∨ p2641)
    (h73506 : p4035 ∨ p3755)
    (h43409 : (¬ p2331) ∨ (¬ p2811) ∨ (¬ p4035) ∨ (¬ p4154) ∨ (¬ p4190) ∨ (¬ p4191))
    : p3461 ∨ (¬ p2811) ∨ (¬ p2331) ∨ (¬ p4190) ∨ p2641 ∨ p3755 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h43409 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step100473 (p2608 p2641 p2727 p2829 p4154 p4328 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h45712 : (¬ p2608) ∨ (¬ p2727) ∨ (¬ p2829) ∨ (¬ p4154) ∨ (¬ p4328))
    : p2641 ∨ (¬ p2829) ∨ (¬ p2608) ∨ (¬ p4328) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45712 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100481 (p2641 p2727 p3016 p4154 p4976 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h51553 : (¬ p2727) ∨ (¬ p3016) ∨ (¬ p4154) ∨ (¬ p4976))
    : p2641 ∨ (¬ p3016) ∨ (¬ p4976) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51553 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step100482 (p2341 p2459 p2641 p2696 p2707 p2748 p3323 p3365 p3577 p4037 p4154 p4604 p4734 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73508 : p4037 ∨ p3323)
    (h72735 : p4734)
    (h73526 : p4154 ∨ p2641)
    (h60703 : (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2707) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3577) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4604) ∨ (¬ p4734))
    : (¬ p3577) ∨ p2696 ∨ (¬ p2341) ∨ p3323 ∨ (¬ p2459) ∨ (¬ p2748) ∨ (¬ p4604) ∨ (¬ p2707) ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4734 := h72735;
    let u12 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h60703 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u11)))))))))))))))))))))

theorem step100484 (p2641 p2651 p2946 p2952 p2992 p4154 p4972 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73330 : p2952 ∨ p2946)
    (h52982 : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4154) ∨ (¬ p4972))
    : p2641 ∨ (¬ p2992) ∨ (¬ p4972) ∨ (¬ p2651) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52982 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100486 (p2295 p2641 p2946 p2952 p2992 p3568 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73416 : p3568 ∨ p2295)
    (h73330 : p2952 ∨ p2946)
    (h44961 : (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3568) ∨ (¬ p4154))
    : p2641 ∨ (¬ p2992) ∨ p2295 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44961 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100487 (p2187 p2641 p2946 p2952 p2992 p3745 p3989 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73502 : p3989 ∨ p2187)
    (h73330 : p2952 ∨ p2946)
    (h44978 : (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p3989) ∨ (¬ p4154))
    : p2641 ∨ (¬ p2992) ∨ (¬ p3745) ∨ p2187 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44978 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100493 (p2255 p2641 p2958 p2962 p3323 p3654 p4037 p4154 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73526 : p4154 ∨ p2641)
    (h48369 : (¬ p2255) ∨ (¬ p2958) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p4037) ∨ (¬ p4154))
    : (¬ p3654) ∨ p3323 ∨ (¬ p2958) ∨ (¬ p2962) ∨ (¬ p2255) ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48369 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step100498 (p2230 p2246 p2373 p2641 p3323 p3366 p3461 p3519 p3969 p4037 p4154 p4191 p4236 p4376 p5119 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73530 : p4191 ∨ p3461)
    (h73508 : p4037 ∨ p3323)
    (h62984 : (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2373) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3969) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4191) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5119))
    : (¬ p3969) ∨ p2641 ∨ (¬ p5119) ∨ (¬ p4236) ∨ (¬ p3519) ∨ p3461 ∨ (¬ p2246) ∨ (¬ p2230) ∨ (¬ p3366) ∨ (¬ p2373) ∨ p3323 ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u14 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h62984 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u14))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (False.elim (r10 u2)))))))))))))))))))))))))

theorem step100504 (p2230 p2241 p2247 p2427 p3189 p3246 p3256 p3950 p4118 p4360 p5190 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73226 : p2247 ∨ p2241)
    (h73520 : p4118 ∨ p3256)
    (h42127 : (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p5190))
    : p3189 ∨ p2241 ∨ (¬ p2427) ∨ p3256 ∨ (¬ p3950) ∨ (¬ p3246) ∨ (¬ p5190) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42127 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step100506 (p2241 p2247 p2363 p3189 p3256 p4118 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73226 : p2247 ∨ p2241)
    (h73520 : p4118 ∨ p3256)
    (h46127 : (¬ p2247) ∨ (¬ p2363) ∨ (¬ p4118) ∨ (¬ p4360))
    : p3189 ∨ p2241 ∨ p3256 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46127 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100508 (p2241 p2247 p2459 p3189 p3256 p4118 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73226 : p2247 ∨ p2241)
    (h73520 : p4118 ∨ p3256)
    (h47732 : (¬ p2247) ∨ (¬ p2459) ∨ (¬ p4118) ∨ (¬ p4360))
    : p3189 ∨ p2241 ∨ p3256 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47732 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100510 (p2331 p2727 p2963 p3166 p3189 p4360 p4972 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73566 : p4360 ∨ p3189)
    (h62912 : (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p4360) ∨ (¬ p4972))
    : p2331 ∨ (¬ p3166) ∨ (¬ p4972) ∨ (¬ p2727) ∨ p3189 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62912 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100513 (p2241 p2247 p2396 p2553 p2573 p3189 p3256 p3950 p4118 p4360 p5190 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73226 : p2247 ∨ p2241)
    (h73520 : p4118 ∨ p3256)
    (h42119 : (¬ p2247) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p5190))
    : p3189 ∨ p2241 ∨ (¬ p3950) ∨ (¬ p5190) ∨ (¬ p2573) ∨ (¬ p2553) ∨ (¬ p2396) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42119 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step100515 (p2241 p2247 p3146 p3189 p3256 p4118 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73226 : p2247 ∨ p2241)
    (h73520 : p4118 ∨ p3256)
    (h44127 : (¬ p2247) ∨ (¬ p3146) ∨ (¬ p4118) ∨ (¬ p4360))
    : p3189 ∨ p2241 ∨ (¬ p3146) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44127 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100516 (p2727 p2946 p2952 p3166 p3189 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73330 : p2952 ∨ p2946)
    (h69700 : (¬ p3166) ∨ (¬ p4360) ∨ (¬ p2952) ∨ (¬ p2727))
    : p3189 ∨ p2946 ∨ (¬ p3166) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69700 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step100518 (p2156 p2241 p2247 p2352 p3096 p3189 p3256 p3979 p4118 p4360 p4521 p5122 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73520 : p4118 ∨ p3256)
    (h73226 : p2247 ∨ p2241)
    (h62266 : (¬ p2156) ∨ (¬ p2247) ∨ (¬ p2352) ∨ (¬ p3096) ∨ (¬ p3979) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4521) ∨ (¬ p5122))
    : p3189 ∨ (¬ p2352) ∨ (¬ p5122) ∨ p3256 ∨ (¬ p3979) ∨ (¬ p4521) ∨ (¬ p2156) ∨ (¬ p3096) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h62266 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step100523 (p2946 p2952 p2992 p3189 p3256 p4118 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73330 : p2952 ∨ p2946)
    (h73520 : p4118 ∨ p3256)
    (h46234 : (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4118) ∨ (¬ p4360))
    : p3189 ∨ (¬ p2992) ∨ p2946 ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46234 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100535 (p2241 p2247 p3189 p3256 p3266 p4118 p4360 p4444 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73226 : p2247 ∨ p2241)
    (h73520 : p4118 ∨ p3256)
    (h73580 : p4444 ∨ p3266)
    (h43941 : (¬ p2247) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4444))
    : p3189 ∨ p2241 ∨ p3256 ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43941 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u7)))))))))

theorem step100536 (p2696 p2992 p3166 p3189 p3365 p4117 p4360 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73566 : p4360 ∨ p3189)
    (h44360 : (¬ p2992) ∨ (¬ p3166) ∨ (¬ p3365) ∨ (¬ p4117) ∨ (¬ p4360))
    : (¬ p4117) ∨ (¬ p3166) ∨ (¬ p2992) ∨ p2696 ∨ p3189 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4117 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44360 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step100538 (p2352 p2641 p3177 p3189 p4170 p4360 p4973 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h55405 : (¬ p2352) ∨ (¬ p2641) ∨ (¬ p3177) ∨ (¬ p4170) ∨ (¬ p4360) ∨ (¬ p4973))
    : p3189 ∨ (¬ p2352) ∨ (¬ p4973) ∨ (¬ p2641) ∨ (¬ p4170) ∨ (¬ p3177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55405 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step100540 (p2132 p2245 p2331 p2641 p2870 p2881 p2963 p3189 p4041 p4360 p4733 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73566 : p4360 ∨ p3189)
    (h62244 : (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2641) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2963) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4733))
    : (¬ p2641) ∨ p2331 ∨ (¬ p2881) ∨ (¬ p4041) ∨ (¬ p4733) ∨ (¬ p2245) ∨ p3189 ∨ (¬ p2870) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62244 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step100544 (p2331 p2641 p2963 p3189 p3256 p4118 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73520 : p4118 ∨ p3256)
    (h73338 : p2963 ∨ p2331)
    (h42716 : (¬ p2641) ∨ (¬ p2963) ∨ (¬ p4118) ∨ (¬ p4360))
    : p3189 ∨ p3256 ∨ p2331 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42716 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100548 (p2088 p2255 p3189 p3256 p3987 p4114 p4118 p4360 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73566 : p4360 ∨ p3189)
    (h48499 : (¬ p2088) ∨ (¬ p2255) ∨ (¬ p3987) ∨ (¬ p4114) ∨ (¬ p4118) ∨ (¬ p4360))
    : (¬ p4114) ∨ p3256 ∨ (¬ p3987) ∨ (¬ p2255) ∨ p3189 ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4114 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48499 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step100549 (p2088 p2255 p3189 p3256 p4104 p4118 p4360 p4590 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73520 : p4118 ∨ p3256)
    (h48842 : (¬ p2088) ∨ (¬ p2255) ∨ (¬ p4104) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4590))
    : p3189 ∨ p3256 ∨ (¬ p4590) ∨ (¬ p2088) ∨ (¬ p4104) ∨ (¬ p2255) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48842 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step100553 (p2641 p4245 p4755 : Prop)
    (h73744 : p4755 ∨ p2641)
    (h7731 : p4245 ∨ (¬ p4755))
    : p4245 ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4245) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr h));
    let u2 : p4755 := (Or.elim h73744 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7731 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step100554 (p2641 p4245 p5893 : Prop)
    (h74197 : p2641 ∨ (¬ p5893))
    (h12343 : p4245 ∨ p5893)
    : p4245 ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4245) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5893) := (Or.elim h74197 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12343 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step100555 (p2630 p4748 p4749 : Prop)
    (h73740 : p4748 ∨ p2630)
    (h7716 : (¬ p4748) ∨ p4749)
    : p2630 ∨ p4749 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4749) := (fun h => hn (Or.inr h));
    let u2 : p4748 := (Or.elim h73740 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7716 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100556 (p2630 p4748 p4750 : Prop)
    (h73740 : p4748 ∨ p2630)
    (h7717 : (¬ p4748) ∨ p4750)
    : p2630 ∨ p4750 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4750) := (fun h => hn (Or.inr h));
    let u2 : p4748 := (Or.elim h73740 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7717 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100557 (p2630 p2810 p4845 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h47180 : (¬ p2810) ∨ p4845)
    : p2630 ∨ p4845 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4845) := (fun h => hn (Or.inr h));
    let u2 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47180 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100560 (p2230 p2427 p2589 p2630 p2662 p2810 p2881 p3570 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73316 : p2810 ∨ p2630)
    (h73284 : p2589 ∨ p2230)
    (h73418 : p3570 ∨ p2881)
    (h43999 : (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3570) ∨ (¬ p4235))
    : p2427 ∨ p2630 ∨ (¬ p2662) ∨ p2230 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43999 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step100563 (p2352 p2630 p2651 p2797 p2810 p3984 p4117 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h46487 : (¬ p2352) ∨ (¬ p2651) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3984) ∨ (¬ p4117))
    : (¬ p2352) ∨ (¬ p3984) ∨ p2630 ∨ (¬ p2797) ∨ (¬ p2651) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46487 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step100564 (p2630 p2651 p2810 p3286 p3292 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h73316 : p2810 ∨ p2630)
    (h58777 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3292) ∨ (¬ p5284))
    : p3286 ∨ (¬ p5284) ∨ p2630 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58777 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step100565 (p2630 p2651 p2737 p2743 p2810 p4117 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73316 : p2810 ∨ p2630)
    (h72236 : (¬ p2810) ∨ (¬ p2743) ∨ (¬ p2651) ∨ (¬ p4117))
    : (¬ p2651) ∨ p2737 ∨ p2630 ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72236 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step100569 (p2284 p2630 p2651 p2810 p2946 p2952 p3952 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73316 : p2810 ∨ p2630)
    (h73496 : p3952 ∨ p2284)
    (h64204 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2952) ∨ (¬ p3952))
    : p2946 ∨ (¬ p2651) ∨ p2630 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64204 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step100570 (p2528 p2534 p2630 p2651 p2810 p3166 p3172 p4437 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73356 : p3172 ∨ p3166)
    (h73316 : p2810 ∨ p2630)
    (h54918 : (¬ p2534) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3172) ∨ (¬ p4437))
    : p2528 ∨ p3166 ∨ (¬ p2651) ∨ (¬ p4437) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54918 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100573 (p2598 p2630 p2727 p2749 p2751 p2810 p3055 p4343 p4734 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73316 : p2810 ∨ p2630)
    (h72735 : p4734)
    (h66848 : (¬ p2727) ∨ (¬ p2751) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p4343) ∨ (¬ p3055) ∨ (¬ p4734))
    : (¬ p2751) ∨ (¬ p2727) ∨ p2598 ∨ (¬ p4343) ∨ p2630 ∨ (¬ p2749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p4734 := h72735;
    (Or.elim h66848 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u8)))))))))))))))

theorem step100576 (p2630 p2651 p2810 p3276 p3286 p3292 p4425 p5171 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h73578 : p4425 ∨ p3276)
    (h73316 : p2810 ∨ p2630)
    (h46018 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3292) ∨ (¬ p4425) ∨ (¬ p5171))
    : p3286 ∨ p3276 ∨ p2630 ∨ (¬ p2651) ∨ (¬ p5171) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46018 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step100578 (p2363 p2528 p2534 p2630 p2810 p3083 p4256 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h73316 : p2810 ∨ p2630)
    (h62316 : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2810) ∨ (¬ p4256))
    : p2528 ∨ p3083 ∨ (¬ p2363) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62316 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100580 (p2331 p2630 p2651 p2668 p2810 p2963 p3324 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73386 : p3324 ∨ p2668)
    (h73316 : p2810 ∨ p2630)
    (h54737 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3324))
    : p2331 ∨ (¬ p2651) ∨ p2668 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54737 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100581 (p2295 p2331 p2630 p2651 p2810 p2963 p3568 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73316 : p2810 ∨ p2630)
    (h73416 : p3568 ∨ p2295)
    (h60666 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3568))
    : p2331 ∨ (¬ p2651) ∨ p2630 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60666 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step100587 (p2331 p2553 p2588 p2630 p2651 p2810 p2963 p4389 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73316 : p2810 ∨ p2630)
    (h73282 : p2588 ∨ p2553)
    (h60671 : (¬ p2588) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p4389))
    : p2331 ∨ (¬ p2651) ∨ (¬ p4389) ∨ p2630 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60671 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100589 (p2187 p2230 p2563 p2589 p2630 p2662 p2810 p3989 p4110 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73502 : p3989 ∨ p2187)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h56583 : (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3989) ∨ (¬ p4110))
    : p2630 ∨ (¬ p2662) ∨ p2187 ∨ p2563 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56583 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step100592 (p2553 p2577 p2588 p2630 p2662 p2810 p3564 p3654 p3946 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h73282 : p2588 ∨ p2553)
    (h73316 : p2810 ∨ p2630)
    (h45374 : (¬ p2577) ∨ (¬ p2588) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3564) ∨ (¬ p3946))
    : (¬ p3564) ∨ p3654 ∨ p2553 ∨ (¬ p2662) ∨ (¬ p2577) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h45374 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step100594 (p2177 p2299 p2553 p2588 p2630 p2810 p3016 p3574 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73282 : p2588 ∨ p2553)
    (h73316 : p2810 ∨ p2630)
    (h73234 : p2299 ∨ p2177)
    (h43874 : (¬ p2299) ∨ (¬ p2588) ∨ (¬ p2810) ∨ (¬ p3574))
    : p3016 ∨ p2553 ∨ p2630 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43874 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100595 (p2307 p2630 p2797 p2810 p3309 p3549 p3567 p3953 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h73316 : p2810 ∨ p2630)
    (h43170 : (¬ p2307) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p3953))
    : (¬ p2307) ∨ (¬ p3567) ∨ (¬ p3953) ∨ p3309 ∨ (¬ p2797) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h43170 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step100600 (p2528 p2630 p2810 p3005 p3146 p3692 p4346 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73448 : p3692 ∨ p3146)
    (h43408 : (¬ p2528) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3692) ∨ (¬ p4346))
    : (¬ p3005) ∨ (¬ p4346) ∨ p2630 ∨ p3146 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43408 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step100601 (p2630 p2810 p2870 p2957 p3051 p3556 p4313 p4704 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73046 : p4704)
    (h73316 : p2810 ∨ p2630)
    (h52043 : (¬ p2810) ∨ (¬ p2870) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4313) ∨ (¬ p4704))
    : (¬ p2957) ∨ (¬ p4313) ∨ (¬ p2870) ∨ p3051 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4704 := h73046;
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52043 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step100614 (p3093 p5019 p5020 : Prop)
    (h73878 : p5019 ∨ (¬ p3093))
    (h8391 : (¬ p5019) ∨ p5020)
    : (¬ p3093) ∨ p5020 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5020) := (fun h => hn (Or.inr h));
    let u2 : p5019 := (Or.elim h73878 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8391 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100615 (p3093 p5019 p5021 : Prop)
    (h73878 : p5019 ∨ (¬ p3093))
    (h8393 : (¬ p5019) ∨ p5021)
    : (¬ p3093) ∨ p5021 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5021) := (fun h => hn (Or.inr h));
    let u2 : p5019 := (Or.elim h73878 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8393 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100616 (p3093 p5019 p5022 : Prop)
    (h73878 : p5019 ∨ (¬ p3093))
    (h8394 : (¬ p5019) ∨ p5022)
    : (¬ p3093) ∨ p5022 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5022) := (fun h => hn (Or.inr h));
    let u2 : p5019 := (Or.elim h73878 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8394 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100625 (p2608 p2737 p2743 p2797 p3093 p3954 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73298 : p2743 ∨ p2737)
    (h73498 : p3954 ∨ p2608)
    (h48424 : (¬ p2743) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p4195))
    : p2797 ∨ p2737 ∨ (¬ p3093) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48424 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100626 (p2187 p2210 p2295 p2696 p2797 p3093 p3365 p3366 p3555 p3568 p4195 p4377 p4405 p4516 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73412 : p3555 ∨ p2210)
    (h73416 : p3568 ∨ p2295)
    (h73390 : p3365 ∨ p2696)
    (h41977 : (¬ p2187) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3555) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4377) ∨ (¬ p4405) ∨ (¬ p4516))
    : p2797 ∨ p2210 ∨ (¬ p4405) ∨ p2295 ∨ (¬ p2187) ∨ (¬ p4377) ∨ (¬ p3366) ∨ (¬ p3093) ∨ p2696 ∨ (¬ p4516) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h41977 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step100627 (p2136 p2220 p2241 p2247 p2459 p2744 p3063 p3093 p3146 p3366 p3692 p4120 p4133 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73522 : p4120 ∨ p2220)
    (h73226 : p2247 ∨ p2241)
    (h52889 : (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4133))
    : (¬ p3063) ∨ p3146 ∨ (¬ p2459) ∨ (¬ p3366) ∨ p2220 ∨ (¬ p4133) ∨ (¬ p2136) ∨ (¬ p3093) ∨ (¬ p2744) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h52889 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step100629 (p2264 p2685 p2696 p3063 p3093 p3365 p3366 p3379 p3452 p3553 p3572 p4133 p4376 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h73410 : p3553 ∨ p2264)
    (h73394 : p3452 ∨ p3379)
    (h73390 : p3365 ∨ p2696)
    (h58328 : (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4133) ∨ (¬ p4376))
    : (¬ p3063) ∨ p2685 ∨ p2264 ∨ p3379 ∨ (¬ p4376) ∨ p2696 ∨ (¬ p3366) ∨ (¬ p4133) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58328 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step100633 (p2230 p2427 p2589 p2608 p3093 p3246 p3319 p3347 p3690 p3954 p4235 p4621 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73536 : p4235 ∨ p2427)
    (h73284 : p2589 ∨ p2230)
    (h73446 : p3690 ∨ p3246)
    (h72239 : (¬ p3690) ∨ (¬ p4621) ∨ (¬ p3347) ∨ (¬ p4235) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p2589) ∨ (¬ p3954))
    : p2608 ∨ (¬ p3319) ∨ (¬ p4621) ∨ p2427 ∨ (¬ p3347) ∨ (¬ p3093) ∨ p2230 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h72239 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step100634 (p2254 p2363 p2901 p2946 p2952 p3063 p3093 p3246 p3690 p4320 p4669 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73330 : p2952 ∨ p2946)
    (h73446 : p3690 ∨ p3246)
    (h58176 : (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4669))
    : (¬ p3063) ∨ p2901 ∨ p2946 ∨ p3246 ∨ (¬ p2363) ∨ (¬ p3093) ∨ (¬ p4669) ∨ (¬ p2254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58176 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step100635 (p2363 p3063 p3093 p3276 p3346 p3680 p4425 p5059 p5193 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h59960 : (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3346) ∨ (¬ p3680) ∨ (¬ p4425) ∨ (¬ p5059) ∨ (¬ p5193))
    : p3276 ∨ (¬ p3063) ∨ (¬ p3680) ∨ (¬ p5193) ∨ (¬ p3346) ∨ (¬ p3093) ∨ (¬ p5059) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h59960 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step100636 (p3093 p3399 p4053 p4366 p4427 p5477 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h42152 : (¬ p3093) ∨ (¬ p4053) ∨ (¬ p4366) ∨ (¬ p4427) ∨ (¬ p5477))
    : (¬ p4053) ∨ p3399 ∨ (¬ p4427) ∨ (¬ p3093) ∨ (¬ p5477) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4053 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42152 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step100642 (p2737 p2750 p2752 : Prop)
    (h73303 : (¬ p2737) ∨ (¬ p2752))
    (h3627 : p2750 ∨ p2752)
    : p2750 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2750) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2752) := (Or.elim h73303 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3627 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step100644 (p3125 p5042 p5043 : Prop)
    (h73888 : p5042 ∨ p3125)
    (h8440 : (¬ p5042) ∨ p5043)
    : p3125 ∨ p5043 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5043) := (fun h => hn (Or.inr h));
    let u2 : p5042 := (Or.elim h73888 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8440 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100646 (p3319 p4430 p6025 : Prop)
    (h74365 : p3319 ∨ (¬ p6025))
    (h13146 : p4430 ∨ p6025)
    : p4430 ∨ p3319 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4430) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6025) := (Or.elim h74365 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13146 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step100647 (p2363 p3654 p3946 p4330 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h51576 : (¬ p2363) ∨ (¬ p3946) ∨ p4330)
    : p4330 ∨ p3654 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4330) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51576 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u0 r1)))))))

theorem step100649 (p3136 p4906 p5048 : Prop)
    (h73892 : p5048 ∨ p3136)
    (h8458 : p4906 ∨ (¬ p5048))
    : p4906 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4906) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3136) := (fun h => hn (Or.inr h));
    let u2 : p5048 := (Or.elim h73892 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h8458 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step100651 (p2284 p2608 p2696 p2839 p3136 p3365 p3583 p3952 p3954 p4315 p4316 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73496 : p3952 ∨ p2284)
    (h73424 : p3583 ∨ p2839)
    (h73390 : p3365 ∨ p2696)
    (h73550 : p4315 ∨ p3136)
    (h65977 : (¬ p3952) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p4316) ∨ (¬ p3583) ∨ (¬ p3954))
    : p2608 ∨ p2284 ∨ p2839 ∨ p2696 ∨ p3136 ∨ (¬ p4316) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h65977 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step100652 (p2870 p2901 p4316 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h19830 : (¬ p2870) ∨ (¬ p4316) ∨ (¬ p4320))
    : p2901 ∨ (¬ p4316) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h19830 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step100654 (p2619 p3156 p3497 p3694 p4316 : Prop)
    (h73449 : (¬ p2619) ∨ (¬ p3694))
    (h73400 : p3497 ∨ p3156)
    (h6537 : (¬ p3497) ∨ p3694 ∨ (¬ p4316))
    : (¬ p2619) ∨ p3156 ∨ (¬ p4316) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3694) := (Or.elim h73449 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h6537 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step100657 (p2284 p3105 p3564 p3952 p3958 p4137 p4316 p4388 p5152 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73496 : p3952 ∨ p2284)
    (h58458 : (¬ p3105) ∨ (¬ p3952) ∨ (¬ p3958) ∨ (¬ p4137) ∨ (¬ p4316) ∨ (¬ p4388) ∨ (¬ p5152))
    : (¬ p5152) ∨ p3564 ∨ (¬ p3958) ∨ p2284 ∨ (¬ p4316) ∨ (¬ p3105) ∨ (¬ p4388) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5152 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4388 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58458 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step100669 (p2696 p4790 p5903 : Prop)
    (h74211 : (¬ p2696) ∨ (¬ p5903))
    (h12402 : p4790 ∨ p5903)
    : p4790 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4790) := (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5903) := (Or.elim h74211 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12402 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step100671 (p2696 p2870 p3051 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h67359 : (¬ p2696) ∨ (¬ p2870) ∨ (¬ p3556))
    : (¬ p2870) ∨ p3051 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67359 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step100676 (p2098 p2104 p2696 p3266 p3609 p4340 p4444 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73204 : p2104 ∨ p2098)
    (h73580 : p4444 ∨ p3266)
    (h55879 : (¬ p2104) ∨ (¬ p2696) ∨ (¬ p4340) ∨ (¬ p4444))
    : p3609 ∨ p2098 ∨ p3266 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55879 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step100677 (p2098 p2104 p2363 p2696 p3609 p4340 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73204 : p2104 ∨ p2098)
    (h43344 : (¬ p2104) ∨ (¬ p2363) ∨ (¬ p2696) ∨ (¬ p4340))
    : p3609 ∨ p2098 ∨ (¬ p2696) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43344 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step100681 (p2685 p2696 p2753 p3367 p3585 p4343 p4652 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h42062 : (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4652))
    : (¬ p2753) ∨ p3367 ∨ (¬ p4343) ∨ (¬ p2696) ∨ (¬ p2685) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42062 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step100682 (p2459 p2696 p3115 p3136 p3399 p3527 p3548 p4348 p4366 p4450 p4733 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73562 : p4348 ∨ p2459)
    (h73404 : p3548 ∨ p3527)
    (h56435 : (¬ p2696) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4450) ∨ (¬ p4733))
    : (¬ p3115) ∨ p3399 ∨ (¬ p3136) ∨ (¬ p4450) ∨ (¬ p4733) ∨ p2459 ∨ (¬ p2696) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h56435 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step100685 (p2696 p2761 p3425 p3434 p4324 p4381 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h73574 : p4381 ∨ p2761)
    (h62659 : (¬ p2696) ∨ (¬ p3425) ∨ (¬ p4324) ∨ (¬ p4381))
    : p3434 ∨ (¬ p3425) ∨ p2761 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62659 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100686 (p2437 p2598 p2696 p2911 p3055 p3644 p3742 p4343 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73434 : p3644 ∨ p2911)
    (h73350 : p3055 ∨ p2598)
    (h51230 : (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4343))
    : p2437 ∨ p2911 ∨ (¬ p4343) ∨ p2598 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51230 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100689 (p2470 p2476 p2528 p2534 p2696 p2753 p2797 p3266 p3347 p4228 p4444 p5250 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73268 : p2534 ∨ p2528)
    (h73580 : p4444 ∨ p3266)
    (h72244 : (¬ p4228) ∨ (¬ p5250) ∨ (¬ p2476) ∨ (¬ p2753) ∨ (¬ p4444) ∨ (¬ p3347) ∨ (¬ p2797) ∨ (¬ p2696) ∨ (¬ p2534))
    : (¬ p4228) ∨ (¬ p2753) ∨ p2470 ∨ p2528 ∨ (¬ p2797) ∨ (¬ p5250) ∨ p3266 ∨ (¬ p3347) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h72244 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u10)))))))))))))))))))

theorem step100693 (p2363 p2383 p2387 p2696 p2787 p3136 p3266 p4272 p4347 p4444 p5400 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73560 : p4347 ∨ p2363)
    (h73246 : p2387 ∨ p2383)
    (h48725 : (¬ p2387) ∨ (¬ p2696) ∨ (¬ p2787) ∨ (¬ p3136) ∨ (¬ p4272) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p5400))
    : (¬ p4272) ∨ p3266 ∨ (¬ p5400) ∨ (¬ p2787) ∨ (¬ p3136) ∨ (¬ p2696) ∨ p2363 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4272 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h48725 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step100697 (p2098 p2104 p2696 p2751 p3189 p4963 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h41438 : (¬ p2104) ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p3189) ∨ (¬ p4963))
    : p2098 ∨ (¬ p3189) ∨ (¬ p4963) ∨ (¬ p2751) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41438 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100698 (p2156 p2553 p2696 p2753 p3096 p3519 p3590 p3599 p3670 p3791 p4379 p4399 p4749 p4826 p5387 : Prop)
    (h73572 : p4379 ∨ p3599)
    (h74026 : p5387 ∨ p3670)
    (h42247 : (¬ p2156) ∨ (¬ p2553) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3096) ∨ (¬ p3519) ∨ (¬ p3590) ∨ (¬ p3791) ∨ (¬ p4379) ∨ (¬ p4399) ∨ (¬ p4749) ∨ (¬ p4826) ∨ (¬ p5387))
    : p3599 ∨ (¬ p2753) ∨ (¬ p2553) ∨ (¬ p3519) ∨ (¬ p3096) ∨ (¬ p4399) ∨ (¬ p2696) ∨ (¬ p3590) ∨ (¬ p2156) ∨ (¬ p4826) ∨ p3670 ∨ (¬ p3791) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u14 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h42247 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u12))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u9))) (fun r11 => (False.elim (r11 u14)))))))))))))))))))))))))))

theorem step100703 (p2440 p2542 p2630 p2685 p2807 p3572 p4117 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73420 : p3572 ∨ p2685)
    (h47421 : (¬ p2542) ∨ (¬ p2630) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p4117))
    : p2440 ∨ (¬ p2630) ∨ (¬ p2807) ∨ (¬ p4117) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47421 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100708 (p2449 p2807 p3527 p3631 p3817 p4117 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h57233 : (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3527) ∨ (¬ p3817) ∨ (¬ p4117))
    : p3631 ∨ (¬ p3527) ∨ (¬ p4117) ∨ (¬ p2449) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h57233 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100709 (p2098 p2104 p2264 p2807 p4117 p4807 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h54740 : (¬ p2104) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p4117) ∨ (¬ p4807))
    : p2098 ∨ (¬ p4807) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p4807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h54740 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step100713 (p2274 p2797 p2946 p3136 p3986 p4117 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h43223 : (¬ p2274) ∨ (¬ p2797) ∨ (¬ p2946) ∨ (¬ p3986) ∨ (¬ p4117) ∨ (¬ p4315))
    : (¬ p2274) ∨ (¬ p2797) ∨ (¬ p2946) ∨ p3136 ∨ (¬ p3986) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43223 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step100716 (p2088 p2098 p2104 p3178 p3256 p4117 p4118 p4969 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h73520 : p4118 ∨ p3256)
    (h58420 : (¬ p2088) ∨ (¬ p2104) ∨ (¬ p3178) ∨ (¬ p4117) ∨ (¬ p4118) ∨ (¬ p4969))
    : (¬ p4969) ∨ p2098 ∨ (¬ p3178) ∨ p3256 ∨ (¬ p4117) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3178 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58420 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step100724 (p2331 p2598 p2797 p3055 p4117 p4195 p4749 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73350 : p3055 ∨ p2598)
    (h62487 : (¬ p2331) ∨ (¬ p3055) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4749))
    : p2797 ∨ (¬ p2331) ∨ (¬ p4749) ∨ p2598 ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62487 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100727 (p2598 p2946 p3055 p3136 p4117 p4315 p4749 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73350 : p3055 ∨ p2598)
    (h41280 : (¬ p2946) ∨ (¬ p3055) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4749))
    : p3136 ∨ (¬ p2946) ∨ p2598 ∨ (¬ p4117) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41280 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step100728 (p2598 p2685 p2807 p3055 p3572 p4117 p4749 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h73350 : p3055 ∨ p2598)
    (h42133 : (¬ p2807) ∨ (¬ p3055) ∨ (¬ p3572) ∨ (¬ p4117) ∨ (¬ p4749))
    : p2685 ∨ p2598 ∨ (¬ p4749) ∨ (¬ p2807) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42133 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100735 (p2651 p2696 p2797 p3365 p4117 p4195 p4972 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73390 : p3365 ∨ p2696)
    (h52711 : (¬ p2651) ∨ (¬ p3365) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4972))
    : p2797 ∨ p2696 ∨ (¬ p4117) ∨ (¬ p4972) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52711 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100739 (p2132 p2138 p2331 p2797 p4117 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73214 : p2138 ∨ p2132)
    (h67259 : (¬ p4195) ∨ (¬ p4117) ∨ (¬ p2331) ∨ (¬ p2138))
    : p2797 ∨ (¬ p2331) ∨ (¬ p4117) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67259 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100740 (p2274 p2331 p2685 p2797 p3097 p3552 p4117 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73352 : p3097 ∨ p2274)
    (h53975 : (¬ p2331) ∨ (¬ p2685) ∨ (¬ p3097) ∨ (¬ p3552) ∨ (¬ p4117) ∨ (¬ p4195))
    : p2797 ∨ p2274 ∨ (¬ p2685) ∨ (¬ p2331) ∨ (¬ p4117) ∨ (¬ p3552) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53975 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step100741 (p2230 p2331 p2427 p2589 p3246 p3461 p3506 p3690 p4117 p4191 p4235 p4421 p4621 p4729 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73284 : p2589 ∨ p2230)
    (h73446 : p3690 ∨ p3246)
    (h73536 : p4235 ∨ p2427)
    (h54322 : (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3506) ∨ (¬ p3690) ∨ (¬ p4117) ∨ (¬ p4191) ∨ (¬ p4235) ∨ (¬ p4421) ∨ (¬ p4621) ∨ (¬ p4729))
    : (¬ p3506) ∨ p3461 ∨ p2230 ∨ (¬ p4621) ∨ p3246 ∨ (¬ p4729) ∨ p2427 ∨ (¬ p4117) ∨ (¬ p2331) ∨ (¬ p4421) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h54322 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step100742 (p2753 p2761 p2807 p3093 p3319 p3379 p3506 p3591 p4026 p4117 p4381 p4625 p4661 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73432 : p3591 ∨ p3093)
    (h73504 : p4026 ∨ p3319)
    (h72251 : (¬ p4026) ∨ (¬ p3506) ∨ (¬ p2807) ∨ (¬ p3379) ∨ (¬ p4661) ∨ (¬ p3591) ∨ (¬ p4381) ∨ (¬ p4625) ∨ (¬ p2753) ∨ (¬ p4117))
    : (¬ p2753) ∨ p2761 ∨ (¬ p2807) ∨ (¬ p3506) ∨ (¬ p3379) ∨ p3093 ∨ (¬ p4117) ∨ (¬ p4625) ∨ p3319 ∨ (¬ p4661) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h72251 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step100743 (p2373 p2427 p2753 p3051 p3166 p3347 p3556 p3880 p3904 p4009 p4117 p4134 p5580 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73414 : p3556 ∨ p3051)
    (h72252 : (¬ p4009) ∨ (¬ p3347) ∨ (¬ p3880) ∨ (¬ p2427) ∨ (¬ p5580) ∨ (¬ p3166) ∨ (¬ p4117) ∨ (¬ p2753) ∨ (¬ p3904) ∨ (¬ p3556) ∨ (¬ p4134))
    : (¬ p4009) ∨ (¬ p2753) ∨ p2373 ∨ (¬ p5580) ∨ (¬ p3347) ∨ (¬ p2427) ∨ (¬ p4117) ∨ (¬ p3166) ∨ (¬ p3904) ∨ p3051 ∨ (¬ p4134) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h72252 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step100750 (p2737 p2743 p2946 p3136 p4117 p4315 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73550 : p4315 ∨ p3136)
    (h72253 : (¬ p2946) ∨ (¬ p2743) ∨ (¬ p4117) ∨ (¬ p4315))
    : (¬ p2946) ∨ p2737 ∨ p3136 ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72253 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100753 (p2737 p2743 p3005 p3166 p3877 p4117 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73298 : p2743 ∨ p2737)
    (h72256 : (¬ p3877) ∨ (¬ p2743) ∨ (¬ p3166) ∨ (¬ p4117))
    : p3005 ∨ (¬ p3166) ∨ p2737 ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72256 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step100754 (p2685 p2737 p2743 p2807 p3572 p4117 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73420 : p3572 ∨ p2685)
    (h72257 : (¬ p2743) ∨ (¬ p2807) ∨ (¬ p4117) ∨ (¬ p3572))
    : (¬ p2807) ∨ p2737 ∨ (¬ p4117) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72257 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100756 (p2284 p2685 p2807 p3136 p3572 p4117 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h47462 : (¬ p2284) ∨ (¬ p2807) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p4117))
    : (¬ p2284) ∨ (¬ p3136) ∨ (¬ p4117) ∨ p2685 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47462 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step100759 (p2331 p2774 p2780 p4117 p4337 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h13755 : (¬ p2331) ∨ (¬ p2780) ∨ (¬ p4117) ∨ (¬ p4337))
    : (¬ p4337) ∨ p2774 ∨ (¬ p2331) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4337 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h13755 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step100761 (p2630 p2685 p2753 p2807 p3266 p3379 p3572 p3707 p3830 p3834 p4117 p4321 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73474 : p3834 ∨ p3830)
    (h73420 : p3572 ∨ p2685)
    (h72258 : (¬ p3266) ∨ (¬ p4321) ∨ (¬ p3834) ∨ (¬ p2753) ∨ (¬ p3572) ∨ (¬ p3379) ∨ (¬ p2630) ∨ (¬ p4117) ∨ (¬ p2807))
    : p3707 ∨ p3830 ∨ (¬ p2807) ∨ (¬ p2753) ∨ (¬ p3266) ∨ (¬ p3379) ∨ (¬ p2630) ∨ (¬ p4117) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h72258 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step100766 (p2145 p2156 p2563 p2761 p2807 p2982 p3506 p3646 p3951 p4117 p4381 p4661 p4948 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73436 : p3646 ∨ p2156)
    (h73846 : p4948 ∨ p2982)
    (h58460 : (¬ p2145) ∨ (¬ p2563) ∨ (¬ p2807) ∨ (¬ p3506) ∨ (¬ p3646) ∨ (¬ p3951) ∨ (¬ p4117) ∨ (¬ p4381) ∨ (¬ p4661) ∨ (¬ p4948))
    : p2761 ∨ (¬ p3506) ∨ (¬ p3951) ∨ (¬ p4661) ∨ p2156 ∨ p2982 ∨ (¬ p4117) ∨ (¬ p2807) ∨ (¬ p2563) ∨ (¬ p2145) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58460 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u12)))))))))))))))))))))

theorem step100767 (p3136 p4315 p5052 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h48318 : (¬ p4315) ∨ p5052)
    : p3136 ∨ p5052 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5052) := (fun h => hn (Or.inr h));
    let u2 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48318 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step100768 (p2331 p2630 p2946 p2963 p3136 p4315 p4972 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73550 : p4315 ∨ p3136)
    (h48056 : (¬ p2630) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p4315) ∨ (¬ p4972))
    : p2331 ∨ (¬ p2946) ∨ p3136 ∨ (¬ p4972) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48056 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100771 (p2459 p2696 p3115 p3136 p3365 p3399 p3527 p4208 p4315 p4736 p5059 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73550 : p4315 ∨ p3136)
    (h73534 : p4208 ∨ p3115)
    (h57816 : (¬ p2459) ∨ (¬ p3365) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4736) ∨ (¬ p5059))
    : (¬ p3527) ∨ p2696 ∨ (¬ p3399) ∨ (¬ p4736) ∨ (¬ p2459) ∨ p3136 ∨ (¬ p5059) ∨ p3115 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57816 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step100775 (p2630 p3136 p3343 p3879 p4315 p4953 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h42378 : (¬ p2630) ∨ (¬ p3343) ∨ (¬ p3879) ∨ (¬ p4315) ∨ (¬ p4953))
    : (¬ p3343) ∨ (¬ p4953) ∨ (¬ p2630) ∨ p3136 ∨ (¬ p3879) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42378 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step100776 (p2132 p2630 p3136 p4315 p5053 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h47703 : (¬ p2132) ∨ (¬ p2630) ∨ (¬ p4315) ∨ p5053)
    : p5053 ∨ p3136 ∨ (¬ p2132) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5053) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3136) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47703 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step100781 (p2396 p2553 p2573 p2579 p2588 p2753 p2946 p3005 p3136 p3347 p3945 p4107 p4117 p4311 p4315 p4902 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73550 : p4315 ∨ p3136)
    (h73282 : p2588 ∨ p2553)
    (h73514 : p4107 ∨ p2396)
    (h72261 : (¬ p3005) ∨ (¬ p2588) ∨ (¬ p4117) ∨ (¬ p2946) ∨ (¬ p4107) ∨ (¬ p4315) ∨ (¬ p3945) ∨ (¬ p2579) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p4311) ∨ (¬ p4902))
    : (¬ p3005) ∨ (¬ p2753) ∨ (¬ p3347) ∨ p2573 ∨ (¬ p4311) ∨ (¬ p4117) ∨ (¬ p3945) ∨ p3136 ∨ (¬ p2946) ∨ p2553 ∨ p2396 ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u14 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u15 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h72261 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u15))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u4))) (fun r10 => (False.elim (r10 u11)))))))))))))))))))))))))

theorem step100782 (p2946 p3136 p3166 p3172 p3256 p4118 p4315 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73356 : p3172 ∨ p3166)
    (h73550 : p4315 ∨ p3136)
    (h43526 : (¬ p2946) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4315))
    : p3256 ∨ p3166 ∨ (¬ p2946) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43526 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step100784 (p2563 p2797 p3136 p3567 p4110 p4315 p4356 p4705 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73550 : p4315 ∨ p3136)
    (h41821 : (¬ p2797) ∨ (¬ p3567) ∨ (¬ p4110) ∨ (¬ p4315) ∨ (¬ p4356) ∨ (¬ p4705))
    : (¬ p2797) ∨ (¬ p3567) ∨ p2563 ∨ (¬ p4705) ∨ (¬ p4356) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41821 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step100789 (p2470 p2630 p2656 p3136 p3879 p4315 p4610 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h42400 : (¬ p2470) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3879) ∨ (¬ p4315) ∨ (¬ p4610))
    : (¬ p2470) ∨ (¬ p2656) ∨ (¬ p2630) ∨ (¬ p3879) ∨ p3136 ∨ (¬ p4610) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42400 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step100791 (p2177 p2299 p2696 p2901 p2911 p2922 p3136 p3365 p3366 p4315 p4320 p4376 p4559 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73552 : p4320 ∨ p2901)
    (h73234 : p2299 ∨ p2177)
    (h73550 : p4315 ∨ p3136)
    (h42455 : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p4315) ∨ (¬ p4320) ∨ (¬ p4376) ∨ (¬ p4559))
    : (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3366) ∨ (¬ p4559) ∨ p2696 ∨ p2901 ∨ p2177 ∨ p3136 ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42455 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step100793 (p2187 p3125 p3136 p3323 p3989 p4037 p4153 p4315 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73550 : p4315 ∨ p3136)
    (h73502 : p3989 ∨ p2187)
    (h57704 : (¬ p3125) ∨ (¬ p3989) ∨ (¬ p4037) ∨ (¬ p4153) ∨ (¬ p4315))
    : (¬ p3125) ∨ p3323 ∨ p3136 ∨ (¬ p4153) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57704 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step100796 (p2363 p2696 p3093 p3115 p3136 p3365 p3366 p3449 p3591 p4208 p4315 p4318 p4866 p5059 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73550 : p4315 ∨ p3136)
    (h73534 : p4208 ∨ p3115)
    (h73390 : p3365 ∨ p2696)
    (h55092 : (¬ p2363) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4318) ∨ (¬ p4866) ∨ (¬ p5059))
    : (¬ p4318) ∨ p3093 ∨ p3136 ∨ p3115 ∨ p2696 ∨ (¬ p3449) ∨ (¬ p3366) ∨ (¬ p5059) ∨ (¬ p2363) ∨ (¬ p4866) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55092 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step100803 (p2220 p2553 p2588 p2619 p2860 p3758 p4120 p4203 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h73282 : p2588 ∨ p2553)
    (h73522 : p4120 ∨ p2220)
    (h45683 : (¬ p2588) ∨ (¬ p2619) ∨ (¬ p3758) ∨ (¬ p4120) ∨ (¬ p4203))
    : p2860 ∨ (¬ p2619) ∨ p2553 ∨ (¬ p4203) ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45683 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step100805 (p2136 p2220 p2619 p3425 p3471 p4120 p4897 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73396 : p3471 ∨ p3425)
    (h54935 : (¬ p2136) ∨ (¬ p2619) ∨ (¬ p3471) ∨ (¬ p4120) ∨ (¬ p4897))
    : (¬ p2619) ∨ (¬ p2136) ∨ p2220 ∨ p3425 ∨ (¬ p4897) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4897 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54935 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step100809 (p2132 p2619 p2774 p2780 p2829 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h42729 : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2780) ∨ (¬ p2829))
    : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2829) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42729 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step100812 (p2619 p2797 p3156 p3497 p4195 p4313 p4700 p4972 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73400 : p3497 ∨ p3156)
    (h59812 : (¬ p2619) ∨ (¬ p3497) ∨ (¬ p4195) ∨ (¬ p4313) ∨ (¬ p4700) ∨ (¬ p4972))
    : (¬ p2619) ∨ p2797 ∨ (¬ p4313) ∨ (¬ p4700) ∨ p3156 ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59812 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step100813 (p2156 p2252 p2417 p2437 p2619 p2651 p2657 p2750 p3125 p3370 p3371 p3742 p3917 p4193 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73452 : p3742 ∨ p2437)
    (h73288 : p2657 ∨ p2651)
    (h53518 : (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3125) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3742) ∨ (¬ p3917) ∨ (¬ p4193) ∨ (¬ p4278))
    : p2417 ∨ (¬ p3370) ∨ (¬ p3917) ∨ (¬ p3371) ∨ (¬ p4193) ∨ p2437 ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2156) ∨ (¬ p2619) ∨ p2651 ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u14 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h53518 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u4))) (fun r10 => (False.elim (r10 u12)))))))))))))))))))))))))

theorem step100821 (p2363 p2459 p2774 p2780 p2819 p4347 p4358 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73564 : p4358 ∨ p2819)
    (h73308 : p2780 ∨ p2774)
    (h46559 : (¬ p2459) ∨ (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4358))
    : p2363 ∨ p2819 ∨ p2774 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46559 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step100822 (p2307 p2313 p2383 p2396 p2819 p4107 p4358 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73238 : p2313 ∨ p2307)
    (h73564 : p4358 ∨ p2819)
    (h46586 : (¬ p2313) ∨ (¬ p2383) ∨ (¬ p4107) ∨ (¬ p4358))
    : (¬ p2383) ∨ p2396 ∨ p2307 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46586 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step100823 (p2230 p2440 p2531 p2608 p2819 p2829 p3083 p3688 p3954 p4358 p4433 p5190 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h73564 : p4358 ∨ p2819)
    (h58255 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p3083) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4358) ∨ (¬ p4433) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p3083) ∨ (¬ p2531) ∨ p2829 ∨ p2608 ∨ p2819 ∨ (¬ p4433) ∨ (¬ p2440) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58255 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step100826 (p2246 p2363 p2744 p2774 p2780 p2819 p2901 p2946 p3246 p3366 p3950 p4347 p4358 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h63980 : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358))
    : p2363 ∨ (¬ p2246) ∨ p2774 ∨ (¬ p2946) ∨ (¬ p3366) ∨ (¬ p2901) ∨ (¬ p3950) ∨ p2819 ∨ (¬ p3246) ∨ (¬ p2744) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63980 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u12)))))))))))))))))))))

theorem step100831 (p2187 p2819 p2870 p4193 p4358 p4558 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h53859 : (¬ p2187) ∨ (¬ p2870) ∨ (¬ p4193) ∨ (¬ p4358) ∨ (¬ p4558))
    : (¬ p4558) ∨ (¬ p2187) ∨ p2819 ∨ (¬ p4193) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53859 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

end ElevenRUP
