import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step84901 (p2190 p2274 p3097 p3969 p4405 p5580 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h48118 : (¬ p2190) ∨ (¬ p3097) ∨ (¬ p3969) ∨ (¬ p4405) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p2190) ∨ (¬ p3969) ∨ (¬ p4405) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48118 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step84902 (p2190 p3125 p3744 p3955 p3969 p4620 p5580 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h42017 : (¬ p2190) ∨ (¬ p3744) ∨ (¬ p3955) ∨ (¬ p3969) ∨ (¬ p4620) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p2190) ∨ p3125 ∨ (¬ p3955) ∨ (¬ p4620) ∨ (¬ p3969) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42017 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step84903 (p2352 p2528 p2534 p3564 p4594 p5118 p5580 : Prop)
    (h73267 : (¬ p2528) ∨ (¬ p2534))
    (h73656 : p4594 ∨ p2352)
    (h67214 : (¬ p4594) ∨ (¬ p3564) ∨ (¬ p5580) ∨ (¬ p5118) ∨ p2534)
    : (¬ p5580) ∨ (¬ p5118) ∨ (¬ p2528) ∨ (¬ p3564) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2534) := (Or.elim h73267 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u6 : p4594 := (Or.elim h73656 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67214 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u5 r3)))))))))))

theorem step84906 (p2352 p2493 p2499 p3379 p3452 p3956 p5580 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h73500 : p3956 ∨ p2352)
    (h44232 : (¬ p2499) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p5580))
    : (¬ p5580) ∨ p2493 ∨ p3379 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44232 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step84909 (p2383 p2387 p2459 p2778 p3941 p4348 p5580 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73246 : p2387 ∨ p2383)
    (h47049 : (¬ p2387) ∨ (¬ p2778) ∨ (¬ p3941) ∨ (¬ p4348) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p3941) ∨ p2459 ∨ p2383 ∨ (¬ p2778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47049 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step84910 (p2383 p2387 p2528 p2534 p2778 p2881 p2901 p2946 p4149 p4786 p5580 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73268 : p2534 ∨ p2528)
    (h52232 : (¬ p2387) ∨ (¬ p2534) ∨ (¬ p2778) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4149) ∨ (¬ p4786) ∨ (¬ p5580))
    : (¬ p4149) ∨ (¬ p5580) ∨ p2383 ∨ p2528 ∨ (¬ p2881) ∨ (¬ p2778) ∨ (¬ p2946) ∨ (¬ p4786) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52232 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step84912 (p2774 p2780 p2819 p2946 p3115 p3680 p4358 p4786 p5123 p5580 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h63992 : (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p4358) ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p3115) ∨ (¬ p2946) ∨ (¬ p3680) ∨ (¬ p5123) ∨ p2774 ∨ (¬ p4786) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63992 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step84917 (p2246 p2352 p2449 p2573 p2579 p2744 p2761 p2807 p3347 p3956 p4257 p5123 p5580 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73500 : p3956 ∨ p2352)
    (h52925 : (¬ p2246) ∨ (¬ p2449) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3347) ∨ (¬ p3956) ∨ (¬ p4257) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p2246) ∨ (¬ p5123) ∨ p2573 ∨ (¬ p2761) ∨ p2352 ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p4257) ∨ (¬ p3347) ∨ (¬ p2744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52925 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step84918 (p2246 p2651 p2744 p2774 p2780 p2819 p3276 p3343 p3366 p4358 p5123 p5580 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h63831 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p4358) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p2246) ∨ (¬ p3366) ∨ p2774 ∨ (¬ p2744) ∨ (¬ p2651) ∨ p2819 ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63831 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step84920 (p2241 p2247 p2352 p2573 p2579 p2744 p3073 p3366 p3449 p3905 p3956 p5118 p5580 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73226 : p2247 ∨ p2241)
    (h73500 : p3956 ∨ p2352)
    (h60494 : (¬ p2247) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3905) ∨ (¬ p3956) ∨ (¬ p5118) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p5118) ∨ (¬ p3905) ∨ (¬ p3366) ∨ p2573 ∨ (¬ p3073) ∨ p2241 ∨ (¬ p2744) ∨ (¬ p3449) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h60494 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step84921 (p2241 p2247 p2744 p2819 p2829 p3073 p3449 p3688 p4358 p5118 p5580 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73564 : p4358 ∨ p2819)
    (h73444 : p3688 ∨ p2829)
    (h52551 : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3688) ∨ (¬ p4358) ∨ (¬ p5118) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p5118) ∨ p2241 ∨ (¬ p2744) ∨ (¬ p3449) ∨ p2819 ∨ (¬ p3073) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h52551 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step84922 (p2136 p2156 p2187 p2241 p2247 p2744 p3073 p3366 p3449 p3646 p3989 p5118 p5580 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73436 : p3646 ∨ p2156)
    (h73502 : p3989 ∨ p2187)
    (h59483 : (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p5118) ∨ (¬ p5580))
    : (¬ p5580) ∨ p2241 ∨ (¬ p5118) ∨ p2156 ∨ (¬ p3449) ∨ (¬ p3073) ∨ (¬ p2744) ∨ (¬ p3366) ∨ p2187 ∨ (¬ p2136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h59483 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step84923 (p2156 p2187 p2241 p2247 p3506 p3645 p3646 p3830 p3853 p3989 p4959 p5123 p5580 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73502 : p3989 ∨ p2187)
    (h73436 : p3646 ∨ p2156)
    (h50171 : (¬ p2247) ∨ (¬ p3506) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p3989) ∨ (¬ p4959) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p3853) ∨ (¬ p3830) ∨ (¬ p3506) ∨ p2241 ∨ (¬ p5123) ∨ (¬ p3645) ∨ p2187 ∨ p2156 ∨ (¬ p4959) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h50171 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step84925 (p2252 p2331 p2608 p2668 p2750 p2963 p3324 p3707 p3830 p3954 p5123 p5580 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73338 : p2963 ∨ p2331)
    (h73386 : p3324 ∨ p2668)
    (h64470 : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ p2608 ∨ p2331 ∨ (¬ p3707) ∨ (¬ p2750) ∨ p2668 ∨ (¬ p3830) ∨ (¬ p5123) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h64470 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step84929 (p2651 p2774 p2780 p2819 p3276 p3343 p4358 p4786 p5123 p5580 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h63748 : (¬ p2651) ∨ (¬ p2780) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4358) ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p5123) ∨ (¬ p3276) ∨ (¬ p3343) ∨ p2774 ∨ (¬ p2651) ∨ p2819 ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63748 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step84933 (p2241 p2247 p2363 p3998 p5242 p5580 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h47024 : (¬ p2247) ∨ (¬ p2363) ∨ (¬ p3998) ∨ (¬ p5242) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p3998) ∨ (¬ p2363) ∨ (¬ p5242) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47024 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step84934 (p2103 p2363 p2563 p3698 p3998 p4110 p4744 p5580 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h57103 : (¬ p2103) ∨ (¬ p2363) ∨ (¬ p3698) ∨ (¬ p3998) ∨ (¬ p4110) ∨ (¬ p4744) ∨ (¬ p5580))
    : (¬ p3998) ∨ (¬ p5580) ∨ (¬ p4744) ∨ (¬ p2103) ∨ (¬ p2363) ∨ (¬ p3698) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3998 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2103 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h57103 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step84935 (p2510 p2553 p2588 p4149 p4405 p5580 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h42587 : (¬ p2510) ∨ (¬ p2588) ∨ (¬ p4149) ∨ (¬ p4405) ∨ (¬ p5580))
    : (¬ p4149) ∨ (¬ p5580) ∨ p2553 ∨ (¬ p4405) ∨ (¬ p2510) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42587 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step84944 (p2307 p2383 p2387 p3941 p5580 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h45830 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3941) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p3941) ∨ p2383 ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45830 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step84945 (p2249 p2331 p2656 p2727 p2963 p3212 p3680 p3922 p3923 p4399 p5123 p5580 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h61194 : (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3212) ∨ (¬ p3680) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p4399) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p3680) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p2249) ∨ (¬ p3212) ∨ (¬ p2727) ∨ (¬ p2656) ∨ (¬ p4399) ∨ p2331 ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h61194 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step84946 (p2230 p2331 p2668 p2963 p3105 p3324 p3362 p3680 p3698 p4789 p5123 p5580 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73338 : p2963 ∨ p2331)
    (h48266 : (¬ p2230) ∨ (¬ p2963) ∨ (¬ p3105) ∨ (¬ p3324) ∨ (¬ p3362) ∨ (¬ p3680) ∨ (¬ p3698) ∨ (¬ p4789) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p3680) ∨ (¬ p5123) ∨ p2668 ∨ (¬ p2230) ∨ (¬ p3362) ∨ (¬ p3105) ∨ (¬ p4789) ∨ (¬ p3698) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h48266 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step84947 (p2156 p2187 p2696 p2753 p3506 p3645 p3646 p3755 p3989 p4877 p5123 p5580 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h73436 : p3646 ∨ p2156)
    (h61381 : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3506) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p3989) ∨ (¬ p4877) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p2753) ∨ p2187 ∨ (¬ p3645) ∨ (¬ p3755) ∨ p2156 ∨ (¬ p3506) ∨ (¬ p4877) ∨ (¬ p2696) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h61381 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step84949 (p2156 p2187 p2241 p3506 p3646 p3842 p3989 p4524 p5123 p5580 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h73436 : p3646 ∨ p2156)
    (h72962 : p4524)
    (h52235 : (¬ p2241) ∨ (¬ p3506) ∨ (¬ p3646) ∨ (¬ p3842) ∨ (¬ p3989) ∨ (¬ p4524) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p3842) ∨ (¬ p5123) ∨ (¬ p2241) ∨ p2187 ∨ p2156 ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p4524 := h72962;
    (Or.elim h52235 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step84952 (p2274 p3125 p3246 p3690 p3744 p3872 : Prop)
    (h73445 : (¬ p3246) ∨ (¬ p3690))
    (h73454 : p3744 ∨ p3125)
    (h65745 : (¬ p3744) ∨ (¬ p2274) ∨ (¬ p3872) ∨ p3690)
    : (¬ p3246) ∨ p3125 ∨ (¬ p3872) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3690) := (Or.elim h73445 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h65745 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u4 r2)))))))))

theorem step84956 (p2284 p3146 p3256 p3692 p3952 p4237 p4509 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73448 : p3692 ∨ p3146)
    (h50306 : (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3952) ∨ (¬ p4237) ∨ (¬ p4509))
    : (¬ p4237) ∨ (¬ p3256) ∨ p2284 ∨ p3146 ∨ (¬ p4509) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4237 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50306 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step84958 (p2284 p3952 p4009 p4188 p4237 p4509 p5612 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h62184 : (¬ p3952) ∨ (¬ p4009) ∨ (¬ p4188) ∨ (¬ p4237) ∨ (¬ p4509) ∨ (¬ p5612))
    : (¬ p5612) ∨ (¬ p4009) ∨ (¬ p4509) ∨ (¬ p4188) ∨ p2284 ∨ (¬ p4237) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5612 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4188 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62184 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step84960 (p2255 p2946 p3073 p3256 p4237 p4261 p4262 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h48511 : (¬ p2255) ∨ (¬ p2946) ∨ (¬ p3256) ∨ (¬ p4237) ∨ (¬ p4261) ∨ (¬ p4262))
    : p3073 ∨ (¬ p3256) ∨ (¬ p2946) ∨ (¬ p2255) ∨ (¬ p4262) ∨ (¬ p4237) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4262 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48511 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step84962 (p2417 p2881 p3570 p3657 p4001 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h33944 : (¬ p2417) ∨ (¬ p3570) ∨ (¬ p3657) ∨ (¬ p4001))
    : (¬ p2417) ∨ (¬ p3657) ∨ p2881 ∨ (¬ p4001) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h33944 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step84968 (p2341 p2946 p2952 p3037 p3527 p3548 p4104 p4919 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73404 : p3548 ∨ p3527)
    (h41024 : (¬ p2341) ∨ (¬ p2952) ∨ (¬ p3037) ∨ (¬ p3548) ∨ (¬ p4104) ∨ (¬ p4919))
    : (¬ p3037) ∨ (¬ p2341) ∨ (¬ p4919) ∨ (¬ p4104) ∨ p2946 ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3037 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41024 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step84975 (p2383 p2396 p2449 p2668 p3324 p3987 p4107 p4156 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73386 : p3324 ∨ p2668)
    (h43228 : (¬ p2383) ∨ (¬ p2449) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4107) ∨ (¬ p4156))
    : (¬ p2383) ∨ (¬ p2449) ∨ (¬ p4156) ∨ p2396 ∨ p2668 ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43228 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step84976 (p2383 p2668 p2946 p2952 p3324 p3987 p4566 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73330 : p2952 ∨ p2946)
    (h41103 : (¬ p2383) ∨ (¬ p2952) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4566))
    : (¬ p2383) ∨ p2668 ∨ (¬ p4566) ∨ (¬ p3987) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2668) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4566 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41103 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step84977 (p2295 p2383 p2396 p2668 p3324 p3987 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h49483 : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2396) ∨ (¬ p3324) ∨ (¬ p3987))
    : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p3987) ∨ p2668 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49483 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step84979 (p2274 p2295 p2383 p2668 p3097 p3324 p3987 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73352 : p3097 ∨ p2274)
    (h49481 : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p3097) ∨ (¬ p3324) ∨ (¬ p3987))
    : (¬ p2295) ∨ (¬ p2383) ∨ p2668 ∨ (¬ p3987) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49481 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step84980 (p2295 p2383 p2651 p2657 p2668 p3324 p3987 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73288 : p2657 ∨ p2651)
    (h49464 : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2657) ∨ (¬ p3324) ∨ (¬ p3987))
    : (¬ p2295) ∨ (¬ p2383) ∨ p2668 ∨ (¬ p3987) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49464 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step84981 (p2383 p2630 p2668 p2797 p3324 p3987 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73386 : p3324 ∨ p2668)
    (h43224 : (¬ p2383) ∨ (¬ p2630) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4195))
    : p2797 ∨ (¬ p2383) ∨ (¬ p2630) ∨ p2668 ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43224 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step84982 (p2383 p2668 p2797 p3324 p3987 p4195 p4790 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73386 : p3324 ∨ p2668)
    (h53073 : (¬ p2383) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4195) ∨ (¬ p4790))
    : p2797 ∨ (¬ p2383) ∨ p2668 ∨ (¬ p4790) ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53073 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step84986 (p3286 p3292 p3987 p4036 p4038 p4190 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h17654 : (¬ p3292) ∨ (¬ p3987) ∨ (¬ p4036) ∨ (¬ p4038) ∨ (¬ p4190))
    : p3286 ∨ (¬ p4036) ∨ (¬ p3987) ∨ (¬ p4038) ∨ (¬ p4190) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p4036 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h17654 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step84987 (p2667 p3286 p3292 p3987 p4421 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h32327 : (¬ p2667) ∨ (¬ p3292) ∨ (¬ p3987) ∨ (¬ p4421))
    : p3286 ∨ (¬ p4421) ∨ (¬ p2667) ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h32327 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step84998 (p2573 p2579 p3355 p3746 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h20208 : (¬ p2579) ∨ (¬ p3355) ∨ (¬ p3746))
    : (¬ p3355) ∨ (¬ p3746) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20208 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step85001 (p2573 p2579 p3016 p3276 p3355 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h47889 : (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3276) ∨ (¬ p3355))
    : (¬ p3355) ∨ (¬ p3276) ∨ (¬ p3016) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47889 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step85004 (p2363 p2470 p2476 p3355 p4347 p4384 p4695 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73250 : p2476 ∨ p2470)
    (h46822 : (¬ p2476) ∨ (¬ p3355) ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p4695))
    : (¬ p4695) ∨ p2363 ∨ (¬ p3355) ∨ p2470 ∨ (¬ p4384) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4695 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46822 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step85006 (p2470 p2476 p3146 p3355 p3692 p4434 p4695 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73250 : p2476 ∨ p2470)
    (h41697 : (¬ p2476) ∨ (¬ p3355) ∨ (¬ p3692) ∨ (¬ p4434) ∨ (¬ p4695))
    : (¬ p3355) ∨ p3146 ∨ (¬ p4434) ∨ p2470 ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41697 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85010 (p3355 p3389 p3540 p4635 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h19852 : (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4635))
    : (¬ p3355) ∨ (¬ p4635) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19852 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step85011 (p2449 p3355 p3389 p3540 p3947 p4327 p4451 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73494 : p3947 ∨ p2449)
    (h48023 : (¬ p3355) ∨ (¬ p3540) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p4451))
    : (¬ p3355) ∨ (¬ p4451) ∨ p3389 ∨ p2449 ∨ (¬ p4327) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4327 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48023 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85012 (p3246 p3355 p3389 p3540 p3690 p4451 p4647 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73402 : p3540 ∨ p3389)
    (h50081 : (¬ p3355) ∨ (¬ p3540) ∨ (¬ p3690) ∨ (¬ p4451) ∨ (¬ p4647))
    : (¬ p3355) ∨ (¬ p4451) ∨ p3246 ∨ (¬ p4647) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50081 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85016 (p2553 p2573 p2579 p2588 p3355 p5160 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73282 : p2588 ∨ p2553)
    (h47982 : (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3355) ∨ (¬ p5160))
    : (¬ p3355) ∨ (¬ p5160) ∨ p2573 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47982 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step85018 (p2493 p2573 p2579 p3276 p3355 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h59610 : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3276) ∨ (¬ p3355))
    : (¬ p3355) ∨ (¬ p3276) ∨ (¬ p2493) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59610 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step85023 (p2437 p2573 p2579 p3016 p3355 p3742 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73274 : p2579 ∨ p2573)
    (h45915 : (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3355) ∨ (¬ p3742))
    : p2437 ∨ (¬ p3355) ∨ (¬ p3016) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45915 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85026 (p2437 p2761 p3355 p3389 p3540 p4451 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h58080 : (¬ p2437) ∨ (¬ p2761) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4451))
    : (¬ p2437) ∨ (¬ p3355) ∨ p3389 ∨ (¬ p2761) ∨ (¬ p4451) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58080 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85029 (p2437 p2440 p3355 p3389 p3540 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h45864 : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p3355) ∨ (¬ p3540))
    : (¬ p3355) ∨ p3389 ∨ (¬ p2440) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45864 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85033 (p2230 p2440 p2542 p2589 p3355 p3680 p4952 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h48715 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3355) ∨ (¬ p3680) ∨ (¬ p4952))
    : (¬ p3680) ∨ (¬ p3355) ∨ p2440 ∨ p2230 ∨ (¬ p4952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48715 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85034 (p2230 p2589 p3276 p3355 p4322 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h63425 : (¬ p2589) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p4322))
    : (¬ p4322) ∨ (¬ p3276) ∨ (¬ p3355) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63425 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step85035 (p2230 p2406 p2589 p3276 p3355 p4281 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h45161 : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p4281))
    : (¬ p2406) ∨ (¬ p3355) ∨ (¬ p3276) ∨ p2230 ∨ (¬ p4281) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45161 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85036 (p2230 p2589 p3237 p3355 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h20205 : (¬ p2589) ∨ (¬ p3237) ∨ (¬ p3355))
    : (¬ p3355) ∨ (¬ p3237) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20205 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step85041 (p2459 p2470 p2476 p3355 p4348 p4438 p4695 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73250 : p2476 ∨ p2470)
    (h40946 : (¬ p2476) ∨ (¬ p3355) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4695))
    : (¬ p3355) ∨ (¬ p4438) ∨ p2459 ∨ p2470 ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h40946 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85042 (p2930 p3355 p3389 p3540 p3631 p3817 p4451 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h73402 : p3540 ∨ p3389)
    (h41096 : (¬ p2930) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p3817) ∨ (¬ p4451))
    : (¬ p3355) ∨ (¬ p4451) ∨ p3631 ∨ p3389 ∨ (¬ p2930) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2930 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41096 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85047 (p2761 p2922 p3355 p3389 p3540 p4451 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h55293 : (¬ p2761) ∨ (¬ p2922) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4451))
    : (¬ p4451) ∨ (¬ p2922) ∨ p3389 ∨ (¬ p2761) ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4451 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55293 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step85052 (p2459 p3941 p4348 p5116 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h30490 : (¬ p3941) ∨ (¬ p4348) ∨ (¬ p5116))
    : (¬ p3941) ∨ (¬ p5116) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h30490 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step85053 (p2241 p2247 p3449 p4262 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h6433 : (¬ p2247) ∨ (¬ p3449) ∨ (¬ p4262))
    : (¬ p4262) ∨ (¬ p3449) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4262 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6433 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step85065 (p2088 p2745 p2951 p3073 p3136 p4261 p4262 p4590 p4988 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h64951 : (¬ p2088) ∨ (¬ p2745) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p4261) ∨ (¬ p4262) ∨ (¬ p4590) ∨ (¬ p4988))
    : p3073 ∨ (¬ p3136) ∨ (¬ p4590) ∨ (¬ p2951) ∨ (¬ p2745) ∨ (¬ p4988) ∨ (¬ p4262) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4262 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h64951 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step85066 (p2295 p2331 p2737 p2743 p2881 p2963 p3361 p3425 p3471 p3527 p3568 p3570 p4424 p4556 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73396 : p3471 ∨ p3425)
    (h73298 : p2743 ∨ p2737)
    (h73416 : p3568 ∨ p2295)
    (h73418 : p3570 ∨ p2881)
    (h71601 : (¬ p4424) ∨ (¬ p3527) ∨ (¬ p4556) ∨ (¬ p3570) ∨ (¬ p3471) ∨ (¬ p2963) ∨ (¬ p2743) ∨ (¬ p3568) ∨ (¬ p3361))
    : (¬ p3527) ∨ p2331 ∨ (¬ p4556) ∨ (¬ p3361) ∨ p3425 ∨ (¬ p4424) ∨ p2737 ∨ p2295 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71601 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step85068 (p2881 p2946 p2992 p3038 p3527 p3570 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73418 : p3570 ∨ p2881)
    (h43745 : (¬ p2946) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3662))
    : (¬ p3527) ∨ (¬ p3038) ∨ p2992 ∨ p2881 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43745 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85069 (p2210 p2553 p2588 p2598 p2881 p3055 p3422 p3527 p3570 p3584 p4431 p4556 p4736 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73426 : p3584 ∨ p3422)
    (h73350 : p3055 ∨ p2598)
    (h73418 : p3570 ∨ p2881)
    (h50471 : (¬ p2210) ∨ (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3584) ∨ (¬ p4431) ∨ (¬ p4556) ∨ (¬ p4736))
    : (¬ p3527) ∨ (¬ p4736) ∨ (¬ p4556) ∨ p2553 ∨ (¬ p2210) ∨ p3422 ∨ p2598 ∨ p2881 ∨ (¬ p4431) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50471 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step85072 (p2881 p3527 p3570 p4909 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h20248 : (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4909))
    : (¬ p3527) ∨ (¬ p4909) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20248 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step85074 (p2608 p2881 p3399 p3527 p3570 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73418 : p3570 ∨ p2881)
    (h45796 : (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3954))
    : (¬ p3527) ∨ p2608 ∨ p2881 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45796 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85075 (p2881 p3379 p3399 p3452 p3527 p3570 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73418 : p3570 ∨ p2881)
    (h44612 : (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3527) ∨ (¬ p3570))
    : (¬ p3527) ∨ p3379 ∨ (¬ p3399) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44612 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85077 (p2295 p2696 p2797 p2881 p3365 p3399 p3527 p3568 p3570 p4195 p4556 p4736 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73390 : p3365 ∨ p2696)
    (h73416 : p3568 ∨ p2295)
    (h73532 : p4195 ∨ p2797)
    (h52360 : (¬ p3365) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3568) ∨ (¬ p3570) ∨ (¬ p4195) ∨ (¬ p4556) ∨ (¬ p4736))
    : (¬ p3527) ∨ (¬ p4556) ∨ (¬ p3399) ∨ p2881 ∨ p2696 ∨ p2295 ∨ p2797 ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52360 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step85078 (p2298 p2331 p2797 p2881 p2963 p3005 p3399 p3527 p3570 p3877 p4044 p4236 p4556 p4736 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73418 : p3570 ∨ p2881)
    (h73338 : p2963 ∨ p2331)
    (h58286 : (¬ p2298) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3877) ∨ (¬ p4044) ∨ (¬ p4236) ∨ (¬ p4556) ∨ (¬ p4736))
    : (¬ p4236) ∨ (¬ p2797) ∨ (¬ p3399) ∨ (¬ p4736) ∨ p3005 ∨ (¬ p4044) ∨ p2881 ∨ (¬ p2298) ∨ p2331 ∨ (¬ p4556) ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h58286 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step85082 (p2437 p2573 p2579 p2881 p3016 p3399 p3527 p3570 p3742 p4647 p5193 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73418 : p3570 ∨ p2881)
    (h73274 : p2579 ∨ p2573)
    (h50534 : (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4647) ∨ (¬ p5193))
    : (¬ p3527) ∨ p2437 ∨ (¬ p5193) ∨ (¬ p3016) ∨ (¬ p3399) ∨ p2881 ∨ (¬ p4647) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50534 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step85085 (p2651 p2657 p2807 p2881 p3032 p3527 p3570 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73418 : p3570 ∨ p2881)
    (h45245 : (¬ p2657) ∨ (¬ p2807) ∨ (¬ p3032) ∨ (¬ p3527) ∨ (¬ p3570))
    : (¬ p3527) ∨ (¬ p3032) ∨ p2651 ∨ (¬ p2807) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45245 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step85086 (p2341 p2427 p3527 p3551 p3959 p4235 p4344 p4431 p4632 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73536 : p4235 ∨ p2427)
    (h41913 : (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3959) ∨ (¬ p4235) ∨ (¬ p4344) ∨ (¬ p4431) ∨ (¬ p4632))
    : (¬ p3527) ∨ p2341 ∨ (¬ p4344) ∨ (¬ p3959) ∨ p2427 ∨ (¬ p4632) ∨ (¬ p4431) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41913 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step85090 (p2156 p2274 p2396 p2441 p2608 p2911 p3097 p3399 p3527 p3644 p3645 p3646 p3954 p4107 p4877 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73436 : p3646 ∨ p2156)
    (h73498 : p3954 ∨ p2608)
    (h73434 : p3644 ∨ p2911)
    (h73352 : p3097 ∨ p2274)
    (h50795 : (¬ p2441) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4877))
    : (¬ p3527) ∨ p2396 ∨ (¬ p2441) ∨ (¬ p4877) ∨ p2156 ∨ p2608 ∨ (¬ p3645) ∨ (¬ p3399) ∨ p2911 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u14 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h50795 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step85094 (p2341 p3379 p3527 p3551 p3687 p5206 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h71602 : (¬ p3551) ∨ (¬ p3527) ∨ (¬ p3687) ∨ (¬ p3379) ∨ (¬ p5206))
    : (¬ p3527) ∨ p2341 ∨ (¬ p3687) ∨ (¬ p3379) ∨ (¬ p5206) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71602 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85098 (p2911 p3379 p3399 p3452 p3527 p3581 p3644 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73434 : p3644 ∨ p2911)
    (h59502 : (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3527) ∨ (¬ p3581) ∨ (¬ p3644))
    : (¬ p3527) ∨ p3379 ∨ (¬ p3399) ∨ p2911 ∨ (¬ p3581) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59502 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step85099 (p2177 p2254 p2299 p2685 p2946 p2952 p3136 p3399 p3527 p3572 p4361 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73420 : p3572 ∨ p2685)
    (h73330 : p2952 ∨ p2946)
    (h58583 : (¬ p2254) ∨ (¬ p2299) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3572) ∨ (¬ p4361))
    : (¬ p3527) ∨ (¬ p3136) ∨ p2177 ∨ (¬ p3399) ∨ (¬ p4361) ∨ (¬ p2254) ∨ p2685 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58583 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step85105 (p2341 p2608 p3527 p3551 p3820 p3873 p4793 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h48117 : (¬ p2608) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p3873) ∨ (¬ p4793))
    : (¬ p3527) ∨ p2341 ∨ (¬ p4793) ∨ (¬ p3873) ∨ (¬ p2608) ∨ (¬ p3820) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4793 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48117 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step85109 (p2241 p2247 p2437 p2911 p3527 p3644 p3742 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73434 : p3644 ∨ p2911)
    (h73452 : p3742 ∨ p2437)
    (h66765 : (¬ p3742) ∨ (¬ p2247) ∨ (¬ p3644) ∨ (¬ p3527))
    : (¬ p3527) ∨ p2241 ∨ p2911 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h66765 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step85111 (p2911 p2927 p3527 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h28361 : (¬ p2927) ∨ (¬ p3527) ∨ (¬ p3644))
    : (¬ p3527) ∨ (¬ p2927) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h28361 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step85118 (p3399 p3527 p3830 p3834 p4666 p5358 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h65032 : (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3834) ∨ (¬ p4666) ∨ (¬ p5358))
    : (¬ p5358) ∨ p3830 ∨ (¬ p4666) ∨ (¬ p3527) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5358 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h65032 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step85120 (p2417 p2911 p3399 p3527 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h44888 : (¬ p2417) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3644))
    : (¬ p3527) ∨ (¬ p2417) ∨ p2911 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44888 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85122 (p2177 p2299 p3527 p4435 p4452 p5472 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h48048 : (¬ p2299) ∨ (¬ p3527) ∨ (¬ p4435) ∨ (¬ p4452) ∨ (¬ p5472))
    : (¬ p4435) ∨ (¬ p5472) ∨ (¬ p4452) ∨ (¬ p3527) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4435 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48048 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85123 (p2254 p2274 p2284 p2717 p2946 p2952 p3097 p3399 p3527 p3659 p3952 p4473 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73438 : p3659 ∨ p2717)
    (h73496 : p3952 ∨ p2284)
    (h73352 : p3097 ∨ p2274)
    (h48457 : (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3952) ∨ (¬ p4473))
    : (¬ p3527) ∨ p2946 ∨ (¬ p2254) ∨ (¬ p4473) ∨ (¬ p3399) ∨ p2717 ∨ p2284 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h48457 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step85129 (p2274 p2311 p2341 p3527 p3551 p4427 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h71604 : (¬ p3527) ∨ (¬ p4427) ∨ (¬ p3551) ∨ (¬ p2274) ∨ (¬ p2311))
    : (¬ p3527) ∨ (¬ p4427) ∨ (¬ p2311) ∨ (¬ p2274) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71604 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85130 (p2274 p2396 p3527 p3631 p3817 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h55388 : (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3527) ∨ (¬ p3817))
    : p3631 ∨ (¬ p3527) ∨ (¬ p2274) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55388 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85135 (p2717 p2927 p3389 p3527 p3659 p3686 p4730 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h59991 : (¬ p2927) ∨ (¬ p3389) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3686) ∨ (¬ p4730))
    : (¬ p3527) ∨ (¬ p2927) ∨ (¬ p4730) ∨ (¬ p3389) ∨ (¬ p3686) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3686 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59991 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step85136 (p2264 p2665 p2927 p3389 p3527 p3553 p4112 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h48396 : (¬ p2665) ∨ (¬ p2927) ∨ (¬ p3389) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4112))
    : (¬ p3389) ∨ (¬ p4112) ∨ (¬ p2665) ∨ (¬ p2927) ∨ (¬ p3527) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48396 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step85138 (p2143 p2156 p2274 p2839 p2911 p3097 p3425 p3471 p3527 p3583 p3644 p3646 p4276 p4424 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73352 : p3097 ∨ p2274)
    (h73424 : p3583 ∨ p2839)
    (h73434 : p3644 ∨ p2911)
    (h73396 : p3471 ∨ p3425)
    (h71605 : (¬ p3527) ∨ (¬ p3583) ∨ (¬ p3097) ∨ (¬ p3471) ∨ (¬ p4276) ∨ (¬ p3646) ∨ (¬ p2143) ∨ (¬ p3644) ∨ (¬ p4424))
    : (¬ p4424) ∨ (¬ p3527) ∨ p2156 ∨ (¬ p2143) ∨ (¬ p4276) ∨ p2274 ∨ p2839 ∨ p2911 ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4424 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71605 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step85140 (p2295 p2383 p2387 p2667 p3527 p4138 p5145 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h63659 : (¬ p2295) ∨ (¬ p2387) ∨ (¬ p2667) ∨ (¬ p3527) ∨ (¬ p4138) ∨ (¬ p5145))
    : (¬ p5145) ∨ (¬ p2295) ∨ (¬ p2667) ∨ (¬ p4138) ∨ p2383 ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63659 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step85142 (p3309 p3547 p5143 : Prop)
    (h73938 : p5143 ∨ (¬ p3309))
    (h8709 : p3547 ∨ (¬ p5143))
    : p3547 ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3547) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5143 := (Or.elim h73938 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h8709 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step85159 (p2295 p2751 p2797 p3309 p3568 p4195 p4759 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73416 : p3568 ∨ p2295)
    (h60580 : (¬ p2751) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4759))
    : p2797 ∨ p2295 ∨ (¬ p2751) ∨ (¬ p4759) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60580 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85160 (p2295 p2797 p3093 p3309 p3568 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73416 : p3568 ∨ p2295)
    (h45998 : (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p4195))
    : p2797 ∨ p2295 ∨ (¬ p3093) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45998 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85162 (p2156 p3051 p3309 p3556 p4275 p4518 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h41646 : (¬ p2156) ∨ (¬ p3309) ∨ (¬ p3556) ∨ (¬ p4275) ∨ (¬ p4518))
    : p3051 ∨ (¬ p3309) ∨ (¬ p4518) ∨ (¬ p2156) ∨ (¬ p4275) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41646 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85165 (p2307 p2313 p2386 p3016 p3309 p3574 p3948 p4338 p4814 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73422 : p3574 ∨ p3016)
    (h53320 : (¬ p2313) ∨ (¬ p2386) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p3948) ∨ (¬ p4338) ∨ (¬ p4814))
    : (¬ p3948) ∨ (¬ p3309) ∨ p2307 ∨ p3016 ∨ (¬ p2386) ∨ (¬ p4814) ∨ (¬ p4338) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3948 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53320 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step85167 (p2307 p2313 p3309 p3379 p4869 p5015 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h71608 : (¬ p3379) ∨ (¬ p3309) ∨ (¬ p2313) ∨ (¬ p5015) ∨ (¬ p4869))
    : (¬ p3309) ∨ p2307 ∨ (¬ p5015) ∨ (¬ p3379) ∨ (¬ p4869) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71608 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85172 (p2553 p2588 p2598 p3309 p3367 p3585 p4869 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73282 : p2588 ∨ p2553)
    (h42877 : (¬ p2588) ∨ (¬ p2598) ∨ (¬ p3309) ∨ (¬ p3585) ∨ (¬ p4869))
    : (¬ p3309) ∨ (¬ p4869) ∨ (¬ p2598) ∨ p3367 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42877 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85174 (p2177 p2507 p2911 p3309 p3581 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h48163 : (¬ p2177) ∨ (¬ p2507) ∨ (¬ p3309) ∨ (¬ p3581) ∨ (¬ p3644))
    : p2911 ∨ (¬ p3309) ∨ (¬ p2177) ∨ (¬ p2507) ∨ (¬ p3581) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48163 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85175 (p2396 p2696 p3005 p3093 p3256 p3309 p3365 p3877 p3950 p4118 p4736 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73390 : p3365 ∨ p2696)
    (h73520 : p4118 ∨ p3256)
    (h50310 : (¬ p2396) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4736))
    : (¬ p3309) ∨ (¬ p2396) ∨ (¬ p3093) ∨ p3005 ∨ p2696 ∨ p3256 ∨ (¬ p4736) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50310 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step85179 (p2177 p2608 p3093 p3309 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h52571 : (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3954))
    : p2608 ∨ (¬ p3309) ∨ (¬ p3093) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h52571 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85181 (p2295 p2608 p3093 p3309 p3568 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73416 : p3568 ∨ p2295)
    (h62694 : (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p3954))
    : p2608 ∨ (¬ p3309) ∨ (¬ p3093) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62694 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85190 (p2295 p2331 p2963 p3309 p3568 p3923 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73338 : p2963 ∨ p2331)
    (h44192 : (¬ p2963) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p3923))
    : p2295 ∨ p2331 ∨ (¬ p3923) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44192 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step85191 (p2177 p2449 p2685 p2696 p3093 p3309 p3365 p3572 p3947 p4666 p4736 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73390 : p3365 ∨ p2696)
    (h73420 : p3572 ∨ p2685)
    (h49409 : (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4666) ∨ (¬ p4736))
    : p2449 ∨ (¬ p3309) ∨ p2696 ∨ (¬ p4666) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p4736) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49409 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step85192 (p2177 p2210 p2881 p3309 p3570 p4338 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h60323 : (¬ p2177) ∨ (¬ p2210) ∨ (¬ p3309) ∨ (¬ p3570) ∨ (¬ p4338))
    : (¬ p3309) ∨ p2881 ∨ (¬ p2177) ∨ (¬ p4338) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60323 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85195 (p2761 p3093 p3309 p3461 p4187 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h45910 : (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3461) ∨ (¬ p4187) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3461) ∨ (¬ p3309) ∨ (¬ p4187) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45910 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85196 (p2307 p2313 p2737 p2743 p2785 p3309 p4845 p4869 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73298 : p2743 ∨ p2737)
    (h42372 : (¬ p2313) ∨ (¬ p2743) ∨ (¬ p2785) ∨ (¬ p3309) ∨ (¬ p4845) ∨ (¬ p4869))
    : (¬ p3309) ∨ (¬ p4869) ∨ (¬ p4845) ∨ p2307 ∨ (¬ p2785) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42372 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step85201 (p2307 p2313 p3309 p3361 p3367 p3585 p3983 p4749 p4869 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73428 : p3585 ∨ p3367)
    (h53026 : (¬ p2313) ∨ (¬ p3309) ∨ (¬ p3361) ∨ (¬ p3585) ∨ (¬ p3983) ∨ (¬ p4749) ∨ (¬ p4869))
    : (¬ p3309) ∨ (¬ p4869) ∨ (¬ p3983) ∨ p2307 ∨ (¬ p3361) ∨ (¬ p4749) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h53026 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step85206 (p2528 p3073 p3309 p4261 p4371 p4432 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h71611 : (¬ p4371) ∨ (¬ p4432) ∨ (¬ p2528) ∨ (¬ p4261) ∨ (¬ p3309))
    : (¬ p3309) ∨ p3073 ∨ (¬ p2528) ∨ (¬ p4432) ∨ (¬ p4371) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71611 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step85207 (p2241 p2247 p2352 p2598 p2744 p3055 p3093 p3309 p3366 p3422 p3584 p3956 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73500 : p3956 ∨ p2352)
    (h73426 : p3584 ∨ p3422)
    (h73350 : p3055 ∨ p2598)
    (h71612 : (¬ p3956) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p3584))
    : p2241 ∨ (¬ p3366) ∨ p2352 ∨ p3422 ∨ (¬ p3309) ∨ (¬ p3093) ∨ (¬ p2744) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71612 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step85209 (p2505 p2509 p2553 p2588 p3309 p4595 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h53837 : (¬ p2505) ∨ (¬ p2509) ∨ (¬ p2588) ∨ (¬ p3309) ∨ (¬ p4595))
    : (¬ p3309) ∨ (¬ p2509) ∨ p2553 ∨ (¬ p2505) ∨ (¬ p4595) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4595 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53837 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85213 (p2132 p2138 p3093 p3105 p3276 p3309 p3791 p4385 p4425 p4736 p4826 p4952 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73576 : p4385 ∨ p3105)
    (h73214 : p2138 ∨ p2132)
    (h51436 : (¬ p2138) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3791) ∨ (¬ p4385) ∨ (¬ p4425) ∨ (¬ p4736) ∨ (¬ p4826) ∨ (¬ p4952))
    : (¬ p3791) ∨ p3276 ∨ p3105 ∨ (¬ p4952) ∨ p2132 ∨ (¬ p3309) ∨ (¬ p4826) ∨ (¬ p4736) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4385 := (Or.elim h73576 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51436 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step85214 (p2274 p3097 p3309 p3319 p3461 p4026 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73504 : p4026 ∨ p3319)
    (h73352 : p3097 ∨ p2274)
    (h64444 : (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4026) ∨ (¬ p4191))
    : p3461 ∨ p3319 ∨ (¬ p3309) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64444 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85218 (p2187 p2210 p2274 p3097 p3309 p4338 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h54997 : (¬ p2187) ∨ (¬ p2210) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4338))
    : (¬ p3309) ∨ p2274 ∨ (¬ p4338) ∨ (¬ p2187) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54997 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85220 (p2298 p2331 p2807 p3309 p3414 p4761 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h41629 : (¬ p2298) ∨ (¬ p2331) ∨ (¬ p3309) ∨ (¬ p3414) ∨ (¬ p4761))
    : (¬ p3309) ∨ (¬ p2298) ∨ (¬ p4761) ∨ p2807 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41629 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85222 (p2295 p2668 p3093 p3309 p3568 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h48668 : (¬ p2668) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3568))
    : (¬ p2668) ∨ p2295 ∨ (¬ p3093) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48668 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85224 (p2295 p2727 p3309 p3568 p4111 p4759 p4975 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73416 : p3568 ∨ p2295)
    (h51560 : (¬ p3309) ∨ (¬ p3568) ∨ (¬ p4111) ∨ (¬ p4759) ∨ (¬ p4975))
    : (¬ p3309) ∨ p2727 ∨ p2295 ∨ (¬ p4975) ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51560 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85227 (p2295 p3073 p3146 p3309 p3568 p4261 p4371 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73416 : p3568 ∨ p2295)
    (h44287 : (¬ p3146) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p4261) ∨ (¬ p4371))
    : p3073 ∨ (¬ p3309) ∨ (¬ p3146) ∨ (¬ p4371) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44287 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85231 (p2230 p2406 p2505 p2553 p2588 p2663 p3238 p3309 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73374 : p3238 ∨ p2406)
    (h63970 : (¬ p2230) ∨ (¬ p2505) ∨ (¬ p2588) ∨ (¬ p2663) ∨ (¬ p3238) ∨ (¬ p3309))
    : (¬ p3309) ∨ (¬ p2505) ∨ p2553 ∨ (¬ p2663) ∨ p2406 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63970 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step85232 (p2307 p2313 p2386 p2406 p2505 p3238 p3309 p4717 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73374 : p3238 ∨ p2406)
    (h42046 : (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2505) ∨ (¬ p3238) ∨ (¬ p3309) ∨ (¬ p4717))
    : (¬ p3309) ∨ p2307 ∨ p2406 ∨ (¬ p4717) ∨ (¬ p2386) ∨ (¬ p2505) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42046 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step85233 (p2505 p2922 p2928 p3309 p3921 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h5810 : (¬ p2505) ∨ (¬ p2928) ∨ (¬ p3309) ∨ (¬ p3921))
    : (¬ p3921) ∨ (¬ p3309) ∨ p2922 ∨ (¬ p2505) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3921 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h5810 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step85236 (p2230 p2441 p2589 p3093 p3309 p3921 p5193 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h41528 : (¬ p2441) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3921) ∨ (¬ p5193))
    : (¬ p3921) ∨ (¬ p2441) ∨ (¬ p3309) ∨ p2230 ∨ (¬ p5193) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3921 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41528 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step85239 (p2307 p2313 p2363 p3309 p3923 p4347 p5015 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73238 : p2313 ∨ p2307)
    (h53787 : (¬ p2313) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p5015))
    : (¬ p3309) ∨ p2363 ∨ (¬ p3923) ∨ p2307 ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53787 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85245 (p2307 p2313 p2373 p2598 p2850 p3309 p3923 p4433 p4733 p5015 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h51556 : (¬ p2313) ∨ (¬ p2373) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4433) ∨ (¬ p4733) ∨ (¬ p5015))
    : (¬ p3309) ∨ (¬ p2850) ∨ (¬ p4433) ∨ (¬ p2598) ∨ (¬ p3923) ∨ (¬ p4733) ∨ p2307 ∨ (¬ p2373) ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51556 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step85250 (p2553 p2588 p2608 p3093 p3309 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73282 : p2588 ∨ p2553)
    (h53566 : (¬ p2588) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3954))
    : p2608 ∨ (¬ p3309) ∨ p2553 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53566 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85252 (p2122 p2608 p3093 p3309 p3822 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73472 : p3822 ∨ p2122)
    (h62948 : (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p3954))
    : p2608 ∨ (¬ p3309) ∨ (¬ p3093) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62948 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85253 (p2274 p2608 p3093 p3097 p3309 p3954 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73498 : p3954 ∨ p2608)
    (h46878 : (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3954))
    : (¬ p3309) ∨ p2274 ∨ p2608 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46878 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85254 (p2210 p2274 p2608 p3097 p3309 p3954 p4338 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73498 : p3954 ∨ p2608)
    (h60218 : (¬ p2210) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3954) ∨ (¬ p4338))
    : (¬ p3309) ∨ p2274 ∨ p2608 ∨ (¬ p2210) ∨ (¬ p4338) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60218 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85255 (p2254 p2396 p2528 p2534 p2651 p2657 p3083 p3093 p3309 p3950 p4256 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73542 : p4256 ∨ p3083)
    (h73268 : p2534 ∨ p2528)
    (h48875 : (¬ p2254) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3950) ∨ (¬ p4256))
    : (¬ p3309) ∨ (¬ p3950) ∨ p2651 ∨ (¬ p3093) ∨ p3083 ∨ p2528 ∨ (¬ p2254) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48875 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step85259 (p2295 p2946 p2952 p3204 p3309 p3568 p3987 p4566 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73416 : p3568 ∨ p2295)
    (h48196 : (¬ p2952) ∨ (¬ p3204) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4566))
    : p2946 ∨ (¬ p3309) ∨ (¬ p3204) ∨ (¬ p4566) ∨ p2295 ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4566 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48196 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step85261 (p2088 p2177 p2255 p2331 p2474 p2528 p2662 p2727 p3309 p3857 p4111 p4319 p4438 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73480 : p3857 ∨ p2088)
    (h64098 : (¬ p2177) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2474) ∨ (¬ p2528) ∨ (¬ p2662) ∨ (¬ p3309) ∨ (¬ p3857) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p4438))
    : (¬ p3309) ∨ (¬ p4319) ∨ (¬ p2528) ∨ (¬ p2255) ∨ p2727 ∨ (¬ p4438) ∨ (¬ p2474) ∨ (¬ p2177) ∨ p2088 ∨ (¬ p2662) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2474 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h64098 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (False.elim (r9 u5)))))))))))))))))))))))

theorem step85262 (p2662 p3016 p3309 p3389 p3540 p3921 p3923 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h47064 : (¬ p2662) ∨ (¬ p3016) ∨ (¬ p3309) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p3923))
    : (¬ p3309) ∨ (¬ p3921) ∨ (¬ p2662) ∨ p3389 ∨ (¬ p3016) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47064 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step85266 (p2230 p2274 p2406 p2505 p3097 p3238 p3309 p4079 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73374 : p3238 ∨ p2406)
    (h46973 : (¬ p2230) ∨ (¬ p2505) ∨ (¬ p3097) ∨ (¬ p3238) ∨ (¬ p3309) ∨ (¬ p4079))
    : (¬ p3309) ∨ (¬ p2505) ∨ p2274 ∨ p2406 ∨ (¬ p2230) ∨ (¬ p4079) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46973 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step85272 (p2307 p2313 p2608 p3309 p4866 p5015 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h48075 : (¬ p2313) ∨ (¬ p2608) ∨ (¬ p3309) ∨ (¬ p4866) ∨ (¬ p5015))
    : (¬ p3309) ∨ (¬ p5015) ∨ (¬ p4866) ∨ (¬ p2608) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48075 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85273 (p2187 p2274 p3093 p3097 p3309 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h59851 : (¬ p2187) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3309))
    : (¬ p3309) ∨ p2274 ∨ (¬ p2187) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h59851 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step85276 (p2177 p2254 p3093 p3146 p3166 p3172 p3256 p3309 p4118 p4905 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73520 : p4118 ∨ p3256)
    (h48870 : (¬ p2177) ∨ (¬ p2254) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3172) ∨ (¬ p3309) ∨ (¬ p4118) ∨ (¬ p4905))
    : p3166 ∨ p3256 ∨ (¬ p4905) ∨ (¬ p2177) ∨ (¬ p3146) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p2254) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48870 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step85280 (p2505 p2553 p2573 p2579 p2588 p3309 p5191 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73274 : p2579 ∨ p2573)
    (h47474 : (¬ p2505) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3309) ∨ (¬ p5191))
    : (¬ p3309) ∨ p2553 ∨ p2573 ∨ (¬ p5191) ∨ (¬ p2505) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47474 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85283 (p2241 p2396 p2449 p3309 p3947 p4759 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h43087 : (¬ p2241) ∨ (¬ p2396) ∨ (¬ p3309) ∨ (¬ p3947) ∨ (¬ p4759))
    : (¬ p3309) ∨ (¬ p2396) ∨ (¬ p4759) ∨ (¬ p2241) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43087 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85287 (p2177 p2311 p2341 p3309 p3551 p5018 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h41725 : (¬ p2177) ∨ (¬ p2311) ∨ (¬ p3309) ∨ (¬ p3551) ∨ (¬ p5018))
    : p2341 ∨ (¬ p3309) ∨ (¬ p2311) ∨ (¬ p5018) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5018 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41725 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85296 (p2264 p2312 p2881 p3309 p3570 p4155 p4204 p4518 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h60908 : (¬ p2264) ∨ (¬ p2312) ∨ (¬ p3309) ∨ (¬ p3570) ∨ (¬ p4155) ∨ (¬ p4204) ∨ (¬ p4518))
    : (¬ p3309) ∨ (¬ p2264) ∨ (¬ p4204) ∨ (¬ p4155) ∨ (¬ p4518) ∨ (¬ p2312) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h60908 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step85297 (p2264 p2685 p2696 p3093 p3246 p3309 p3365 p3553 p3572 p4275 p4668 p4736 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h73410 : p3553 ∨ p2264)
    (h73390 : p3365 ∨ p2696)
    (h60453 : (¬ p3093) ∨ (¬ p3246) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4275) ∨ (¬ p4668) ∨ (¬ p4736))
    : (¬ p3246) ∨ (¬ p3309) ∨ (¬ p4275) ∨ (¬ p3093) ∨ p2685 ∨ p2264 ∨ (¬ p4668) ∨ p2696 ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h60453 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step85298 (p2264 p2312 p2341 p3309 p3553 p4067 p4761 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h42488 : (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3309) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4761))
    : (¬ p2341) ∨ (¬ p3309) ∨ (¬ p4761) ∨ p2264 ∨ (¬ p4067) ∨ (¬ p2312) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42488 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step85300 (p2274 p2331 p2630 p2797 p2810 p2963 p3093 p3097 p3309 p3366 p3379 p3452 p4236 p4376 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73394 : p3452 ∨ p3379)
    (h73338 : p2963 ∨ p2331)
    (h73352 : p3097 ∨ p2274)
    (h58003 : (¬ p2797) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p4236) ∨ (¬ p4376))
    : (¬ p3309) ∨ (¬ p2797) ∨ (¬ p3366) ∨ p2630 ∨ p3379 ∨ p2331 ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p3093) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h58003 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step85301 (p2241 p2247 p2274 p3093 p3097 p3309 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73352 : p3097 ∨ p2274)
    (h46476 : (¬ p2247) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3309))
    : p2241 ∨ (¬ p3309) ∨ (¬ p3093) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46476 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step85302 (p2177 p2241 p2247 p3093 p3309 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h45442 : (¬ p2177) ∨ (¬ p2247) ∨ (¬ p3093) ∨ (¬ p3309))
    : p2241 ∨ (¬ p3309) ∨ (¬ p2177) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45442 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step85303 (p2241 p2247 p2307 p2313 p3093 p3309 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73238 : p2313 ∨ p2307)
    (h59915 : (¬ p2247) ∨ (¬ p2313) ∨ (¬ p3093) ∨ (¬ p3309))
    : p2241 ∨ (¬ p3309) ∨ (¬ p3093) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59915 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step85305 (p2331 p3166 p3172 p3309 p4319 p4769 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h71619 : (¬ p4769) ∨ (¬ p3172) ∨ (¬ p4319) ∨ (¬ p3309) ∨ (¬ p2331))
    : p3166 ∨ (¬ p3309) ∨ (¬ p4319) ∨ (¬ p4769) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71619 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85306 (p2177 p2230 p2589 p2850 p3093 p3309 p3641 p3874 p4438 p5193 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73484 : p3874 ∨ p3641)
    (h62817 : (¬ p2177) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3874) ∨ (¬ p4438) ∨ (¬ p5193))
    : (¬ p3309) ∨ (¬ p2177) ∨ (¬ p5193) ∨ (¬ p2850) ∨ (¬ p3093) ∨ (¬ p4438) ∨ p2230 ∨ p3641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u9 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62817 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step85307 (p2363 p3073 p3309 p4261 p4371 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h71620 : (¬ p4371) ∨ (¬ p4261) ∨ (¬ p2363) ∨ (¬ p3309))
    : (¬ p3309) ∨ p3073 ∨ (¬ p4371) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71620 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step85310 (p2177 p2255 p2331 p2957 p2992 p3051 p3246 p3309 p3556 p3662 p3690 p4319 p4666 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h73440 : p3662 ∨ p2992)
    (h59138 : (¬ p2177) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2957) ∨ (¬ p3309) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p4319) ∨ (¬ p4666))
    : (¬ p3309) ∨ (¬ p2331) ∨ (¬ p4666) ∨ p3246 ∨ (¬ p2177) ∨ p3051 ∨ (¬ p2957) ∨ (¬ p2255) ∨ p2992 ∨ (¬ p4319) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h59138 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step85312 (p2253 p2274 p2946 p2992 p3097 p3309 p3662 p4759 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73352 : p3097 ∨ p2274)
    (h47217 : (¬ p2253) ∨ (¬ p2946) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3662) ∨ (¬ p4759))
    : (¬ p3309) ∨ p2992 ∨ p2274 ∨ (¬ p2946) ∨ (¬ p4759) ∨ (¬ p2253) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47217 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step85313 (p2363 p2459 p3093 p3309 p3325 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h56034 : (¬ p2363) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3325) ∨ (¬ p4348))
    : (¬ p3309) ∨ (¬ p3093) ∨ (¬ p2363) ∨ (¬ p3325) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56034 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85316 (p2396 p2528 p2534 p2598 p3055 p3093 p3309 p3641 p3874 p3950 p4736 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73484 : p3874 ∨ p3641)
    (h73350 : p3055 ∨ p2598)
    (h49622 : (¬ p2396) ∨ (¬ p2534) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4736))
    : p2528 ∨ (¬ p3309) ∨ p3641 ∨ (¬ p3950) ∨ (¬ p3093) ∨ (¬ p4736) ∨ p2598 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49622 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step85321 (p2396 p2663 p2774 p3166 p3172 p3256 p3309 p3363 p3367 p3585 p3918 p3950 p4118 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73520 : p4118 ∨ p3256)
    (h73428 : p3585 ∨ p3367)
    (h71622 : (¬ p3918) ∨ (¬ p4118) ∨ (¬ p3363) ∨ (¬ p2663) ∨ (¬ p2774) ∨ (¬ p3309) ∨ (¬ p2396) ∨ (¬ p3585) ∨ (¬ p3172) ∨ (¬ p3950))
    : p3166 ∨ p3256 ∨ (¬ p3918) ∨ (¬ p2663) ∨ p3367 ∨ (¬ p2774) ∨ (¬ p3363) ∨ (¬ p2396) ∨ (¬ p3309) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71622 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step85323 (p2177 p3125 p3309 p3319 p4026 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h62811 : (¬ p2177) ∨ (¬ p3125) ∨ (¬ p3309) ∨ (¬ p4026))
    : (¬ p3309) ∨ p3319 ∨ (¬ p3125) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62811 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85327 (p2685 p2807 p3005 p3093 p3309 p3366 p3379 p3414 p3452 p3877 p4236 p4376 p4769 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73394 : p3452 ∨ p3379)
    (h73392 : p3414 ∨ p2807)
    (h71623 : (¬ p3877) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3309) ∨ (¬ p3452) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p2685) ∨ (¬ p4769))
    : p3005 ∨ p3379 ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p2685) ∨ p2807 ∨ (¬ p4376) ∨ (¬ p4236) ∨ (¬ p4769) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71623 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step85328 (p2307 p2313 p2386 p2505 p3016 p3309 p3574 p4814 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73238 : p2313 ∨ p2307)
    (h62838 : (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2505) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p4814))
    : (¬ p3309) ∨ p3016 ∨ p2307 ∨ (¬ p2386) ∨ (¬ p4814) ∨ (¬ p2505) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62838 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step85330 (p3246 p3309 p3319 p4026 p4396 p4559 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h60189 : (¬ p3246) ∨ (¬ p3309) ∨ (¬ p4026) ∨ (¬ p4396) ∨ (¬ p4559))
    : (¬ p3246) ∨ p3319 ∨ (¬ p4396) ∨ (¬ p3309) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60189 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85331 (p2255 p2331 p2662 p2727 p3276 p3309 p3346 p3791 p4111 p4319 p4425 p4826 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73518 : p4111 ∨ p2727)
    (h60342 : (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3309) ∨ (¬ p3346) ∨ (¬ p3791) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p4425) ∨ (¬ p4826))
    : (¬ p3791) ∨ (¬ p4319) ∨ (¬ p3309) ∨ (¬ p4826) ∨ p3276 ∨ (¬ p2255) ∨ (¬ p2331) ∨ p2727 ∨ (¬ p3346) ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h60342 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step85333 (p3309 p3461 p3707 p4321 p4430 p4620 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h49078 : (¬ p3309) ∨ (¬ p3461) ∨ (¬ p4321) ∨ (¬ p4430) ∨ (¬ p4620))
    : p3707 ∨ (¬ p3461) ∨ (¬ p4620) ∨ (¬ p4430) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4430 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49078 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85339 (p2352 p2553 p2588 p3093 p3309 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h45408 : (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3093) ∨ (¬ p3309))
    : (¬ p3309) ∨ p2553 ∨ (¬ p3093) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45408 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step85342 (p2396 p2737 p2743 p2774 p3166 p3172 p3256 p3309 p3361 p3918 p3950 p4118 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73298 : p2743 ∨ p2737)
    (h73356 : p3172 ∨ p3166)
    (h71624 : (¬ p3918) ∨ (¬ p2743) ∨ (¬ p3309) ∨ (¬ p3950) ∨ (¬ p3172) ∨ (¬ p3361) ∨ (¬ p4118) ∨ (¬ p2396) ∨ (¬ p2774))
    : (¬ p2396) ∨ (¬ p3309) ∨ p3256 ∨ (¬ p3361) ∨ (¬ p2774) ∨ (¬ p3950) ∨ p2737 ∨ (¬ p3918) ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71624 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step85345 (p2396 p2598 p2911 p3055 p3093 p3201 p3309 p3644 p3876 p4668 p4736 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h51268 : (¬ p2396) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4668) ∨ (¬ p4736))
    : (¬ p3309) ∨ (¬ p2396) ∨ (¬ p4736) ∨ p2911 ∨ (¬ p4668) ∨ p3201 ∨ (¬ p3093) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51268 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step85346 (p2396 p2598 p2850 p2982 p3055 p3093 p3309 p3684 p3951 p4736 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73442 : p3684 ∨ p2850)
    (h73350 : p3055 ∨ p2598)
    (h49594 : (¬ p2396) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3684) ∨ (¬ p3951) ∨ (¬ p4736) ∨ (¬ p4948))
    : (¬ p3309) ∨ (¬ p2396) ∨ (¬ p3951) ∨ (¬ p4736) ∨ p2982 ∨ p2850 ∨ p2598 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49594 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step85348 (p2383 p2427 p2598 p2850 p3055 p3309 p3684 p3923 p4235 p4559 p4736 p5020 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73536 : p4235 ∨ p2427)
    (h73442 : p3684 ∨ p2850)
    (h57029 : (¬ p2383) ∨ (¬ p3055) ∨ (¬ p3309) ∨ (¬ p3684) ∨ (¬ p3923) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4736) ∨ (¬ p5020))
    : (¬ p3309) ∨ (¬ p2383) ∨ (¬ p4559) ∨ p2598 ∨ p2427 ∨ (¬ p3923) ∨ p2850 ∨ (¬ p4736) ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h57029 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step85349 (p2177 p2417 p2598 p3055 p3093 p3201 p3309 p3876 p4278 p4666 p4736 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h61865 : (¬ p2177) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4736))
    : (¬ p3309) ∨ p2417 ∨ (¬ p4736) ∨ (¬ p4666) ∨ p3201 ∨ (¬ p2177) ∨ (¬ p3093) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h61865 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step85350 (p2396 p2417 p3093 p3309 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h43572 : (¬ p2396) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p4278))
    : (¬ p3309) ∨ p2417 ∨ (¬ p2396) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43572 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85355 (p2553 p2588 p3093 p3309 p3379 p3452 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73394 : p3452 ∨ p3379)
    (h43348 : (¬ p2588) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3452))
    : (¬ p3309) ∨ (¬ p3093) ∨ p2553 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43348 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85361 (p2098 p2104 p2177 p2528 p3093 p3309 p3609 p4340 p4438 p4736 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h73558 : p4340 ∨ p3609)
    (h60113 : (¬ p2104) ∨ (¬ p2177) ∨ (¬ p2528) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p4340) ∨ (¬ p4438) ∨ (¬ p4736))
    : (¬ p3309) ∨ (¬ p3093) ∨ (¬ p2528) ∨ (¬ p2177) ∨ (¬ p4736) ∨ p2098 ∨ (¬ p4438) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h60113 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step85363 (p2274 p2668 p3097 p3309 p3923 p4560 : Prop)
    (h72955 : p4560)
    (h73352 : p3097 ∨ p2274)
    (h50672 : (¬ p2668) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4560))
    : (¬ p3309) ∨ (¬ p2668) ∨ (¬ p3923) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4560 := h72955;
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50672 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85366 (p2307 p2313 p2505 p2608 p3309 p4376 p5015 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h53487 : (¬ p2313) ∨ (¬ p2505) ∨ (¬ p2608) ∨ (¬ p3309) ∨ (¬ p4376) ∨ (¬ p5015))
    : (¬ p3309) ∨ (¬ p5015) ∨ (¬ p2505) ∨ (¬ p2608) ∨ (¬ p4376) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h53487 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step85375 (p2341 p4589 p4592 : Prop)
    (h73654 : p4589 ∨ (¬ p2341))
    (h7300 : (¬ p4589) ∨ p4592)
    : (¬ p2341) ∨ p4592 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4592) := (fun h => hn (Or.inr h));
    let u2 : p4589 := (Or.elim h73654 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7300 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step85378 (p2156 p3646 p4518 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h46069 : (¬ p3646) ∨ p4518)
    : p2156 ∨ p4518 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4518) := (fun h => hn (Or.inr h));
    let u2 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46069 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step85379 (p2156 p3646 p4401 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h47395 : (¬ p3646) ∨ p4401)
    : p2156 ∨ p4401 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4401) := (fun h => hn (Or.inr h));
    let u2 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47395 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step85380 (p2156 p3646 p4489 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h48273 : (¬ p3646) ∨ p4489)
    : p2156 ∨ p4489 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4489) := (fun h => hn (Or.inr h));
    let u2 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48273 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step85382 (p2156 p2284 p3051 p3246 p3646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h46276 : (¬ p2284) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3646))
    : (¬ p3051) ∨ (¬ p2284) ∨ (¬ p3246) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46276 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85383 (p2156 p2563 p2881 p3051 p3646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h54943 : (¬ p2563) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3646))
    : (¬ p3051) ∨ p2156 ∨ (¬ p2881) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54943 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85384 (p2156 p2284 p2881 p3051 p3646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h57971 : (¬ p2284) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3646))
    : (¬ p3051) ∨ (¬ p2284) ∨ p2156 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57971 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85385 (p2156 p2553 p2588 p3051 p3646 p3958 p4140 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73436 : p3646 ∨ p2156)
    (h53078 : (¬ p2588) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3958) ∨ (¬ p4140))
    : (¬ p3051) ∨ (¬ p4140) ∨ p2553 ∨ p2156 ∨ (¬ p3958) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53078 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85386 (p2156 p2177 p2563 p3051 p3646 p4140 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h61941 : (¬ p2177) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4140))
    : (¬ p3051) ∨ (¬ p4140) ∨ p2156 ∨ (¬ p2177) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61941 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85387 (p2156 p2563 p2881 p2891 p3645 p3646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h54942 : (¬ p2563) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3645) ∨ (¬ p3646))
    : (¬ p2891) ∨ p2156 ∨ (¬ p2881) ∨ (¬ p3645) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54942 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85388 (p2156 p2264 p2274 p2396 p2608 p3037 p3097 p3399 p3645 p3646 p3954 p4107 p4666 p4877 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73514 : p4107 ∨ p2396)
    (h73352 : p3097 ∨ p2274)
    (h73436 : p3646 ∨ p2156)
    (h62242 : (¬ p2264) ∨ (¬ p3037) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p4877))
    : p2608 ∨ p2396 ∨ (¬ p3645) ∨ p2274 ∨ p2156 ∨ (¬ p4877) ∨ (¬ p3399) ∨ (¬ p4666) ∨ (¬ p3037) ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62242 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step85389 (p2156 p2427 p2563 p3246 p3646 p3690 p3904 p4235 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73536 : p4235 ∨ p2427)
    (h73436 : p3646 ∨ p2156)
    (h62769 : (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3690) ∨ (¬ p3904) ∨ (¬ p4235))
    : p3246 ∨ p2427 ∨ (¬ p3904) ∨ (¬ p2563) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62769 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step85390 (p2156 p3246 p3516 p3646 p3690 p4558 p4988 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73436 : p3646 ∨ p2156)
    (h62280 : (¬ p3516) ∨ (¬ p3646) ∨ (¬ p3690) ∨ (¬ p4558) ∨ (¬ p4988))
    : (¬ p3516) ∨ p3246 ∨ (¬ p4558) ∨ (¬ p4988) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62280 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85391 (p2156 p2220 p2363 p2563 p3646 p4441 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h52293 : (¬ p2220) ∨ (¬ p2363) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p4441))
    : (¬ p4441) ∨ p2156 ∨ (¬ p2363) ∨ (¬ p2563) ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52293 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step85394 (p2156 p2220 p2553 p2588 p3646 p3958 p4119 p4140 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73436 : p3646 ∨ p2156)
    (h59154 : (¬ p2220) ∨ (¬ p2588) ∨ (¬ p3646) ∨ (¬ p3958) ∨ (¬ p4119) ∨ (¬ p4140))
    : (¬ p4140) ∨ p2553 ∨ (¬ p2220) ∨ p2156 ∨ (¬ p4119) ∨ (¬ p3958) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4140 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59154 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step85395 (p2156 p3051 p3125 p3461 p3646 p3744 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73436 : p3646 ∨ p2156)
    (h73454 : p3744 ∨ p3125)
    (h45155 : (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4191))
    : (¬ p3051) ∨ p3461 ∨ p2156 ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45155 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85396 (p2143 p2156 p2563 p2839 p3367 p3583 p3646 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73436 : p3646 ∨ p2156)
    (h45384 : (¬ p2143) ∨ (¬ p2563) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3646))
    : (¬ p3367) ∨ p2839 ∨ (¬ p2143) ∨ (¬ p2563) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45384 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step85398 (p2143 p2156 p2839 p3125 p3461 p3583 p3646 p3744 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73454 : p3744 ∨ p3125)
    (h73424 : p3583 ∨ p2839)
    (h73436 : p3646 ∨ p2156)
    (h43858 : (¬ p2143) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4191))
    : p3461 ∨ p3125 ∨ (¬ p2143) ∨ p2839 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43858 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85399 (p2156 p2220 p2274 p2396 p3097 p3646 p4107 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73352 : p3097 ∨ p2274)
    (h73514 : p4107 ∨ p2396)
    (h43851 : (¬ p2220) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4107))
    : p2156 ∨ (¬ p2220) ∨ p2274 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43851 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step85401 (p2156 p2396 p2860 p2870 p3646 p4107 p4244 p4275 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73514 : p4107 ∨ p2396)
    (h73436 : p3646 ∨ p2156)
    (h53109 : (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4244) ∨ (¬ p4275))
    : p2870 ∨ p2396 ∨ (¬ p2860) ∨ (¬ p4275) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53109 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85405 (p2156 p2187 p2220 p2363 p3646 p3989 p4347 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73560 : p4347 ∨ p2363)
    (h73502 : p3989 ∨ p2187)
    (h53199 : (¬ p2220) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4347))
    : (¬ p2220) ∨ p2156 ∨ p2363 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53199 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85406 (p2156 p2187 p2352 p3646 p3660 p3989 p4533 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73502 : p3989 ∨ p2187)
    (h40917 : (¬ p2352) ∨ (¬ p3646) ∨ (¬ p3660) ∨ (¬ p3989) ∨ (¬ p4533))
    : (¬ p2352) ∨ p2156 ∨ p2187 ∨ (¬ p4533) ∨ (¬ p3660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h40917 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85407 (p2156 p2396 p2563 p3516 p3646 p4107 p4988 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73436 : p3646 ∨ p2156)
    (h45646 : (¬ p2563) ∨ (¬ p3516) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4988))
    : (¬ p3516) ∨ p2396 ∨ (¬ p4988) ∨ p2156 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45646 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85408 (p2156 p2274 p2396 p2957 p2992 p3097 p3646 p3662 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73440 : p3662 ∨ p2992)
    (h73436 : p3646 ∨ p2156)
    (h73352 : p3097 ∨ p2274)
    (h43800 : (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p4107))
    : p2396 ∨ p2992 ∨ p2156 ∨ (¬ p2957) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43800 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85410 (p2156 p2274 p2396 p2957 p3097 p3136 p3646 p4107 p4315 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73352 : p3097 ∨ p2274)
    (h73436 : p3646 ∨ p2156)
    (h73550 : p4315 ∨ p3136)
    (h43803 : (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4315))
    : p2396 ∨ p2274 ∨ (¬ p2957) ∨ p2156 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43803 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step85412 (p2156 p2284 p2363 p3156 p3497 p3646 p4347 p4506 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73400 : p3497 ∨ p3156)
    (h73436 : p3646 ∨ p2156)
    (h45284 : (¬ p2284) ∨ (¬ p3497) ∨ (¬ p3646) ∨ (¬ p4347) ∨ (¬ p4506))
    : p2363 ∨ (¬ p2284) ∨ p3156 ∨ p2156 ∨ (¬ p4506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45284 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85413 (p2156 p2220 p2284 p3646 p3969 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h46277 : (¬ p2220) ∨ (¬ p2284) ∨ (¬ p3646) ∨ (¬ p3969))
    : (¬ p3969) ∨ (¬ p2220) ∨ p2156 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46277 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step85416 (p2156 p2177 p2192 p2299 p2341 p3646 p4988 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73234 : p2299 ∨ p2177)
    (h46388 : (¬ p2192) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p3646) ∨ (¬ p4988))
    : (¬ p2341) ∨ (¬ p2192) ∨ p2156 ∨ p2177 ∨ (¬ p4988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46388 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85419 (p2156 p2220 p2274 p3097 p3646 p4405 p4441 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73352 : p3097 ∨ p2274)
    (h42531 : (¬ p2220) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4405) ∨ (¬ p4441))
    : (¬ p2220) ∨ p2156 ∨ p2274 ∨ (¬ p4405) ∨ (¬ p4441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42531 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85421 (p2156 p2187 p2363 p2608 p2707 p3434 p3646 p3950 p3989 p4347 p4524 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h72962 : p4524)
    (h73436 : p3646 ∨ p2156)
    (h73502 : p3989 ∨ p2187)
    (h63956 : (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p4347) ∨ (¬ p4524))
    : (¬ p2608) ∨ p2363 ∨ (¬ p3950) ∨ (¬ p2707) ∨ p2156 ∨ (¬ p3434) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4524 := h72962;
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63956 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step85424 (p2156 p2396 p2563 p3051 p3646 p4140 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h54932 : (¬ p2396) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4140))
    : (¬ p3051) ∨ (¬ p2396) ∨ (¬ p2563) ∨ p2156 ∨ (¬ p4140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54932 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85425 (p2156 p2563 p3051 p3246 p3646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h53674 : (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3646))
    : (¬ p3051) ∨ p2156 ∨ (¬ p3246) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53674 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85437 (p2156 p2187 p2363 p2440 p3646 p3989 p4031 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73436 : p3646 ∨ p2156)
    (h73502 : p3989 ∨ p2187)
    (h45124 : (¬ p2440) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4031) ∨ (¬ p4347))
    : p2363 ∨ (¬ p4031) ∨ p2156 ∨ (¬ p2440) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45124 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85438 (p2156 p2274 p3097 p3212 p3646 p4624 p5045 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73436 : p3646 ∨ p2156)
    (h51261 : (¬ p3097) ∨ (¬ p3212) ∨ (¬ p3646) ∨ (¬ p4624) ∨ (¬ p5045))
    : (¬ p3212) ∨ (¬ p5045) ∨ p2274 ∨ p2156 ∨ (¬ p4624) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51261 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85441 (p2156 p2284 p2427 p3051 p3646 p4235 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73536 : p4235 ∨ p2427)
    (h46133 : (¬ p2284) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4235))
    : (¬ p3051) ∨ (¬ p2284) ∨ p2156 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46133 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85443 (p2156 p2220 p2284 p2373 p3646 p3880 p4705 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73490 : p3880 ∨ p2373)
    (h63320 : (¬ p2220) ∨ (¬ p2284) ∨ (¬ p3646) ∨ (¬ p3880) ∨ (¬ p4705))
    : (¬ p2220) ∨ p2156 ∨ p2373 ∨ (¬ p2284) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h63320 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85444 (p2156 p2459 p2881 p3051 p3646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h45511 : (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3646))
    : (¬ p2881) ∨ (¬ p3051) ∨ p2156 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45511 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85445 (p2156 p2177 p2220 p2299 p2563 p3646 p4042 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73234 : p2299 ∨ p2177)
    (h47088 : (¬ p2220) ∨ (¬ p2299) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p4042))
    : (¬ p2220) ∨ p2156 ∨ (¬ p2563) ∨ p2177 ∨ (¬ p4042) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47088 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85449 (p2156 p2563 p3389 p3646 p3904 p4646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h41336 : (¬ p2563) ∨ (¬ p3389) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4646))
    : (¬ p3389) ∨ p2156 ∨ (¬ p2563) ∨ (¬ p4646) ∨ (¬ p3904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41336 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85451 (p2156 p2563 p2850 p3646 p3904 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h71627 : (¬ p2850) ∨ (¬ p3904) ∨ (¬ p3646) ∨ (¬ p2563))
    : p2156 ∨ (¬ p2850) ∨ (¬ p2563) ∨ (¬ p3904) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71627 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step85453 (p2156 p2284 p2737 p2743 p2950 p3156 p3361 p3497 p3646 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73298 : p2743 ∨ p2737)
    (h73436 : p3646 ∨ p2156)
    (h54028 : (¬ p2284) ∨ (¬ p2743) ∨ (¬ p2950) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3646))
    : p3156 ∨ (¬ p2950) ∨ p2737 ∨ (¬ p3361) ∨ p2156 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54028 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u8)))))))))))))

theorem step85454 (p2143 p2156 p2187 p2363 p2839 p3583 p3646 p3989 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73502 : p3989 ∨ p2187)
    (h73436 : p3646 ∨ p2156)
    (h73424 : p3583 ∨ p2839)
    (h43799 : (¬ p2143) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4347))
    : (¬ p2143) ∨ p2363 ∨ p2187 ∨ p2156 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43799 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85457 (p2143 p2156 p2284 p2737 p2839 p3583 p3646 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73436 : p3646 ∨ p2156)
    (h45929 : (¬ p2143) ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p3583) ∨ (¬ p3646))
    : (¬ p2284) ∨ (¬ p2737) ∨ p2839 ∨ p2156 ∨ (¬ p2143) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45929 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step85458 (p2143 p2156 p2177 p2839 p2881 p3570 p3583 p3646 p4204 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73418 : p3570 ∨ p2881)
    (h73436 : p3646 ∨ p2156)
    (h50296 : (¬ p2143) ∨ (¬ p2177) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p4204))
    : p2839 ∨ p2881 ∨ (¬ p2177) ∨ p2156 ∨ (¬ p4204) ∨ (¬ p2143) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50296 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step85462 (p2122 p2156 p3125 p3483 p3646 p3744 p3822 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73472 : p3822 ∨ p2122)
    (h73436 : p3646 ∨ p2156)
    (h61620 : (¬ p3483) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3822))
    : (¬ p3483) ∨ p3125 ∨ p2122 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61620 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85464 (p2156 p2177 p2274 p2299 p2957 p3097 p3136 p3646 p4315 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73436 : p3646 ∨ p2156)
    (h73234 : p2299 ∨ p2177)
    (h73550 : p4315 ∨ p3136)
    (h47628 : (¬ p2299) ∨ (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4315))
    : (¬ p2957) ∨ p2274 ∨ p2156 ∨ p2177 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47628 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step85467 (p2143 p2156 p2177 p2274 p2299 p2839 p3097 p3583 p3646 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73436 : p3646 ∨ p2156)
    (h73234 : p2299 ∨ p2177)
    (h73352 : p3097 ∨ p2274)
    (h43849 : (¬ p2143) ∨ (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p3646))
    : p2839 ∨ p2156 ∨ (¬ p2143) ∨ p2177 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43849 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step85470 (p2156 p2341 p2881 p3570 p3646 p4558 p4988 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73436 : p3646 ∨ p2156)
    (h52565 : (¬ p2341) ∨ (¬ p3570) ∨ (¬ p3646) ∨ (¬ p4558) ∨ (¬ p4988))
    : (¬ p4988) ∨ (¬ p2341) ∨ (¬ p4558) ∨ p2881 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4988 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52565 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step85475 (p2156 p3051 p3125 p3646 p3744 p4140 p4620 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73436 : p3646 ∨ p2156)
    (h41348 : (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4140) ∨ (¬ p4620))
    : (¬ p3051) ∨ p3125 ∨ (¬ p4140) ∨ p2156 ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41348 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85476 (p2136 p2156 p2187 p2363 p2459 p3646 p3989 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73502 : p3989 ∨ p2187)
    (h73436 : p3646 ∨ p2156)
    (h58719 : (¬ p2136) ∨ (¬ p2459) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4347))
    : p2363 ∨ (¬ p2136) ∨ p2187 ∨ p2156 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58719 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85479 (p2132 p2138 p2156 p2284 p3136 p3646 p5050 : Prop)
    (h73894 : p5050 ∨ (¬ p3136))
    (h73436 : p3646 ∨ p2156)
    (h73214 : p2138 ∨ p2132)
    (h66786 : (¬ p5050) ∨ (¬ p2284) ∨ (¬ p2138) ∨ (¬ p3646))
    : (¬ p2284) ∨ (¬ p3136) ∨ p2156 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5050 := (Or.elim h73894 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h66786 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85480 (p2122 p2140 p2156 p2274 p3097 p3646 p3985 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73352 : p3097 ∨ p2274)
    (h50858 : (¬ p2122) ∨ (¬ p2140) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3985))
    : (¬ p2122) ∨ (¬ p3985) ∨ (¬ p2140) ∨ p2156 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50858 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85481 (p2156 p2563 p3355 p3646 p3904 p4953 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h41693 : (¬ p2563) ∨ (¬ p3355) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4953))
    : (¬ p3355) ∨ p2156 ∨ (¬ p2563) ∨ (¬ p4953) ∨ (¬ p3904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41693 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85485 (p2156 p2440 p2542 p2563 p2659 p3646 p3904 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73270 : p2542 ∨ p2440)
    (h41572 : (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2659) ∨ (¬ p3646) ∨ (¬ p3904))
    : p2156 ∨ p2440 ∨ (¬ p2563) ∨ (¬ p2659) ∨ (¬ p3904) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41572 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85486 (p2156 p2440 p2542 p2563 p3363 p3646 p3904 p4750 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73436 : p3646 ∨ p2156)
    (h49794 : (¬ p2542) ∨ (¬ p2563) ∨ (¬ p3363) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4750))
    : p2440 ∨ p2156 ∨ (¬ p4750) ∨ (¬ p2563) ∨ (¬ p3904) ∨ (¬ p3363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49794 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step85487 (p2156 p2563 p2982 p3461 p3646 p4033 p4191 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73436 : p3646 ∨ p2156)
    (h73530 : p4191 ∨ p3461)
    (h57600 : (¬ p2563) ∨ (¬ p3646) ∨ (¬ p4033) ∨ (¬ p4191) ∨ (¬ p4948))
    : p2982 ∨ p2156 ∨ (¬ p4033) ∨ (¬ p2563) ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57600 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85491 (p2156 p2230 p2563 p3369 p3646 p5190 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h41218 : (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p5190))
    : (¬ p2563) ∨ (¬ p2230) ∨ p2156 ∨ (¬ p5190) ∨ (¬ p3369) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41218 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85492 (p2156 p2284 p2982 p3646 p3680 p4031 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h46275 : (¬ p2284) ∨ (¬ p2982) ∨ (¬ p3646) ∨ (¬ p3680) ∨ (¬ p4031))
    : (¬ p2284) ∨ (¬ p3680) ∨ (¬ p4031) ∨ p2156 ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46275 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85493 (p2156 p2668 p3125 p3323 p3324 p3646 p3744 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73386 : p3324 ∨ p2668)
    (h73436 : p3646 ∨ p2156)
    (h60051 : (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3646) ∨ (¬ p3744))
    : (¬ p3323) ∨ p3125 ∨ p2668 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60051 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85495 (p2156 p3125 p3323 p3645 p3646 p3744 p4336 p4957 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73454 : p3744 ∨ p3125)
    (h42208 : (¬ p3323) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4336) ∨ (¬ p4957))
    : (¬ p4336) ∨ (¬ p3323) ∨ (¬ p4957) ∨ p2156 ∨ p3125 ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4336 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42208 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step85500 (p2156 p2957 p2992 p3125 p3461 p3646 p3662 p3744 p4191 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73530 : p4191 ∨ p3461)
    (h73436 : p3646 ∨ p2156)
    (h73454 : p3744 ∨ p3125)
    (h57460 : (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p3744) ∨ (¬ p4191))
    : p2992 ∨ p3461 ∨ p2156 ∨ p3125 ∨ (¬ p2957) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57460 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step85502 (p2156 p2608 p3125 p3399 p3461 p3645 p3646 p3744 p3954 p4075 p4191 p4826 p4877 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73454 : p3744 ∨ p3125)
    (h73530 : p4191 ∨ p3461)
    (h73436 : p3646 ∨ p2156)
    (h58422 : (¬ p3399) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3954) ∨ (¬ p4075) ∨ (¬ p4191) ∨ (¬ p4826) ∨ (¬ p4877))
    : (¬ p4075) ∨ p2608 ∨ p3125 ∨ p3461 ∨ (¬ p3399) ∨ p2156 ∨ (¬ p4877) ∨ (¬ p4826) ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4075 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58422 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step85503 (p2156 p2957 p3125 p3136 p3461 p3646 p3744 p4191 p4315 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73454 : p3744 ∨ p3125)
    (h73550 : p4315 ∨ p3136)
    (h73436 : p3646 ∨ p2156)
    (h57290 : (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4191) ∨ (¬ p4315))
    : p3461 ∨ (¬ p2957) ∨ p3125 ∨ p3136 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57290 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step85504 (p2098 p2156 p2252 p2598 p2748 p2950 p3055 p3125 p3461 p3646 p3744 p4019 p4191 p4749 p5119 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73454 : p3744 ∨ p3125)
    (h73436 : p3646 ∨ p2156)
    (h73350 : p3055 ∨ p2598)
    (h42159 : (¬ p2098) ∨ (¬ p2252) ∨ (¬ p2748) ∨ (¬ p2950) ∨ (¬ p3055) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4019) ∨ (¬ p4191) ∨ (¬ p4749) ∨ (¬ p5119))
    : (¬ p4019) ∨ p3461 ∨ p3125 ∨ (¬ p2098) ∨ (¬ p2748) ∨ (¬ p2252) ∨ (¬ p2950) ∨ (¬ p5119) ∨ p2156 ∨ p2598 ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u13 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u14 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h42159 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step85507 (p2156 p2284 p2950 p3286 p3646 p5039 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h58906 : (¬ p2284) ∨ (¬ p2950) ∨ (¬ p3286) ∨ (¬ p3646) ∨ (¬ p5039))
    : (¬ p3286) ∨ (¬ p2284) ∨ p2156 ∨ (¬ p2950) ∨ (¬ p5039) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5039 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58906 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85516 (p2156 p2254 p2284 p2901 p2911 p2950 p3399 p3527 p3644 p3646 p4277 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73436 : p3646 ∨ p2156)
    (h73434 : p3644 ∨ p2911)
    (h62374 : (¬ p2254) ∨ (¬ p2284) ∨ (¬ p2950) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p3646) ∨ (¬ p4277) ∨ (¬ p4320))
    : (¬ p2284) ∨ p2901 ∨ (¬ p3527) ∨ (¬ p2950) ∨ p2156 ∨ (¬ p2254) ∨ p2911 ∨ (¬ p3399) ∨ (¬ p4277) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62374 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step85517 (p2156 p2254 p2284 p2608 p2707 p2717 p2950 p3156 p3497 p3646 p4905 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73400 : p3497 ∨ p3156)
    (h55537 : (¬ p2254) ∨ (¬ p2284) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2950) ∨ (¬ p3497) ∨ (¬ p3646) ∨ (¬ p4905))
    : (¬ p2284) ∨ (¬ p2707) ∨ p2156 ∨ p3156 ∨ (¬ p2608) ∨ (¬ p2254) ∨ (¬ p2950) ∨ (¬ p2717) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55537 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step85518 (p2156 p2284 p2807 p2950 p3413 p3646 p4652 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h42258 : (¬ p2284) ∨ (¬ p2807) ∨ (¬ p2950) ∨ (¬ p3413) ∨ (¬ p3646) ∨ (¬ p4652))
    : (¬ p2284) ∨ (¬ p2950) ∨ (¬ p4652) ∨ (¬ p3413) ∨ p2156 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42258 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step85520 (p2156 p2563 p2982 p3646 p3904 p4322 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73436 : p3646 ∨ p2156)
    (h47470 : (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4322) ∨ (¬ p4948))
    : p2982 ∨ p2156 ∨ (¬ p3904) ∨ (¬ p2563) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47470 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85525 (p2156 p2284 p2440 p2542 p2573 p2579 p2659 p2911 p3016 p3413 p3646 p3872 p4705 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73270 : p2542 ∨ p2440)
    (h73436 : p3646 ∨ p2156)
    (h65915 : (¬ p2579) ∨ (¬ p2284) ∨ (¬ p2659) ∨ (¬ p3646) ∨ (¬ p4705) ∨ (¬ p2542) ∨ (¬ p3413) ∨ (¬ p2911) ∨ (¬ p3016) ∨ (¬ p3872))
    : (¬ p3872) ∨ (¬ p3413) ∨ p2573 ∨ (¬ p2284) ∨ (¬ p4705) ∨ p2440 ∨ (¬ p3016) ∨ (¬ p2911) ∨ (¬ p2659) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3872 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h65915 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step85526 (p2156 p2440 p3125 p3461 p3646 p3744 p4031 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73454 : p3744 ∨ p3125)
    (h73436 : p3646 ∨ p2156)
    (h61344 : (¬ p2440) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4031) ∨ (¬ p4191))
    : p3461 ∨ (¬ p4031) ∨ (¬ p2440) ∨ p3125 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61344 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85539 (p2156 p2331 p2651 p2946 p2949 p3646 : Prop)
    (h73328 : p2949 ∨ p2946)
    (h73436 : p3646 ∨ p2156)
    (h69653 : (¬ p3646) ∨ (¬ p2949) ∨ (¬ p2651) ∨ (¬ p2331))
    : p2946 ∨ (¬ p2331) ∨ (¬ p2651) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2949 := (Or.elim h73328 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69653 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step85541 (p2156 p2881 p2911 p3051 p3644 p3646 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73436 : p3646 ∨ p2156)
    (h60010 : (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3644) ∨ (¬ p3646))
    : (¬ p3051) ∨ p2911 ∨ p2156 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60010 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85542 (p2156 p2363 p2957 p2992 p3146 p3646 p3662 p3692 p3988 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73448 : p3692 ∨ p3146)
    (h73436 : p3646 ∨ p2156)
    (h49178 : (¬ p2363) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p3988))
    : p2992 ∨ p3146 ∨ p2156 ∨ (¬ p2957) ∨ (¬ p2363) ∨ (¬ p3988) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49178 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step85543 (p2136 p2156 p2246 p2363 p2417 p2437 p2651 p2744 p3146 p3366 p3646 p3657 p3692 p3988 p4503 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73436 : p3646 ∨ p2156)
    (h63744 : (¬ p2136) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3646) ∨ (¬ p3657) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4503))
    : (¬ p3657) ∨ (¬ p3366) ∨ p3146 ∨ (¬ p2363) ∨ (¬ p3988) ∨ (¬ p2651) ∨ p2156 ∨ (¬ p2437) ∨ (¬ p2417) ∨ (¬ p4503) ∨ (¬ p2136) ∨ (¬ p2246) ∨ (¬ p2744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u14 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63744 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u14))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u13))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u4))) (fun r11 => (False.elim (r11 u9)))))))))))))))))))))))))))

theorem step85544 (p2156 p2187 p2363 p2957 p2992 p3646 p3662 p3989 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73440 : p3662 ∨ p2992)
    (h73502 : p3989 ∨ p2187)
    (h73436 : p3646 ∨ p2156)
    (h43834 : (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p3989) ∨ (¬ p4347))
    : p2363 ∨ p2992 ∨ p2187 ∨ (¬ p2957) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43834 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85546 (p2156 p2187 p2363 p2957 p3136 p3646 p3989 p4315 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73550 : p4315 ∨ p3136)
    (h73502 : p3989 ∨ p2187)
    (h73436 : p3646 ∨ p2156)
    (h48932 : (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4315) ∨ (¬ p4347))
    : p2363 ∨ (¬ p2957) ∨ p3136 ∨ p2187 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48932 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85553 (p2145 p2156 p2284 p2761 p3115 p3276 p3355 p3362 p3646 p3951 p4208 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73436 : p3646 ∨ p2156)
    (h73534 : p4208 ∨ p3115)
    (h56797 : (¬ p2145) ∨ (¬ p2284) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3646) ∨ (¬ p3951) ∨ (¬ p4208) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3276) ∨ (¬ p3951) ∨ (¬ p2145) ∨ (¬ p3362) ∨ p2156 ∨ p3115 ∨ (¬ p2284) ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56797 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step85554 (p2156 p2220 p2553 p2588 p3646 p4203 p4405 p4441 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73282 : p2588 ∨ p2553)
    (h48815 : (¬ p2220) ∨ (¬ p2588) ∨ (¬ p3646) ∨ (¬ p4203) ∨ (¬ p4405) ∨ (¬ p4441))
    : (¬ p4441) ∨ p2156 ∨ (¬ p2220) ∨ p2553 ∨ (¬ p4203) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48815 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step85556 (p2156 p2563 p3212 p3461 p3646 p5045 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h45748 : (¬ p2563) ∨ (¬ p3212) ∨ (¬ p3461) ∨ (¬ p3646) ∨ (¬ p5045))
    : (¬ p3212) ∨ (¬ p5045) ∨ (¬ p2563) ∨ p2156 ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45748 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85558 (p2156 p2696 p3365 p3425 p3434 p3461 p3471 p3645 p3646 p4030 p4202 p4205 p4322 p4625 p4752 : Prop)
    (h73396 : p3471 ∨ p3425)
    (h73436 : p3646 ∨ p2156)
    (h73390 : p3365 ∨ p2696)
    (h63724 : (¬ p3365) ∨ (¬ p3434) ∨ (¬ p3461) ∨ (¬ p3471) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4030) ∨ (¬ p4202) ∨ (¬ p4205) ∨ (¬ p4322) ∨ (¬ p4625) ∨ (¬ p4752))
    : p3425 ∨ (¬ p4322) ∨ (¬ p4202) ∨ (¬ p4752) ∨ (¬ p4625) ∨ (¬ p3434) ∨ (¬ p3645) ∨ p2156 ∨ (¬ p4030) ∨ (¬ p3461) ∨ (¬ p4205) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4205 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u14 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h63724 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u4))) (fun r10 => (False.elim (r10 u3)))))))))))))))))))))))))

theorem step85562 (p2156 p2284 p2950 p3136 p3646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h71634 : (¬ p2284) ∨ (¬ p3136) ∨ (¬ p3646) ∨ (¬ p2950))
    : (¬ p2284) ∨ (¬ p3136) ∨ (¬ p2950) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71634 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step85568 (p2156 p2246 p2264 p2807 p3125 p3461 p3645 p3646 p3744 p3941 p4191 p4959 p5119 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73454 : p3744 ∨ p3125)
    (h73436 : p3646 ∨ p2156)
    (h61500 : (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3941) ∨ (¬ p4191) ∨ (¬ p4959) ∨ (¬ p5119))
    : p3461 ∨ (¬ p2246) ∨ (¬ p4959) ∨ (¬ p3941) ∨ (¬ p3645) ∨ p3125 ∨ (¬ p5119) ∨ p2156 ∨ (¬ p2807) ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h61500 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step85569 (p2156 p2264 p2341 p3553 p3646 p4333 p4558 p4988 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73436 : p3646 ∨ p2156)
    (h59303 : (¬ p2341) ∨ (¬ p3553) ∨ (¬ p3646) ∨ (¬ p4333) ∨ (¬ p4558) ∨ (¬ p4988))
    : (¬ p2341) ∨ (¬ p4333) ∨ p2264 ∨ (¬ p4988) ∨ p2156 ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59303 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step85573 (p2156 p2274 p2396 p2911 p2922 p3097 p3379 p3646 p4107 p4524 p4666 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73352 : p3097 ∨ p2274)
    (h72962 : p4524)
    (h73436 : p3646 ∨ p2156)
    (h54913 : (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4524) ∨ (¬ p4666))
    : p2396 ∨ p2274 ∨ (¬ p4666) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p2911) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4524 := h72962;
    let u10 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h54913 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step85587 (p2177 p2274 p2341 p3546 p3551 p3922 p4105 p4564 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h51850 : (¬ p2177) ∨ (¬ p2274) ∨ (¬ p3546) ∨ (¬ p3551) ∨ (¬ p3922) ∨ (¬ p4105) ∨ (¬ p4564))
    : p2341 ∨ (¬ p2274) ∨ (¬ p3546) ∨ (¬ p4105) ∨ (¬ p3922) ∨ (¬ p4564) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51850 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step85589 (p2274 p2312 p2341 p3527 p3548 p4105 p4514 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h54550 : (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3548) ∨ (¬ p4105) ∨ (¬ p4514))
    : (¬ p2341) ∨ p3527 ∨ (¬ p2312) ∨ (¬ p2274) ∨ (¬ p4514) ∨ (¬ p4105) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54550 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step85599 (p2641 p4319 p5893 : Prop)
    (h74197 : p2641 ∨ (¬ p5893))
    (h12346 : p4319 ∨ p5893)
    : p4319 ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4319) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5893) := (Or.elim h74197 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12346 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step85610 (p2307 p2313 p2667 p3309 p3549 p4319 : Prop)
    (h73405 : (¬ p3309) ∨ (¬ p3549))
    (h73238 : p2313 ∨ p2307)
    (h33739 : (¬ p2313) ∨ (¬ p2667) ∨ p3549 ∨ (¬ p4319))
    : (¬ p4319) ∨ (¬ p3309) ∨ (¬ p2667) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3549) := (Or.elim h73405 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h33739 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step85625 (p2284 p3412 p3952 p4338 p4516 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h19493 : (¬ p3412) ∨ (¬ p3952) ∨ (¬ p4338) ∨ (¬ p4516))
    : (¬ p3412) ∨ p2284 ∨ (¬ p4516) ∨ (¬ p4338) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3412 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h19493 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step85627 (p2274 p3309 p3549 p4516 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h25006 : (¬ p2274) ∨ (¬ p3549) ∨ (¬ p4516))
    : p3309 ∨ (¬ p2274) ∨ (¬ p4516) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3309) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h25006 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step85633 (p2220 p2307 p2962 p3309 p3549 p4120 p4516 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h73522 : p4120 ∨ p2220)
    (h69504 : (¬ p2307) ∨ (¬ p4120) ∨ (¬ p2962) ∨ (¬ p4516) ∨ (¬ p3549))
    : (¬ p2307) ∨ p3309 ∨ (¬ p2962) ∨ p2220 ∨ (¬ p4516) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69504 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85635 (p3051 p3556 p3571 p3645 p4431 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h13537 : (¬ p3556) ∨ (¬ p3571) ∨ (¬ p3645) ∨ (¬ p4431))
    : p3051 ∨ (¬ p3645) ∨ (¬ p4431) ∨ (¬ p3571) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h13537 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step85636 (p2156 p2187 p2246 p2363 p2437 p2663 p2744 p3343 p3389 p3645 p3646 p3742 p3989 p4332 p4347 p4874 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73560 : p4347 ∨ p2363)
    (h73452 : p3742 ∨ p2437)
    (h73502 : p3989 ∨ p2187)
    (h57004 : (¬ p2246) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3343) ∨ (¬ p3389) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3742) ∨ (¬ p3989) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4874))
    : (¬ p3343) ∨ (¬ p3389) ∨ (¬ p2246) ∨ (¬ p4874) ∨ (¬ p4332) ∨ (¬ p2744) ∨ (¬ p2663) ∨ (¬ p3645) ∨ p2156 ∨ p2363 ∨ p2437 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u13 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u14 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u15 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h57004 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u14))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u15))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u13))) (fun r10 => (False.elim (r10 u3)))))))))))))))))))))))))

theorem step85638 (p2156 p2192 p3645 p3646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h5323 : (¬ p2192) ∨ (¬ p3645) ∨ (¬ p3646))
    : (¬ p2192) ∨ p2156 ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5323 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step85643 (p2383 p2584 p2668 p2761 p3323 p3324 p3519 p3645 p4032 p4322 p4376 p4621 p4874 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h59453 : (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2761) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3519) ∨ (¬ p3645) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4376) ∨ (¬ p4621) ∨ (¬ p4874))
    : (¬ p4322) ∨ (¬ p2383) ∨ p2668 ∨ (¬ p4032) ∨ (¬ p2761) ∨ (¬ p3519) ∨ (¬ p3323) ∨ (¬ p4621) ∨ (¬ p3645) ∨ (¬ p4376) ∨ (¬ p2584) ∨ (¬ p4874) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h59453 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (False.elim (r10 u11)))))))))))))))))))))))))

theorem step85649 (p2156 p2563 p2696 p2982 p3256 p3365 p3366 p3537 p3645 p3646 p4030 p4202 p4752 p4948 p4967 p5059 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73846 : p4948 ∨ p2982)
    (h73390 : p3365 ∨ p2696)
    (h63723 : (¬ p2563) ∨ (¬ p3256) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3537) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4030) ∨ (¬ p4202) ∨ (¬ p4752) ∨ (¬ p4948) ∨ (¬ p4967) ∨ (¬ p5059))
    : (¬ p4967) ∨ (¬ p3366) ∨ (¬ p2563) ∨ (¬ p3256) ∨ p2156 ∨ (¬ p5059) ∨ (¬ p4202) ∨ (¬ p3537) ∨ (¬ p4030) ∨ (¬ p3645) ∨ (¬ p4752) ∨ p2982 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4967 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u14 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u15 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    (Or.elim h63723 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u14))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u0))) (fun r11 => (False.elim (r11 u5)))))))))))))))))))))))))))

theorem step85651 (p2220 p2246 p2651 p2749 p3016 p3146 p3266 p3645 p3692 p3888 p4120 p4444 p4877 p5250 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73580 : p4444 ∨ p3266)
    (h73448 : p3692 ∨ p3146)
    (h62238 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p3016) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p3888) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4877) ∨ (¬ p5250))
    : (¬ p2246) ∨ (¬ p3888) ∨ p2220 ∨ (¬ p2651) ∨ p3266 ∨ (¬ p5250) ∨ (¬ p3016) ∨ p3146 ∨ (¬ p4877) ∨ (¬ p3645) ∨ (¬ p2749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62238 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u5)))))))))))))))))))))))

theorem step85659 (p2220 p2563 p3645 p3979 p4120 p4210 p5568 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h45148 : (¬ p2563) ∨ (¬ p3645) ∨ (¬ p3979) ∨ (¬ p4120) ∨ (¬ p4210) ∨ (¬ p5568))
    : (¬ p5568) ∨ (¬ p3979) ∨ p2220 ∨ (¬ p2563) ∨ (¬ p3645) ∨ (¬ p4210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45148 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step85660 (p2156 p2187 p2246 p2651 p2749 p3276 p3333 p3645 p3646 p3989 p4343 p4877 p5123 p5580 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73502 : p3989 ∨ p2187)
    (h50803 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4343) ∨ (¬ p4877) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p5123) ∨ (¬ p3645) ∨ p2156 ∨ (¬ p2246) ∨ (¬ p4877) ∨ (¬ p3333) ∨ p2187 ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p4343) ∨ (¬ p3276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50803 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u1))) (fun r10 => (False.elim (r10 u0)))))))))))))))))))))))))

theorem step85669 (p2352 p4432 p5833 : Prop)
    (h74121 : p2352 ∨ (¬ p5833))
    (h11991 : p4432 ∨ p5833)
    : p4432 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4432) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2352) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5833) := (Or.elim h74121 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11991 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step85673 (p2911 p4383 p4921 : Prop)
    (h73830 : p4921 ∨ p2911)
    (h8137 : p4383 ∨ (¬ p4921))
    : p4383 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4383) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr h));
    let u2 : p4921 := (Or.elim h73830 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h8137 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step85674 (p2911 p4383 p5950 : Prop)
    (h74273 : p2911 ∨ (¬ p5950))
    (h12681 : p4383 ∨ p5950)
    : p4383 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4383) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5950) := (Or.elim h74273 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12681 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step85676 (p2651 p2657 p3166 p3878 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h19564 : (¬ p2657) ∨ (¬ p3166) ∨ (¬ p3878))
    : (¬ p3166) ∨ (¬ p3878) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19564 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step85684 (p3389 p5200 p5203 : Prop)
    (h73954 : p5200 ∨ (¬ p3389))
    (h8824 : (¬ p5200) ∨ p5203)
    : (¬ p3389) ∨ p5203 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5203) := (fun h => hn (Or.inr h));
    let u2 : p5200 := (Or.elim h73954 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8824 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step85687 (p2881 p2996 p3246 p3516 p3570 p3821 p4155 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73418 : p3570 ∨ p2881)
    (h43658 : (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3821) ∨ (¬ p4155))
    : (¬ p3246) ∨ p3516 ∨ (¬ p4155) ∨ p2881 ∨ (¬ p2996) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43658 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85691 (p2088 p2187 p2192 p2255 p2459 p2946 p2996 p3412 p3857 p3961 p4133 p4155 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h58979 : (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2255) ∨ (¬ p2459) ∨ (¬ p2946) ∨ (¬ p2996) ∨ (¬ p3412) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4133) ∨ (¬ p4155))
    : (¬ p4155) ∨ (¬ p2187) ∨ (¬ p3412) ∨ (¬ p2192) ∨ (¬ p2996) ∨ (¬ p3961) ∨ p2088 ∨ (¬ p2946) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p2255) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4155 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h58979 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step85698 (p2493 p2573 p2579 p3347 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h5216 : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3347))
    : p2573 ∨ (¬ p3347) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h5216 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step85704 (p2493 p2573 p2579 p2655 p2946 p4116 p4704 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73046 : p4704)
    (h53224 : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2946) ∨ (¬ p4116) ∨ (¬ p4704))
    : (¬ p4116) ∨ (¬ p2655) ∨ p2573 ∨ (¬ p2493) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4704 := h73046;
    (Or.elim h53224 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step85709 (p2406 p2493 p2573 p2579 p2608 p3238 p3366 p3905 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73274 : p2579 ∨ p2573)
    (h73374 : p3238 ∨ p2406)
    (h60977 : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3238) ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p3954))
    : p2608 ∨ p2573 ∨ (¬ p3905) ∨ p2406 ∨ (¬ p3366) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60977 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step85710 (p2406 p2440 p2493 p2542 p2573 p2579 p3238 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73274 : p2579 ∨ p2573)
    (h73374 : p3238 ∨ p2406)
    (h44855 : (¬ p2493) ∨ (¬ p2542) ∨ (¬ p2579) ∨ (¬ p3238))
    : p2440 ∨ p2573 ∨ p2406 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44855 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step85713 (p2493 p2573 p2579 p2655 p2839 p3361 p3541 p3583 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73274 : p2579 ∨ p2573)
    (h67323 : (¬ p2493) ∨ (¬ p2655) ∨ (¬ p2579) ∨ (¬ p3361) ∨ (¬ p3583) ∨ (¬ p3541))
    : (¬ p2655) ∨ p2839 ∨ p2573 ∨ (¬ p3541) ∨ (¬ p2493) ∨ (¬ p3361) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2655 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67323 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step85716 (p2177 p2299 p2493 p2573 p2579 p2922 p2928 p3921 p4108 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73234 : p2299 ∨ p2177)
    (h73274 : p2579 ∨ p2573)
    (h51361 : (¬ p2299) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2928) ∨ (¬ p3921) ∨ (¬ p4108))
    : p2922 ∨ (¬ p4108) ∨ p2177 ∨ (¬ p2493) ∨ p2573 ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51361 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step85717 (p2088 p2482 p2493 p2528 p2534 p2573 p2579 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73274 : p2579 ∨ p2573)
    (h45635 : (¬ p2088) ∨ (¬ p2482) ∨ (¬ p2493) ∨ (¬ p2534) ∨ (¬ p2579))
    : p2528 ∨ (¬ p2482) ∨ p2573 ∨ (¬ p2088) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2482 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45635 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step85718 (p2230 p2493 p2573 p2579 p2922 p2928 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73274 : p2579 ∨ p2573)
    (h45504 : (¬ p2230) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2928))
    : p2922 ∨ (¬ p2493) ∨ p2573 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45504 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85722 (p2132 p2493 p2509 p2573 p2579 p2870 p2881 p4108 p4438 p4733 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h60685 : (¬ p2132) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2579) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p4108) ∨ (¬ p4438) ∨ (¬ p4733))
    : (¬ p2870) ∨ (¬ p2881) ∨ p2573 ∨ (¬ p2132) ∨ (¬ p4438) ∨ (¬ p2493) ∨ (¬ p4733) ∨ (¬ p4108) ∨ (¬ p2509) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60685 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step85723 (p2132 p2406 p2493 p2573 p2579 p2870 p2901 p3115 p3238 p4108 p4320 p4733 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73274 : p2579 ∨ p2573)
    (h73374 : p3238 ∨ p2406)
    (h57792 : (¬ p2132) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2870) ∨ (¬ p3115) ∨ (¬ p3238) ∨ (¬ p4108) ∨ (¬ p4320) ∨ (¬ p4733))
    : (¬ p2870) ∨ p2901 ∨ p2573 ∨ (¬ p4108) ∨ (¬ p4733) ∨ (¬ p2132) ∨ (¬ p2493) ∨ p2406 ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57792 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step85726 (p2493 p2573 p2579 p2911 p2922 p2928 p3644 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73434 : p3644 ∨ p2911)
    (h73274 : p2579 ∨ p2573)
    (h48935 : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2928) ∨ (¬ p3644))
    : p2922 ∨ p2911 ∨ (¬ p2493) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48935 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85727 (p2493 p3016 p3193 p3461 p3574 p4022 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73422 : p3574 ∨ p3016)
    (h52615 : (¬ p2493) ∨ (¬ p3193) ∨ (¬ p3574) ∨ (¬ p4022) ∨ (¬ p4191))
    : p3461 ∨ (¬ p3193) ∨ (¬ p2493) ∨ (¬ p4022) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52615 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85729 (p2493 p2992 p3016 p3574 p3662 p4281 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73422 : p3574 ∨ p3016)
    (h69654 : (¬ p2493) ∨ (¬ p3662) ∨ (¬ p3574) ∨ (¬ p4281))
    : p2992 ∨ p3016 ∨ (¬ p4281) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69654 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step85739 (p2331 p2493 p2651 p2963 p4389 p4814 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h50450 : (¬ p2493) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p4389) ∨ (¬ p4814))
    : p2331 ∨ (¬ p4389) ∨ (¬ p4814) ∨ (¬ p2651) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50450 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85744 (p2255 p2352 p2493 p2651 p2881 p2957 p2992 p3051 p3556 p3570 p3662 p4116 p4133 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h73440 : p3662 ∨ p2992)
    (h60170 : (¬ p2255) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2651) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4116) ∨ (¬ p4133))
    : (¬ p2493) ∨ (¬ p2651) ∨ (¬ p4116) ∨ p2881 ∨ (¬ p4133) ∨ (¬ p2255) ∨ (¬ p2957) ∨ (¬ p2352) ∨ p3051 ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u12 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h60170 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step85745 (p2493 p2509 p2528 p2534 p3422 p3584 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73426 : p3584 ∨ p3422)
    (h59905 : (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3584))
    : (¬ p2509) ∨ p2528 ∨ (¬ p2493) ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59905 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85747 (p2254 p2352 p2459 p2493 p3166 p3172 p3256 p3379 p4118 p4133 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73356 : p3172 ∨ p3166)
    (h49041 : (¬ p2254) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2493) ∨ (¬ p3172) ∨ (¬ p3379) ∨ (¬ p4118) ∨ (¬ p4133))
    : (¬ p2493) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p4133) ∨ p3256 ∨ p3166 ∨ (¬ p2254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49041 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step85750 (p2307 p2352 p2383 p2387 p2493 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h43307 : (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2493))
    : (¬ p2493) ∨ (¬ p2352) ∨ (¬ p2307) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43307 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step85752 (p2254 p2352 p2493 p2881 p2901 p2946 p2952 p3379 p3570 p4133 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73418 : p3570 ∨ p2881)
    (h73330 : p2952 ∨ p2946)
    (h49040 : (¬ p2254) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4320))
    : (¬ p2493) ∨ p2901 ∨ (¬ p2254) ∨ (¬ p4133) ∨ (¬ p2352) ∨ (¬ p3379) ∨ p2881 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49040 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step85753 (p2241 p2247 p2352 p2493 p3379 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h54572 : (¬ p2247) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3379))
    : (¬ p2493) ∨ (¬ p2352) ∨ (¬ p3379) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54572 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step85755 (p2220 p2352 p2459 p2493 p3146 p3379 p3692 p4120 p4133 p4524 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h72962 : p4524)
    (h73522 : p4120 ∨ p2220)
    (h59460 : (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4133) ∨ (¬ p4524))
    : (¬ p2493) ∨ (¬ p2352) ∨ (¬ p2459) ∨ p3146 ∨ (¬ p4133) ∨ p2220 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4524 := h72962;
    let u9 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59460 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step85756 (p2230 p2352 p2406 p2493 p3238 p4079 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h49321 : (¬ p2230) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p4079))
    : (¬ p2493) ∨ (¬ p2352) ∨ p2406 ∨ (¬ p4079) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49321 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85757 (p2254 p2352 p2459 p2493 p2807 p3256 p3379 p3414 p3919 p4118 p4133 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73520 : p4118 ∨ p3256)
    (h59459 : (¬ p2254) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4133))
    : p2807 ∨ (¬ p2352) ∨ (¬ p4133) ∨ (¬ p2459) ∨ (¬ p2493) ∨ p3256 ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p3919) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2807) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59459 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step85758 (p2187 p2352 p2440 p2493 p3989 p4116 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h58369 : (¬ p2352) ∨ (¬ p2440) ∨ (¬ p2493) ∨ (¬ p3989) ∨ (¬ p4116))
    : (¬ p2493) ∨ (¬ p4116) ∨ p2187 ∨ (¬ p2352) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58369 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85759 (p2352 p2493 p2668 p3324 p4194 p4814 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h41518 : (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3324) ∨ (¬ p4194) ∨ (¬ p4814))
    : (¬ p2493) ∨ (¬ p2352) ∨ (¬ p4814) ∨ p2668 ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41518 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85760 (p2363 p2493 p2509 p3016 p3574 p4347 p4432 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73422 : p3574 ∨ p3016)
    (h43476 : (¬ p2493) ∨ (¬ p2509) ∨ (¬ p3574) ∨ (¬ p4347) ∨ (¬ p4432))
    : (¬ p2509) ∨ p2363 ∨ (¬ p2493) ∨ p3016 ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43476 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85762 (p2493 p2922 p2928 p3564 p3921 p4624 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h49562 : (¬ p2493) ∨ (¬ p2928) ∨ (¬ p3564) ∨ (¬ p3921) ∨ (¬ p4624))
    : (¬ p3564) ∨ p2922 ∨ (¬ p4624) ∨ (¬ p2493) ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49562 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85763 (p2254 p2493 p2946 p2952 p3146 p3156 p3379 p3497 p3564 p3692 p4330 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73330 : p2952 ∨ p2946)
    (h73400 : p3497 ∨ p3156)
    (h49061 : (¬ p2254) ∨ (¬ p2493) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3497) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p4330))
    : (¬ p3564) ∨ p3146 ∨ (¬ p2493) ∨ (¬ p3379) ∨ p2946 ∨ (¬ p2254) ∨ p3156 ∨ (¬ p4330) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49061 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step85767 (p2493 p2651 p2946 p2952 p3879 p4116 p4717 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h63411 : (¬ p2493) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4116) ∨ (¬ p4717))
    : p2946 ∨ (¬ p4116) ∨ (¬ p2651) ∨ (¬ p4717) ∨ (¬ p3879) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63411 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step85768 (p2493 p2608 p3016 p3379 p3574 p3954 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73498 : p3954 ∨ p2608)
    (h46431 : (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3574) ∨ (¬ p3954))
    : p3016 ∨ p2608 ∨ (¬ p2493) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46431 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85769 (p2241 p2247 p2493 p3016 p3379 p3574 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73226 : p2247 ∨ p2241)
    (h46469 : (¬ p2247) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3574))
    : p3016 ∨ p2241 ∨ (¬ p3379) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46469 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85770 (p2241 p2440 p2493 p2542 p3016 p3574 p4281 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73270 : p2542 ∨ p2440)
    (h45175 : (¬ p2241) ∨ (¬ p2493) ∨ (¬ p2542) ∨ (¬ p3574) ∨ (¬ p4281))
    : p3016 ∨ p2440 ∨ (¬ p4281) ∨ (¬ p2241) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45175 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85780 (p2210 p2493 p3379 p3555 p4034 p4717 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h41796 : (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4717))
    : p2210 ∨ (¬ p3379) ∨ (¬ p2493) ∨ (¬ p4717) ∨ (¬ p4034) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41796 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85790 (p2156 p2406 p2493 p3238 p3646 p4203 p4533 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73374 : p3238 ∨ p2406)
    (h61001 : (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3646) ∨ (¬ p4203) ∨ (¬ p4533))
    : p2156 ∨ (¬ p4203) ∨ p2406 ∨ (¬ p2493) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61001 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85791 (p2284 p2406 p2493 p3238 p3952 p4203 p4702 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73374 : p3238 ∨ p2406)
    (h52922 : (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3952) ∨ (¬ p4203) ∨ (¬ p4702))
    : (¬ p4702) ∨ p2284 ∨ p2406 ∨ (¬ p2493) ∨ (¬ p4203) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4702 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52922 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step85793 (p2187 p2493 p2922 p2928 p3921 p4203 p4405 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h41678 : (¬ p2187) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (¬ p3921) ∨ (¬ p4203) ∨ (¬ p4405))
    : (¬ p3921) ∨ (¬ p2493) ∨ (¬ p4405) ∨ p2922 ∨ (¬ p4203) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3921 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41678 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step85794 (p2187 p2493 p3564 p3654 p3946 p4356 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h46129 : (¬ p2187) ∨ (¬ p2493) ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p4356))
    : (¬ p3564) ∨ p3654 ∨ (¬ p4356) ∨ (¬ p2493) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46129 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85797 (p2307 p2396 p2406 p2493 p2578 p3238 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h47764 : (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2493) ∨ (¬ p2578) ∨ (¬ p3238))
    : (¬ p2396) ∨ (¬ p2307) ∨ p2406 ∨ (¬ p2493) ∨ (¬ p2578) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47764 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85798 (p2396 p2417 p2493 p2922 p2928 p4278 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73546 : p4278 ∨ p2417)
    (h61300 : (¬ p2396) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (¬ p4278))
    : p2922 ∨ p2417 ∨ (¬ p2396) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61300 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85799 (p2295 p2493 p2553 p3379 p3568 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h42795 : (¬ p2493) ∨ (¬ p2553) ∨ (¬ p3379) ∨ (¬ p3568))
    : (¬ p2553) ∨ p2295 ∨ (¬ p2493) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42795 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85800 (p2295 p2493 p3193 p3323 p3568 p4022 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h56300 : (¬ p2493) ∨ (¬ p3193) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4022))
    : (¬ p3323) ∨ (¬ p3193) ∨ (¬ p2493) ∨ (¬ p4022) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56300 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85802 (p2341 p2493 p2926 p3527 p3548 p3575 p3741 p4717 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h41078 : (¬ p2341) ∨ (¬ p2493) ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p3575) ∨ (¬ p3741) ∨ (¬ p4717))
    : p3527 ∨ (¬ p2341) ∨ (¬ p3741) ∨ (¬ p2493) ∨ (¬ p2926) ∨ (¬ p3575) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2926 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41078 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step85803 (p2417 p2493 p2926 p3631 p3741 p3817 p4717 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h41974 : (¬ p2417) ∨ (¬ p2493) ∨ (¬ p2926) ∨ (¬ p3741) ∨ (¬ p3817) ∨ (¬ p4717))
    : p3631 ∨ (¬ p2926) ∨ (¬ p2417) ∨ (¬ p2493) ∨ (¬ p3741) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p2926 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41974 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step85804 (p2187 p2254 p2284 p2493 p2553 p2946 p2952 p3379 p3952 p3989 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h73502 : p3989 ∨ p2187)
    (h71641 : (¬ p3989) ∨ (¬ p2493) ∨ (¬ p2254) ∨ (¬ p3379) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p2553))
    : (¬ p2553) ∨ p2946 ∨ (¬ p2254) ∨ p2284 ∨ p2187 ∨ (¬ p3379) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71641 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step85807 (p2307 p2493 p2586 p2922 p2928 p3921 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h41158 : (¬ p2307) ∨ (¬ p2493) ∨ (¬ p2586) ∨ (¬ p2928) ∨ (¬ p3921))
    : p2922 ∨ (¬ p2307) ∨ (¬ p2586) ∨ (¬ p2493) ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41158 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85808 (p2406 p2427 p2493 p3238 p4203 p4235 p4555 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73374 : p3238 ∨ p2406)
    (h41051 : (¬ p2493) ∨ (¬ p3238) ∨ (¬ p4203) ∨ (¬ p4235) ∨ (¬ p4555))
    : p2427 ∨ (¬ p4555) ∨ (¬ p2493) ∨ (¬ p4203) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41051 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85810 (p2274 p2312 p2493 p2922 p2928 p3958 p4279 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h51885 : (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (¬ p3958) ∨ (¬ p4279))
    : (¬ p2312) ∨ (¬ p2274) ∨ (¬ p3958) ∨ (¬ p2493) ∨ p2922 ∨ (¬ p4279) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2312 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51885 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step85817 (p2307 p2313 p2493 p2553 p2577 p5191 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h41407 : (¬ p2313) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p5191))
    : (¬ p2553) ∨ p2307 ∨ (¬ p5191) ∨ (¬ p2493) ∨ (¬ p2577) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41407 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85823 (p2230 p2493 p2589 p2922 p2928 p3389 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73284 : p2589 ∨ p2230)
    (h43811 : (¬ p2493) ∨ (¬ p2589) ∨ (¬ p2928) ∨ (¬ p3389))
    : (¬ p3389) ∨ p2922 ∨ (¬ p2493) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43811 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step85831 (p2373 p2406 p2493 p3238 p3880 p4203 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73374 : p3238 ∨ p2406)
    (h69506 : (¬ p3238) ∨ (¬ p2493) ∨ (¬ p3880) ∨ (¬ p4203))
    : p2373 ∨ (¬ p4203) ∨ (¬ p2493) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69506 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step85833 (p2406 p2493 p3238 p4203 p5433 p5440 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h41057 : (¬ p2493) ∨ (¬ p3238) ∨ (¬ p4203) ∨ (¬ p5433) ∨ (¬ p5440))
    : (¬ p5433) ∨ (¬ p5440) ∨ (¬ p4203) ∨ p2406 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5433 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41057 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step85838 (p2493 p2608 p3367 p3422 p3584 p3585 p3954 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73428 : p3585 ∨ p3367)
    (h73498 : p3954 ∨ p2608)
    (h61611 : (¬ p2493) ∨ (¬ p3584) ∨ (¬ p3585) ∨ (¬ p3954))
    : p3422 ∨ p3367 ∨ (¬ p2493) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61611 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step85845 (p2992 p4958 p4960 : Prop)
    (h73852 : p4958 ∨ (¬ p2992))
    (h8248 : (¬ p4958) ∨ p4960)
    : (¬ p2992) ∨ p4960 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4960) := (fun h => hn (Or.inr h));
    let u2 : p4958 := (Or.elim h73852 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8248 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step85846 (p2245 p2608 p2744 p2946 p2952 p2992 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h52369 : (¬ p2245) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2952) ∨ (¬ p2992))
    : (¬ p2992) ∨ p2946 ∨ (¬ p2744) ∨ (¬ p2245) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52369 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step85848 (p2630 p2651 p2810 p2946 p2952 p2992 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73316 : p2810 ∨ p2630)
    (h44641 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2952) ∨ (¬ p2992))
    : p2946 ∨ (¬ p2992) ∨ p2630 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44641 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step85849 (p2331 p2727 p2946 p2952 p2992 p4111 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73518 : p4111 ∨ p2727)
    (h61272 : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4111))
    : (¬ p2331) ∨ (¬ p2992) ∨ p2946 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61272 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85850 (p2727 p2807 p2946 p2952 p2992 p4111 p4652 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73330 : p2952 ∨ p2946)
    (h57730 : (¬ p2807) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4652))
    : p2727 ∨ (¬ p2992) ∨ p2946 ∨ (¬ p2807) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57730 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85851 (p2727 p2881 p2901 p2992 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h46164 : (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4111))
    : p2727 ∨ (¬ p2992) ∨ (¬ p2881) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46164 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85853 (p2427 p2727 p2901 p2992 p4111 p4235 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73536 : p4235 ∨ p2427)
    (h62076 : (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4235))
    : p2727 ∨ (¬ p2992) ∨ p2427 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62076 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85855 (p2241 p2307 p2313 p2363 p2459 p2992 p3156 p3955 p4347 p4902 p5021 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73238 : p2313 ∨ p2307)
    (h57107 : (¬ p2241) ∨ (¬ p2313) ∨ (¬ p2459) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p4902) ∨ (¬ p5021))
    : (¬ p2992) ∨ p2363 ∨ (¬ p4902) ∨ (¬ p3955) ∨ (¬ p2459) ∨ (¬ p3156) ∨ (¬ p2241) ∨ p2307 ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57107 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step85856 (p2252 p2284 p2630 p2651 p2657 p2992 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h58442 : (¬ p2252) ∨ (¬ p2284) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2992))
    : (¬ p2992) ∨ (¬ p2252) ∨ (¬ p2284) ∨ (¬ p2630) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58442 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step85857 (p2230 p2589 p2659 p2727 p2992 p4111 p4241 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73284 : p2589 ∨ p2230)
    (h41378 : (¬ p2589) ∨ (¬ p2659) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241))
    : p2727 ∨ (¬ p2992) ∨ (¬ p2659) ∨ p2230 ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41378 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85859 (p2727 p2992 p3115 p3680 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h62490 : (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p4111))
    : (¬ p3115) ∨ (¬ p3680) ∨ (¬ p2992) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62490 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85860 (p2727 p2850 p2992 p3684 p4111 p4241 p4750 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73442 : p3684 ∨ p2850)
    (h50114 : (¬ p2992) ∨ (¬ p3684) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4750))
    : p2727 ∨ (¬ p2992) ∨ p2850 ∨ (¬ p4241) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50114 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85862 (p2245 p2946 p2952 p2992 p3379 p4813 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h52499 : (¬ p2245) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3379) ∨ (¬ p4813))
    : (¬ p2992) ∨ p2946 ∨ (¬ p2245) ∨ (¬ p3379) ∨ (¬ p4813) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4813 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52499 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85863 (p2440 p2493 p2499 p2727 p2992 p4703 p4715 p4809 : Prop)
    (h73770 : p4809 ∨ p2727)
    (h73260 : p2499 ∨ p2493)
    (h73714 : p4703 ∨ p2440)
    (h65966 : (¬ p4809) ∨ (¬ p4703) ∨ (¬ p2499) ∨ (¬ p4715) ∨ (¬ p2992))
    : (¬ p2992) ∨ p2727 ∨ p2493 ∨ (¬ p4715) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h65966 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step85864 (p2727 p2992 p3016 p3574 p4111 p4241 p4715 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73422 : p3574 ∨ p3016)
    (h41275 : (¬ p2992) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4715))
    : p2727 ∨ (¬ p2992) ∨ p3016 ∨ (¬ p4241) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41275 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85869 (p2727 p2881 p2951 p2992 p3051 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h46346 : (¬ p2881) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p4111))
    : (¬ p3051) ∨ (¬ p2881) ∨ (¬ p2992) ∨ (¬ p2951) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46346 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85872 (p2295 p2641 p2992 p3136 p3568 p4154 p4315 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73416 : p3568 ∨ p2295)
    (h73550 : p4315 ∨ p3136)
    (h62524 : (¬ p2992) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4315))
    : p2641 ∨ (¬ p2992) ∨ p2295 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62524 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step85873 (p2274 p2641 p2992 p3097 p3136 p3745 p4154 p4315 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73352 : p3097 ∨ p2274)
    (h73550 : p4315 ∨ p3136)
    (h53191 : (¬ p2992) ∨ (¬ p3097) ∨ (¬ p3745) ∨ (¬ p4154) ∨ (¬ p4315))
    : p2641 ∨ (¬ p2992) ∨ (¬ p3745) ∨ p2274 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53191 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step85875 (p2252 p2264 p2807 p2992 p3136 p3414 p3553 p4315 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73550 : p4315 ∨ p3136)
    (h73392 : p3414 ∨ p2807)
    (h46607 : (¬ p2252) ∨ (¬ p2992) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4315))
    : (¬ p2992) ∨ (¬ p2252) ∨ p2264 ∨ p3136 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46607 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step85878 (p2177 p2311 p2341 p2696 p2742 p2785 p2829 p2901 p2992 p3551 p3688 p4556 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73444 : p3688 ∨ p2829)
    (h71644 : (¬ p2742) ∨ (¬ p3688) ∨ (¬ p3551) ∨ (¬ p2177) ∨ (¬ p2696) ∨ (¬ p2785) ∨ (¬ p4556) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p2311))
    : p2341 ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p2742) ∨ p2829 ∨ (¬ p2785) ∨ (¬ p2311) ∨ (¬ p2696) ∨ (¬ p4556) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71644 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step85882 (p2187 p2668 p2727 p2992 p3989 p4111 p4336 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h73518 : p4111 ∨ p2727)
    (h55144 : (¬ p2668) ∨ (¬ p2992) ∨ (¬ p3989) ∨ (¬ p4111) ∨ (¬ p4336))
    : (¬ p2668) ∨ (¬ p2992) ∨ p2187 ∨ (¬ p4336) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55144 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85883 (p2274 p2295 p2727 p2992 p3097 p4111 p4336 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73352 : p3097 ∨ p2274)
    (h46255 : (¬ p2295) ∨ (¬ p2992) ∨ (¬ p3097) ∨ (¬ p4111) ∨ (¬ p4336))
    : p2727 ∨ (¬ p2992) ∨ p2274 ∨ (¬ p2295) ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46255 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85890 (p2437 p2727 p2992 p3742 p4111 p4241 p4644 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73452 : p3742 ∨ p2437)
    (h51415 : (¬ p2992) ∨ (¬ p3742) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4644))
    : p2727 ∨ (¬ p2992) ∨ (¬ p4241) ∨ (¬ p4644) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51415 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85892 (p2727 p2992 p3083 p4111 p4241 p4256 p4608 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73542 : p4256 ∨ p3083)
    (h41356 : (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4256) ∨ (¬ p4608))
    : p2727 ∨ (¬ p2992) ∨ (¬ p4608) ∨ (¬ p4241) ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41356 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85894 (p2253 p2563 p2651 p2727 p2992 p4111 p4241 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h43378 : (¬ p2253) ∨ (¬ p2563) ∨ (¬ p2651) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241))
    : p2727 ∨ (¬ p2992) ∨ (¬ p2253) ∨ (¬ p4241) ∨ (¬ p2563) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43378 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step85895 (p2241 p2363 p2383 p2387 p2992 p3156 p3609 p4347 p4746 p5021 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73560 : p4347 ∨ p2363)
    (h63609 : (¬ p2241) ∨ (¬ p2387) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3609) ∨ (¬ p4347) ∨ (¬ p4746) ∨ (¬ p5021))
    : (¬ p2992) ∨ (¬ p3609) ∨ p2383 ∨ (¬ p2241) ∨ (¬ p3156) ∨ (¬ p4746) ∨ p2363 ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63609 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step85900 (p2177 p2241 p2299 p2307 p2313 p2459 p2992 p3115 p4348 p4450 p5021 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73234 : p2299 ∨ p2177)
    (h73238 : p2313 ∨ p2307)
    (h63968 : (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p5021))
    : p2459 ∨ (¬ p3115) ∨ (¬ p2241) ∨ p2177 ∨ p2307 ∨ (¬ p4450) ∨ (¬ p2992) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63968 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step85903 (p2241 p2352 p2363 p2573 p2579 p2992 p3115 p3956 p4347 p4450 p5193 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73500 : p3956 ∨ p2352)
    (h73274 : p2579 ∨ p2573)
    (h54246 : (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p5193))
    : (¬ p3115) ∨ (¬ p2992) ∨ (¬ p2241) ∨ (¬ p5193) ∨ p2363 ∨ (¬ p4450) ∨ p2352 ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h54246 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step85906 (p2563 p2641 p2992 p4154 p4702 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h67014 : (¬ p2992) ∨ (¬ p4154) ∨ (¬ p4702) ∨ (¬ p2563))
    : p2641 ∨ (¬ p2992) ∨ (¬ p4702) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h67014 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step85918 (p2187 p2284 p2608 p2744 p2992 p3399 p3527 p3548 p4133 p4366 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73404 : p3548 ∨ p3527)
    (h58449 : (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2992) ∨ (¬ p3548) ∨ (¬ p4133) ∨ (¬ p4366))
    : p3399 ∨ (¬ p2187) ∨ (¬ p4133) ∨ p3527 ∨ (¬ p2284) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58449 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step85919 (p2187 p2284 p2727 p2992 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h53791 : (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2992) ∨ (¬ p4111))
    : (¬ p2284) ∨ (¬ p2187) ∨ p2727 ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53791 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85920 (p2295 p2553 p2641 p2992 p3568 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73416 : p3568 ∨ p2295)
    (h44624 : (¬ p2553) ∨ (¬ p2992) ∨ (¬ p3568) ∨ (¬ p4154))
    : p2641 ∨ p2295 ∨ (¬ p2992) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44624 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85921 (p2253 p2608 p2807 p2992 p2996 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h49982 : (¬ p2253) ∨ (¬ p2807) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3954))
    : p2608 ∨ (¬ p2996) ∨ (¬ p2253) ∨ (¬ p2992) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49982 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85922 (p2992 p3189 p4237 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h10182 : (¬ p2992) ∨ (¬ p4237) ∨ (¬ p4360))
    : p3189 ∨ (¬ p2992) ∨ (¬ p4237) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h10182 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step85925 (p2241 p2427 p2901 p2992 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h43122 : (¬ p2241) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4235))
    : (¬ p2992) ∨ (¬ p2241) ∨ p2427 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43122 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85926 (p2901 p2992 p3166 p3189 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h47223 : (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3166) ∨ (¬ p4360))
    : (¬ p2992) ∨ p3189 ∨ (¬ p3166) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47223 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85927 (p2284 p2992 p3166 p3189 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h56447 : (¬ p2284) ∨ (¬ p2992) ∨ (¬ p3166) ∨ (¬ p4360))
    : p3189 ∨ (¬ p2992) ∨ (¬ p3166) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h56447 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85930 (p2187 p2992 p3125 p3323 p3744 p4336 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h42739 : (¬ p2187) ∨ (¬ p2992) ∨ (¬ p3323) ∨ (¬ p3744) ∨ (¬ p4336))
    : (¬ p4336) ∨ (¬ p2187) ∨ (¬ p2992) ∨ (¬ p3323) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4336 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42739 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step85934 (p2341 p2656 p2992 p3031 p3527 p3548 p4704 p5201 : Prop)
    (h73046 : p4704)
    (h73404 : p3548 ∨ p3527)
    (h63083 : (¬ p2341) ∨ (¬ p2656) ∨ (¬ p2992) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p4704) ∨ (¬ p5201))
    : (¬ p2992) ∨ (¬ p2341) ∨ (¬ p3031) ∨ p3527 ∨ (¬ p2656) ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4704 := h73046;
    let u7 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63083 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step85935 (p2156 p2641 p2960 p2992 p3745 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h49623 : (¬ p2156) ∨ (¬ p2960) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4154))
    : p2641 ∨ (¬ p3745) ∨ (¬ p2156) ∨ (¬ p2992) ∨ (¬ p2960) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49623 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85938 (p2252 p2331 p2901 p2963 p2992 p3745 p4558 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h55461 : (¬ p2252) ∨ (¬ p2901) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4558))
    : (¬ p2992) ∨ (¬ p4558) ∨ (¬ p2252) ∨ (¬ p3745) ∨ p2331 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55461 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step85939 (p2641 p2992 p3156 p3745 p4154 p4509 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h50128 : (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3745) ∨ (¬ p4154) ∨ (¬ p4509))
    : p2641 ∨ (¬ p2992) ∨ (¬ p4509) ∨ (¬ p3745) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50128 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85941 (p2641 p2901 p2992 p3745 p4154 p4558 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h49250 : (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4154) ∨ (¬ p4558))
    : p2641 ∨ (¬ p2992) ∨ (¬ p2901) ∨ (¬ p4558) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49250 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85943 (p2742 p2797 p2901 p2992 p3745 p4195 p4558 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h55463 : (¬ p2742) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4558))
    : p2797 ∨ (¬ p2742) ∨ (¬ p4558) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55463 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step85947 (p2619 p2992 p3189 p4312 p4360 p5053 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h48526 : (¬ p2619) ∨ (¬ p2992) ∨ (¬ p4312) ∨ (¬ p4360) ∨ (¬ p5053))
    : p3189 ∨ (¬ p2992) ∨ (¬ p2619) ∨ (¬ p4312) ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48526 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step85949 (p2373 p2992 p3189 p4312 p4360 p4702 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h48175 : (¬ p2373) ∨ (¬ p2992) ∨ (¬ p4312) ∨ (¬ p4360) ∨ (¬ p4702))
    : p3189 ∨ (¬ p2992) ∨ (¬ p2373) ∨ (¬ p4702) ∨ (¬ p4312) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48175 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step85958 (p2156 p2563 p2951 p2992 p2996 p4110 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h56912 : (¬ p2156) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p4110))
    : (¬ p2996) ∨ (¬ p2992) ∨ p2563 ∨ (¬ p2156) ∨ (¬ p2951) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56912 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85959 (p2156 p2563 p2951 p2992 p3189 p4110 p4360 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73566 : p4360 ∨ p3189)
    (h46373 : (¬ p2156) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p4110) ∨ (¬ p4360))
    : (¬ p2951) ∨ (¬ p2992) ∨ p2563 ∨ (¬ p2156) ∨ p3189 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2951 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46373 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step85960 (p2284 p2563 p2727 p2992 p4110 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73516 : p4110 ∨ p2563)
    (h46242 : (¬ p2284) ∨ (¬ p2992) ∨ (¬ p4110) ∨ (¬ p4111))
    : p2727 ∨ (¬ p2992) ∨ (¬ p2284) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46242 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85962 (p2177 p2241 p2299 p2553 p2573 p2579 p2588 p2992 p3156 p4902 p5193 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73234 : p2299 ∨ p2177)
    (h73282 : p2588 ∨ p2553)
    (h61603 : (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p4902) ∨ (¬ p5193))
    : (¬ p3156) ∨ (¬ p2992) ∨ (¬ p5193) ∨ p2573 ∨ p2177 ∨ (¬ p2241) ∨ (¬ p4902) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h61603 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step85966 (p2274 p2951 p2962 p2992 p3125 p3654 p3744 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h44512 : (¬ p2274) ∨ (¬ p2951) ∨ (¬ p2962) ∨ (¬ p2992) ∨ (¬ p3654) ∨ (¬ p3744))
    : (¬ p2951) ∨ (¬ p3654) ∨ p3125 ∨ (¬ p2992) ∨ (¬ p2274) ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2951 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44512 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step85968 (p2641 p2992 p3125 p3323 p4037 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73508 : p4037 ∨ p3323)
    (h43792 : (¬ p2992) ∨ (¬ p3125) ∨ (¬ p4037) ∨ (¬ p4154))
    : p2641 ∨ p3323 ∨ (¬ p3125) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43792 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85972 (p2122 p2177 p2245 p2774 p2946 p2952 p2992 p3189 p4041 p4360 p4733 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73330 : p2952 ∨ p2946)
    (h53301 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4733))
    : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p2245) ∨ p3189 ∨ (¬ p4041) ∨ (¬ p2992) ∨ (¬ p2177) ∨ (¬ p4733) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h53301 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step85973 (p2641 p2992 p3323 p3483 p4037 p4154 p4375 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73508 : p4037 ∨ p3323)
    (h60316 : (¬ p2992) ∨ (¬ p3483) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4375))
    : (¬ p3483) ∨ p2641 ∨ (¬ p4375) ∨ p3323 ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60316 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step85974 (p2437 p2922 p2928 p2992 p3402 p4704 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73046 : p4704)
    (h41708 : (¬ p2437) ∨ (¬ p2928) ∨ (¬ p2992) ∨ (¬ p3402) ∨ (¬ p4704))
    : (¬ p3402) ∨ (¬ p2992) ∨ p2922 ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3402 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4704 := h73046;
    (Or.elim h41708 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85976 (p2641 p2667 p2860 p2992 p3743 p4154 p5053 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h41355 : (¬ p2667) ∨ (¬ p2860) ∨ (¬ p2992) ∨ (¬ p3743) ∨ (¬ p4154) ∨ (¬ p5053))
    : p2641 ∨ (¬ p3743) ∨ (¬ p2860) ∨ (¬ p5053) ∨ (¬ p2667) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41355 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step85979 (p2156 p2249 p2284 p2950 p2992 p3646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h41432 : (¬ p2249) ∨ (¬ p2284) ∨ (¬ p2950) ∨ (¬ p2992) ∨ (¬ p3646))
    : (¬ p2992) ∨ (¬ p2950) ∨ (¬ p2249) ∨ (¬ p2284) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41432 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step85980 (p2156 p2187 p2992 p2996 p3646 p3989 p4155 p4988 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73502 : p3989 ∨ p2187)
    (h60317 : (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4155) ∨ (¬ p4988))
    : (¬ p4988) ∨ (¬ p2996) ∨ (¬ p2992) ∨ p2156 ∨ (¬ p4155) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4988 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h60317 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step85984 (p2901 p2995 p5948 : Prop)
    (h74271 : (¬ p2901) ∨ (¬ p5948))
    (h12671 : p2995 ∨ p5948)
    : p2995 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2995) := (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5948) := (Or.elim h74271 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12671 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step85985 (p2641 p3922 p4758 : Prop)
    (h73746 : p4758 ∨ (¬ p2641))
    (h7737 : p3922 ∨ (¬ p4758))
    : p3922 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3922) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4758 := (Or.elim h73746 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h7737 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step85986 (p2641 p4758 p4759 : Prop)
    (h73746 : p4758 ∨ (¬ p2641))
    (h7738 : (¬ p4758) ∨ p4759)
    : (¬ p2641) ∨ p4759 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4759) := (fun h => hn (Or.inr h));
    let u2 : p4758 := (Or.elim h73746 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7738 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step85988 (p2641 p4758 p4761 : Prop)
    (h73746 : p4758 ∨ (¬ p2641))
    (h7741 : (¬ p4758) ∨ p4761)
    : (¬ p2641) ∨ p4761 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4761) := (fun h => hn (Or.inr h));
    let u2 : p4758 := (Or.elim h73746 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7741 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step85990 (p2187 p2641 p2668 p2727 p3989 p4111 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h73518 : p4111 ∨ p2727)
    (h54763 : (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3989) ∨ (¬ p4111))
    : (¬ p2641) ∨ (¬ p2668) ∨ p2187 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54763 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85991 (p2187 p2241 p2641 p2668 p3989 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h57955 : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3989))
    : (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2241) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57955 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85992 (p2331 p2641 p2651 p2963 p2992 p3662 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73440 : p3662 ∨ p2992)
    (h42706 : (¬ p2641) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3662))
    : (¬ p2641) ∨ p2331 ∨ (¬ p2651) ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42706 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step85995 (p2274 p2295 p2641 p2992 p3097 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73352 : p3097 ∨ p2274)
    (h64310 : (¬ p2295) ∨ (¬ p2641) ∨ (¬ p3097) ∨ (¬ p3662))
    : (¬ p2295) ∨ p2992 ∨ p2274 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64310 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85996 (p2331 p2630 p2641 p2651 p2810 p2963 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73316 : p2810 ∨ p2630)
    (h60565 : (¬ p2641) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963))
    : (¬ p2641) ∨ p2331 ∨ (¬ p2651) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60565 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step85998 (p2331 p2630 p2641 p2727 p2963 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73338 : p2963 ∨ p2331)
    (h71646 : (¬ p4111) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p2630))
    : (¬ p2641) ∨ p2727 ∨ (¬ p2630) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71646 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step86000 (p2641 p2727 p4111 p4194 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h20024 : (¬ p2641) ∨ (¬ p4111) ∨ (¬ p4194))
    : (¬ p2641) ∨ (¬ p4194) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20024 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step86002 (p2245 p2331 p2608 p2641 p2744 p2963 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h52297 : (¬ p2245) ∨ (¬ p2608) ∨ (¬ p2641) ∨ (¬ p2744) ∨ (¬ p2963))
    : (¬ p2641) ∨ p2331 ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2245) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52297 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86005 (p2295 p2641 p2651 p2727 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h42742 : (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2651) ∨ (¬ p4111))
    : p2727 ∨ (¬ p2295) ∨ (¬ p2651) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42742 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86006 (p2230 p2241 p2295 p2563 p2589 p2641 p3125 p3744 p4110 p4620 p5193 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h73454 : p3744 ∨ p3125)
    (h50278 : (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2589) ∨ (¬ p2641) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4620) ∨ (¬ p5193))
    : (¬ p2641) ∨ (¬ p2295) ∨ p2563 ∨ p2230 ∨ (¬ p5193) ∨ (¬ p4620) ∨ p3125 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50278 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step86007 (p2177 p2249 p2295 p2373 p2406 p2641 p2651 p2657 p3238 p3487 p3880 p4905 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73288 : p2657 ∨ p2651)
    (h73374 : p3238 ∨ p2406)
    (h60562 : (¬ p2177) ∨ (¬ p2249) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3238) ∨ (¬ p3487) ∨ (¬ p3880) ∨ (¬ p4905))
    : (¬ p2295) ∨ (¬ p2177) ∨ (¬ p2641) ∨ (¬ p3487) ∨ p2373 ∨ p2651 ∨ (¬ p4905) ∨ (¬ p2249) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h60562 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step86014 (p2440 p2641 p2727 p3984 p4111 p4717 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h58149 : (¬ p2440) ∨ (¬ p2641) ∨ (¬ p3984) ∨ (¬ p4111) ∨ (¬ p4717))
    : p2727 ∨ (¬ p2641) ∨ (¬ p2440) ∨ (¬ p3984) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h58149 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86016 (p2641 p2992 p3115 p3662 p3986 p4208 p5043 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73534 : p4208 ∨ p3115)
    (h41037 : (¬ p2641) ∨ (¬ p3662) ∨ (¬ p3986) ∨ (¬ p4208) ∨ (¬ p5043))
    : p2992 ∨ p3115 ∨ (¬ p2641) ∨ (¬ p5043) ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41037 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86017 (p2641 p2797 p2946 p2992 p3662 p4195 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73532 : p4195 ∨ p2797)
    (h46001 : (¬ p2641) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p4195))
    : (¬ p2641) ∨ p2992 ∨ (¬ p2946) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46001 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86019 (p2641 p2992 p3156 p3497 p3662 p3986 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73400 : p3497 ∨ p3156)
    (h69507 : (¬ p3662) ∨ (¬ p3986) ∨ (¬ p3497) ∨ (¬ p2641))
    : p2992 ∨ (¬ p2641) ∨ (¬ p3986) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69507 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step86027 (p2156 p2641 p2954 p2992 p3646 p3662 p3986 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73436 : p3646 ∨ p2156)
    (h41571 : (¬ p2641) ∨ (¬ p2954) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p3986))
    : (¬ p3986) ∨ p2992 ∨ p2156 ∨ (¬ p2954) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3986 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41571 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step86030 (p2241 p2341 p2417 p2641 p2911 p3323 p3551 p4278 p4621 p5193 p5197 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73408 : p3551 ∨ p2341)
    (h54494 : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2911) ∨ (¬ p3323) ∨ (¬ p3551) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p5193) ∨ (¬ p5197))
    : p2417 ∨ p2341 ∨ (¬ p2911) ∨ (¬ p5197) ∨ (¬ p2641) ∨ (¬ p5193) ∨ (¬ p4621) ∨ (¬ p3323) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54494 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step86031 (p2230 p2241 p2274 p2563 p2589 p2641 p2668 p3097 p4110 p4405 p5193 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h53722 : (¬ p2241) ∨ (¬ p2589) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4405) ∨ (¬ p5193))
    : (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2241) ∨ (¬ p4405) ∨ p2274 ∨ p2563 ∨ p2230 ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h53722 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86033 (p2641 p2651 p2668 p2727 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h62026 : (¬ p2641) ∨ (¬ p2651) ∨ (¬ p2668) ∨ (¬ p4111))
    : p2727 ∨ (¬ p2668) ∨ (¬ p2641) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h62026 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86036 (p2563 p2641 p2807 p2996 p3986 p4110 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h43682 : (¬ p2641) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p3986) ∨ (¬ p4110))
    : (¬ p2641) ∨ (¬ p2996) ∨ (¬ p2807) ∨ (¬ p3986) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43682 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86038 (p2641 p2656 p2891 p3051 p3368 p3486 p4399 p4975 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h62796 : (¬ p2641) ∨ (¬ p2656) ∨ (¬ p3051) ∨ (¬ p3368) ∨ (¬ p3486) ∨ (¬ p4399) ∨ (¬ p4975))
    : (¬ p3051) ∨ (¬ p3368) ∨ (¬ p2656) ∨ (¬ p4975) ∨ (¬ p2641) ∨ p2891 ∨ (¬ p4399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h62796 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step86041 (p2241 p2427 p2440 p2608 p2641 p2737 p2797 p4153 p4699 : Prop)
    (h73712 : p4699 ∨ (¬ p2440))
    (h67060 : (¬ p2797) ∨ (¬ p2608) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2737) ∨ (¬ p2427) ∨ (¬ p4153) ∨ (¬ p4699))
    : (¬ p2797) ∨ (¬ p2641) ∨ (¬ p4153) ∨ (¬ p2737) ∨ (¬ p2608) ∨ (¬ p2440) ∨ (¬ p2241) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h67060 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step86042 (p2245 p2331 p2608 p2641 p2727 p2963 p4111 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73518 : p4111 ∨ p2727)
    (h55152 : (¬ p2245) ∨ (¬ p2608) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p4111))
    : (¬ p2245) ∨ p2331 ∨ (¬ p2608) ∨ p2727 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step86043 (p2341 p2459 p2641 p2696 p2707 p2742 p3323 p3551 p3588 p3959 p4330 p4348 : Prop)
    (h73430 : p3588 ∨ p2707)
    (h73408 : p3551 ∨ p2341)
    (h73562 : p4348 ∨ p2459)
    (h71648 : (¬ p3551) ∨ (¬ p4348) ∨ (¬ p2696) ∨ (¬ p2641) ∨ (¬ p4330) ∨ (¬ p3959) ∨ (¬ p2742) ∨ (¬ p3588) ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p2742) ∨ p2707 ∨ (¬ p3959) ∨ (¬ p4330) ∨ p2341 ∨ (¬ p2641) ∨ (¬ p2696) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3588 := (Or.elim h73430 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71648 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step86047 (p2274 p2641 p2946 p2992 p3662 p3986 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h42954 : (¬ p2274) ∨ (¬ p2641) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3986))
    : p2992 ∨ (¬ p2274) ∨ (¬ p3986) ∨ (¬ p2641) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42954 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86048 (p2641 p2957 p2992 p3051 p3556 p3662 p3986 p4555 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73414 : p3556 ∨ p3051)
    (h48448 : (¬ p2641) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3986) ∨ (¬ p4555))
    : (¬ p2641) ∨ p2992 ∨ p3051 ∨ (¬ p3986) ∨ (¬ p2957) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48448 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step86049 (p2331 p2406 p2440 p2542 p2641 p2963 p3238 p3402 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73270 : p2542 ∨ p2440)
    (h73374 : p3238 ∨ p2406)
    (h50078 : (¬ p2542) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p3238) ∨ (¬ p3402))
    : (¬ p2641) ∨ p2331 ∨ p2440 ∨ p2406 ∨ (¬ p3402) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50078 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86050 (p2563 p2641 p2992 p3662 p3986 p4110 p4705 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73516 : p4110 ∨ p2563)
    (h57446 : (¬ p2641) ∨ (¬ p3662) ∨ (¬ p3986) ∨ (¬ p4110) ∨ (¬ p4705))
    : (¬ p2641) ∨ p2992 ∨ (¬ p4705) ∨ (¬ p3986) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57446 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86056 (p2573 p2579 p2641 p2659 p2727 p3984 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73274 : p2579 ∨ p2573)
    (h42036 : (¬ p2579) ∨ (¬ p2641) ∨ (¬ p2659) ∨ (¬ p3984) ∨ (¬ p4111))
    : (¬ p2641) ∨ p2727 ∨ (¬ p3984) ∨ p2573 ∨ (¬ p2659) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42036 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86058 (p2241 p2459 p2641 p2911 p3323 p3389 p3540 p3644 p4330 p4348 p5193 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73562 : p4348 ∨ p2459)
    (h73402 : p3540 ∨ p3389)
    (h54676 : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5193))
    : (¬ p2641) ∨ p2911 ∨ (¬ p5193) ∨ p2459 ∨ (¬ p3323) ∨ p3389 ∨ (¬ p2241) ∨ (¬ p4330) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h54676 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step86061 (p2641 p2992 p3115 p3662 p4208 p4322 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73534 : p4208 ∨ p3115)
    (h47538 : (¬ p2641) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p4322))
    : p2992 ∨ (¬ p4322) ∨ (¬ p2641) ∨ p3115 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47538 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step86069 (p2245 p2331 p2459 p2470 p2528 p2641 p2963 p3189 p4041 p4348 p4360 p5190 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73562 : p4348 ∨ p2459)
    (h73338 : p2963 ∨ p2331)
    (h42101 : (¬ p2245) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4360) ∨ (¬ p5190))
    : (¬ p2245) ∨ p3189 ∨ p2459 ∨ (¬ p5190) ∨ p2331 ∨ (¬ p2470) ∨ (¬ p2641) ∨ (¬ p4041) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42101 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step86070 (p2641 p2651 p2657 p2946 p2992 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73288 : p2657 ∨ p2651)
    (h42864 : (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3662))
    : p2992 ∨ (¬ p2641) ∨ p2651 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42864 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86071 (p2641 p2651 p2657 p3166 p3189 p4360 p4975 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73288 : p2657 ∨ p2651)
    (h60434 : (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p4360) ∨ (¬ p4975))
    : (¬ p2641) ∨ (¬ p3166) ∨ p3189 ∨ (¬ p4975) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60434 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86072 (p2563 p2641 p2992 p3567 p3662 p4110 p4356 p4705 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73516 : p4110 ∨ p2563)
    (h42039 : (¬ p2641) ∨ (¬ p3567) ∨ (¬ p3662) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4705))
    : p2992 ∨ (¬ p3567) ∨ (¬ p2641) ∨ (¬ p4356) ∨ p2563 ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42039 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step86073 (p2249 p2307 p2396 p2509 p2528 p2534 p2641 p2651 p2657 p3487 p3567 p3950 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73268 : p2534 ∨ p2528)
    (h62190 : (¬ p2249) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3487) ∨ (¬ p3567) ∨ (¬ p3950))
    : (¬ p2307) ∨ (¬ p3567) ∨ (¬ p2396) ∨ (¬ p3950) ∨ (¬ p3487) ∨ p2651 ∨ (¬ p2641) ∨ (¬ p2509) ∨ (¬ p2249) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h62190 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step86077 (p2230 p2406 p2641 p2656 p3238 p3402 p4975 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h49513 : (¬ p2230) ∨ (¬ p2641) ∨ (¬ p2656) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p4975))
    : p2406 ∨ (¬ p3402) ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2641) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49513 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step86078 (p2241 p2641 p3266 p3276 p3323 p3346 p4330 p4425 p5193 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h49988 : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3266) ∨ (¬ p3323) ∨ (¬ p3346) ∨ (¬ p4330) ∨ (¬ p4425) ∨ (¬ p5193))
    : p3276 ∨ (¬ p3323) ∨ (¬ p2641) ∨ (¬ p2241) ∨ (¬ p5193) ∨ (¬ p3266) ∨ (¬ p4330) ∨ (¬ p3346) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49988 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step86080 (p2641 p2651 p2657 p2807 p2996 p4975 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h60433 : (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p4975))
    : (¬ p2996) ∨ (¬ p2641) ∨ (¬ p4975) ∨ (¬ p2807) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60433 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86089 (p2352 p2641 p3323 p3564 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h43757 : (¬ p2352) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p4137))
    : p3564 ∨ (¬ p3323) ∨ (¬ p2641) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43757 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86090 (p2187 p2641 p3189 p4360 p4564 p4769 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h52244 : (¬ p2187) ∨ (¬ p2641) ∨ (¬ p4360) ∨ (¬ p4564) ∨ (¬ p4769))
    : (¬ p2641) ∨ p3189 ∨ (¬ p4769) ∨ (¬ p4564) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52244 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86091 (p2187 p2641 p3189 p3958 p3984 p4360 p4769 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h60226 : (¬ p2187) ∨ (¬ p2641) ∨ (¬ p3958) ∨ (¬ p3984) ∨ (¬ p4360) ∨ (¬ p4769))
    : (¬ p2641) ∨ p3189 ∨ (¬ p3984) ∨ (¬ p3958) ∨ (¬ p4769) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60226 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step86093 (p2187 p2641 p2946 p2992 p3662 p3986 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h47569 : (¬ p2187) ∨ (¬ p2641) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3986))
    : (¬ p2641) ∨ (¬ p2187) ∨ p2992 ∨ (¬ p2946) ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47569 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86094 (p2641 p3189 p4341 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h20133 : (¬ p2641) ∨ (¬ p4341) ∨ (¬ p4360))
    : (¬ p4341) ∨ p3189 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20133 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step86099 (p2241 p2373 p2427 p2641 p2668 p3051 p3556 p3880 p4134 p4524 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h72962 : p4524)
    (h73414 : p3556 ∨ p3051)
    (h51897 : (¬ p2241) ∨ (¬ p2427) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3556) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4524))
    : (¬ p2641) ∨ p2373 ∨ (¬ p4134) ∨ (¬ p2668) ∨ p3051 ∨ (¬ p2427) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4524 := h72962;
    let u9 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51897 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step86100 (p2249 p2383 p2387 p2641 p2668 p3983 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h52257 : (¬ p2249) ∨ (¬ p2387) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3983))
    : (¬ p3983) ∨ (¬ p2668) ∨ p2383 ∨ (¬ p2249) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3983 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52257 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step86102 (p2641 p2668 p3166 p3189 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h46010 : (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3166) ∨ (¬ p4360))
    : p3189 ∨ (¬ p2668) ∨ (¬ p2641) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46010 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86108 (p2641 p2668 p2727 p2819 p4111 p4358 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73564 : p4358 ∨ p2819)
    (h44990 : (¬ p2641) ∨ (¬ p2668) ∨ (¬ p4111) ∨ (¬ p4358))
    : (¬ p2668) ∨ (¬ p2641) ∨ p2727 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44990 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86114 (p2253 p2274 p2553 p2573 p2579 p2588 p2641 p2807 p2996 p4564 p5193 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73274 : p2579 ∨ p2573)
    (h49720 : (¬ p2253) ∨ (¬ p2274) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2641) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p4564) ∨ (¬ p5193))
    : (¬ p2641) ∨ (¬ p2274) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p5193) ∨ (¬ p2253) ∨ p2553 ∨ p2573 ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49720 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step86116 (p2274 p2307 p2641 p3097 p3125 p3567 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h60963 : (¬ p2307) ∨ (¬ p2641) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3567))
    : (¬ p3567) ∨ (¬ p2307) ∨ (¬ p2641) ∨ p2274 ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60963 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step86118 (p2122 p2307 p2641 p2751 p3567 p3822 p4841 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h42548 : (¬ p2307) ∨ (¬ p2641) ∨ (¬ p2751) ∨ (¬ p3567) ∨ (¬ p3822) ∨ (¬ p4841))
    : (¬ p4841) ∨ p2122 ∨ (¬ p2307) ∨ (¬ p2751) ∨ (¬ p2641) ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4841 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42548 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step86119 (p2274 p2307 p2641 p2727 p3097 p3567 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73352 : p3097 ∨ p2274)
    (h46371 : (¬ p2307) ∨ (¬ p2641) ∨ (¬ p3097) ∨ (¬ p3567) ∨ (¬ p4111))
    : p2727 ∨ (¬ p2307) ∨ (¬ p3567) ∨ p2274 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46371 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86121 (p2177 p2307 p2641 p2727 p3567 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h46285 : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2641) ∨ (¬ p3567) ∨ (¬ p4111))
    : p2727 ∨ (¬ p2307) ∨ (¬ p2177) ∨ (¬ p2641) ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46285 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86126 (p2641 p2656 p2972 p3212 p3368 p4363 p4399 p4975 : Prop)
    (h73568 : p4363 ∨ p2972)
    (h58486 : (¬ p2641) ∨ (¬ p2656) ∨ (¬ p3212) ∨ (¬ p3368) ∨ (¬ p4363) ∨ (¬ p4399) ∨ (¬ p4975))
    : (¬ p3368) ∨ (¬ p3212) ∨ (¬ p4399) ∨ (¬ p4975) ∨ (¬ p2656) ∨ (¬ p2641) ∨ p2972 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3368 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4363 := (Or.elim h73568 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h58486 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step86132 (p2264 p2331 p2641 p2807 p2963 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h44027 : (¬ p2264) ∨ (¬ p2641) ∨ (¬ p2807) ∨ (¬ p2963))
    : p2331 ∨ (¬ p2641) ∨ (¬ p2807) ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44027 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86139 (p2641 p2996 p3027 p4156 : Prop)
    (h73339 : (¬ p2996) ∨ (¬ p3027))
    (h26504 : (¬ p2641) ∨ p3027 ∨ (¬ p4156))
    : (¬ p2996) ∨ (¬ p4156) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3027) := (Or.elim h73339 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h26504 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step86141 (p2295 p2396 p2641 p2727 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h44989 : (¬ p2295) ∨ (¬ p2396) ∨ (¬ p2641) ∨ (¬ p4111))
    : (¬ p2295) ∨ (¬ p2396) ∨ p2727 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44989 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86142 (p2295 p2641 p3166 p3189 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h47398 : (¬ p2295) ∨ (¬ p2641) ∨ (¬ p3166) ∨ (¬ p4360))
    : (¬ p2641) ∨ p3189 ∨ (¬ p2295) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47398 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86146 (p2241 p2295 p2427 p2598 p2641 p2850 p3055 p3684 p4235 p4559 p4736 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73350 : p3055 ∨ p2598)
    (h73442 : p3684 ∨ p2850)
    (h49393 : (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4736))
    : (¬ p2295) ∨ p2427 ∨ (¬ p4736) ∨ (¬ p2241) ∨ p2598 ∨ (¬ p4559) ∨ (¬ p2641) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49393 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step86155 (p2493 p2499 p2598 p3422 p3584 : Prop)
    (h73425 : (¬ p3422) ∨ (¬ p3584))
    (h73260 : p2499 ∨ p2493)
    (h71649 : p3584 ∨ (¬ p2499) ∨ (¬ p2598))
    : (¬ p3422) ∨ (¬ p2598) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3584) := (Or.elim h73425 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71649 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u1)))))))

theorem step86158 (p2437 p3422 p3584 p3742 p3920 p4343 : Prop)
    (h73425 : (¬ p3422) ∨ (¬ p3584))
    (h73452 : p3742 ∨ p2437)
    (h32587 : p3584 ∨ (¬ p3742) ∨ (¬ p3920) ∨ (¬ p4343))
    : (¬ p3920) ∨ (¬ p3422) ∨ (¬ p4343) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3920 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3584) := (Or.elim h73425 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h32587 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step86164 (p2187 p2274 p3097 p3325 p3989 : Prop)
    (h73351 : (¬ p2274) ∨ (¬ p3097))
    (h73502 : p3989 ∨ p2187)
    (h26630 : p3097 ∨ (¬ p3325) ∨ (¬ p3989))
    : (¬ p3325) ∨ (¬ p2274) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3325 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3097) := (Or.elim h73351 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h26630 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u4)))))))

theorem step86171 (p2363 p2449 p2696 p2748 p2819 p2829 p2996 p3365 p3947 p4669 p4734 : Prop)
    (h72735 : p4734)
    (h73390 : p3365 ∨ p2696)
    (h73494 : p3947 ∨ p2449)
    (h52246 : (¬ p2363) ∨ (¬ p2748) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p2996) ∨ (¬ p3365) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4734))
    : (¬ p2829) ∨ (¬ p2819) ∨ (¬ p4669) ∨ p2696 ∨ (¬ p2996) ∨ (¬ p2748) ∨ p2449 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4734 := h72735;
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52246 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step86173 (p2122 p2318 p2819 p3516 p3550 p3821 p3822 p4666 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73472 : p3822 ∨ p2122)
    (h42270 : (¬ p2318) ∨ (¬ p2819) ∨ (¬ p3550) ∨ (¬ p3821) ∨ (¬ p3822) ∨ (¬ p4666))
    : (¬ p2819) ∨ p3516 ∨ (¬ p2318) ∨ (¬ p4666) ∨ (¬ p3550) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42270 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step86175 (p2187 p2819 p3989 p4428 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h29866 : (¬ p2819) ∨ (¬ p3989) ∨ (¬ p4428))
    : (¬ p2819) ∨ (¬ p4428) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h29866 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step86177 (p2122 p2819 p2911 p3644 p3822 p4170 p4276 p4403 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73434 : p3644 ∨ p2911)
    (h60396 : (¬ p2819) ∨ (¬ p3644) ∨ (¬ p3822) ∨ (¬ p4170) ∨ (¬ p4276) ∨ (¬ p4403))
    : (¬ p2819) ∨ p2122 ∨ p2911 ∨ (¬ p4403) ∨ (¬ p4276) ∨ (¬ p4170) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60396 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step86178 (p2122 p2819 p2911 p3569 p3644 p3822 p4170 p4403 p4556 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73434 : p3644 ∨ p2911)
    (h51056 : (¬ p2819) ∨ (¬ p3569) ∨ (¬ p3644) ∨ (¬ p3822) ∨ (¬ p4170) ∨ (¬ p4403) ∨ (¬ p4556))
    : (¬ p2819) ∨ p2122 ∨ (¬ p4170) ∨ p2911 ∨ (¬ p3569) ∨ (¬ p4556) ∨ (¬ p4403) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51056 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step86179 (p2122 p2363 p2819 p3146 p3692 p3822 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73472 : p3822 ∨ p2122)
    (h43468 : (¬ p2363) ∨ (¬ p2819) ∨ (¬ p3692) ∨ (¬ p3822))
    : (¬ p2819) ∨ p3146 ∨ (¬ p2363) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43468 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86180 (p2122 p2459 p2819 p3266 p3550 p3822 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h47345 : (¬ p2459) ∨ (¬ p2819) ∨ (¬ p3266) ∨ (¬ p3550) ∨ (¬ p3822))
    : (¬ p2819) ∨ (¬ p3550) ∨ (¬ p3266) ∨ (¬ p2459) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47345 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86181 (p2187 p2274 p2819 p2829 p3989 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h58076 : (¬ p2274) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3989))
    : (¬ p2819) ∨ (¬ p2829) ∨ p2187 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58076 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86186 (p2132 p2138 p2187 p2774 p2819 p3989 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h73214 : p2138 ∨ p2132)
    (h45948 : (¬ p2138) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3989))
    : (¬ p2774) ∨ (¬ p2819) ∨ p2187 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45948 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86192 (p2122 p2383 p2387 p2406 p2427 p2819 p3379 p3822 p4556 p5021 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73246 : p2387 ∨ p2383)
    (h57203 : (¬ p2387) ∨ (¬ p2406) ∨ (¬ p2427) ∨ (¬ p2819) ∨ (¬ p3379) ∨ (¬ p3822) ∨ (¬ p4556) ∨ (¬ p5021))
    : p2122 ∨ (¬ p2819) ∨ (¬ p5021) ∨ p2383 ∨ (¬ p4556) ∨ (¬ p2427) ∨ (¬ p2406) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57203 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step86194 (p2363 p2459 p2774 p2819 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h46381 : (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p4348))
    : (¬ p2819) ∨ (¬ p2774) ∨ p2459 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46381 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86197 (p2363 p2598 p2774 p2819 p3055 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h52878 : (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3055))
    : (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2363) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52878 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86198 (p2122 p2307 p2363 p2786 p2819 p3822 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h59041 : (¬ p2307) ∨ (¬ p2363) ∨ (¬ p2786) ∨ (¬ p2819) ∨ (¬ p3822))
    : p2122 ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p2363) ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h59041 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86200 (p2352 p2819 p2829 p3367 p3585 p3956 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73500 : p3956 ∨ p2352)
    (h53317 : (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p3956))
    : (¬ p2829) ∨ (¬ p2819) ∨ p3367 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53317 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86202 (p2122 p2307 p2373 p2406 p2819 p3238 p3379 p3452 p3822 p3880 p4134 p5017 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73490 : p3880 ∨ p2373)
    (h73374 : p3238 ∨ p2406)
    (h73472 : p3822 ∨ p2122)
    (h57530 : (¬ p2307) ∨ (¬ p2819) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3822) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p5017))
    : p3379 ∨ p2373 ∨ (¬ p2819) ∨ (¬ p2307) ∨ p2406 ∨ (¬ p5017) ∨ (¬ p4134) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57530 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step86206 (p2187 p2608 p2819 p2829 p3989 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h43056 : (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3989))
    : (¬ p2819) ∨ (¬ p2829) ∨ (¬ p2608) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43056 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86207 (p2254 p2608 p2819 p2829 p3146 p3166 p3172 p3256 p4118 p4134 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73520 : p4118 ∨ p3256)
    (h56442 : (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3146) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4134))
    : (¬ p2819) ∨ (¬ p2829) ∨ (¬ p4134) ∨ p3166 ∨ (¬ p2608) ∨ (¬ p2254) ∨ p3256 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56442 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step86210 (p2122 p2331 p2668 p2819 p2963 p3324 p3822 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73472 : p3822 ∨ p2122)
    (h73386 : p3324 ∨ p2668)
    (h64040 : (¬ p2819) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3822))
    : p2331 ∨ (¬ p2819) ∨ p2122 ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64040 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86219 (p2252 p2459 p2608 p2750 p2807 p2819 p3093 p3256 p3414 p3919 p3954 p4024 p4118 p4133 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73392 : p3414 ∨ p2807)
    (h73520 : p4118 ∨ p3256)
    (h55543 : (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2750) ∨ (¬ p2819) ∨ (¬ p3093) ∨ (¬ p3414) ∨ (¬ p3919) ∨ (¬ p3954) ∨ (¬ p4024) ∨ (¬ p4118) ∨ (¬ p4133))
    : (¬ p2819) ∨ p2608 ∨ (¬ p3093) ∨ (¬ p4133) ∨ (¬ p4024) ∨ p2807 ∨ (¬ p2750) ∨ (¬ p3919) ∨ (¬ p2459) ∨ p3256 ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h55543 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u13))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step86220 (p2254 p2459 p2608 p2819 p2829 p3166 p3172 p3256 p4118 p4133 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73356 : p3172 ∨ p3166)
    (h48989 : (¬ p2254) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4133))
    : (¬ p2829) ∨ (¬ p2819) ∨ (¬ p2254) ∨ (¬ p4133) ∨ (¬ p2608) ∨ (¬ p2459) ∨ p3256 ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u9 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h48989 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step86224 (p2383 p2387 p2641 p2667 p2745 p2819 p4154 p4426 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73246 : p2387 ∨ p2383)
    (h41270 : (¬ p2387) ∨ (¬ p2667) ∨ (¬ p2745) ∨ (¬ p2819) ∨ (¬ p4154) ∨ (¬ p4426))
    : p2641 ∨ (¬ p2819) ∨ (¬ p4426) ∨ (¬ p2745) ∨ (¬ p2667) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41270 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step86225 (p2246 p2383 p2387 p2744 p2778 p2819 p2901 p2946 p3246 p3366 p3917 p4625 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h63982 : (¬ p2246) ∨ (¬ p2387) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3917) ∨ (¬ p4625))
    : (¬ p3917) ∨ (¬ p2819) ∨ (¬ p4625) ∨ (¬ p2744) ∨ (¬ p3366) ∨ p2383 ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p2246) ∨ (¬ p2778) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3917 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63982 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (False.elim (r9 u2)))))))))))))))))))))))

theorem step86229 (p2363 p2528 p2534 p2819 p3573 p5225 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h53397 : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2819) ∨ (¬ p3573) ∨ (¬ p5225))
    : (¬ p2819) ∨ p2528 ∨ (¬ p2363) ∨ (¬ p5225) ∨ (¬ p3573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53397 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86231 (p2252 p2437 p2651 p2657 p2750 p2753 p2786 p2819 p2911 p3644 p3654 p3742 p3917 p4133 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73434 : p3644 ∨ p2911)
    (h73288 : p2657 ∨ p2651)
    (h63140 : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2786) ∨ (¬ p2819) ∨ (¬ p3644) ∨ (¬ p3654) ∨ (¬ p3742) ∨ (¬ p3917) ∨ (¬ p4133))
    : (¬ p3917) ∨ (¬ p2819) ∨ (¬ p3654) ∨ (¬ p2750) ∨ (¬ p2786) ∨ p2437 ∨ p2911 ∨ (¬ p2753) ∨ (¬ p2252) ∨ p2651 ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3917 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h63140 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step86234 (p2230 p2274 p2563 p2589 p2608 p2819 p2829 p3097 p4110 p4405 p5193 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h60249 : (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4405) ∨ (¬ p5193))
    : (¬ p2819) ∨ (¬ p2829) ∨ p2274 ∨ p2563 ∨ (¬ p2608) ∨ p2230 ∨ (¬ p4405) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h60249 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86236 (p2352 p2573 p2579 p2819 p3956 p4375 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73500 : p3956 ∨ p2352)
    (h71652 : (¬ p3956) ∨ (¬ p2579) ∨ (¬ p4375) ∨ (¬ p2819))
    : (¬ p2819) ∨ p2573 ∨ p2352 ∨ (¬ p4375) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71652 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step86237 (p2122 p2363 p2459 p2819 p3822 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73472 : p3822 ∨ p2122)
    (h53945 : (¬ p2363) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p4348))
    : (¬ p2819) ∨ p2459 ∨ (¬ p2363) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53945 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86240 (p2363 p2737 p2743 p2819 p2829 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h52593 : (¬ p2363) ∨ (¬ p2743) ∨ (¬ p2819) ∨ (¬ p2829))
    : (¬ p2829) ∨ (¬ p2819) ∨ (¬ p2363) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52593 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step86242 (p2220 p2284 p2819 p2957 p4120 p4401 p4506 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h42178 : (¬ p2284) ∨ (¬ p2819) ∨ (¬ p2957) ∨ (¬ p4120) ∨ (¬ p4401) ∨ (¬ p4506))
    : (¬ p2957) ∨ p2220 ∨ (¬ p4401) ∨ (¬ p2819) ∨ (¬ p2284) ∨ (¬ p4506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42178 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step86244 (p2254 p2553 p2588 p2608 p2651 p2657 p2819 p2829 p3016 p3574 p4405 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73288 : p2657 ∨ p2651)
    (h73422 : p3574 ∨ p3016)
    (h56713 : (¬ p2254) ∨ (¬ p2588) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3574) ∨ (¬ p4405))
    : (¬ p2819) ∨ (¬ p2829) ∨ p2553 ∨ p2651 ∨ p3016 ∨ (¬ p2608) ∨ (¬ p2254) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56713 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86248 (p2383 p2386 p2387 p2819 p3016 p3574 p4375 p4753 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73246 : p2387 ∨ p2383)
    (h42360 : (¬ p2386) ∨ (¬ p2387) ∨ (¬ p2819) ∨ (¬ p3574) ∨ (¬ p4375) ∨ (¬ p4753))
    : p3016 ∨ (¬ p2819) ∨ (¬ p4753) ∨ (¬ p4375) ∨ (¬ p2386) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42360 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step86249 (p2122 p2274 p2352 p2819 p3822 p3956 p3958 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73500 : p3956 ∨ p2352)
    (h51887 : (¬ p2274) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p3956) ∨ (¬ p3958))
    : p2122 ∨ (¬ p2819) ∨ (¬ p2274) ∨ (¬ p3958) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51887 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86250 (p2122 p2252 p2307 p2528 p2534 p2651 p2657 p2750 p2753 p2786 p2819 p3083 p3550 p3822 p3941 p4256 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73542 : p4256 ∨ p3083)
    (h73288 : p2657 ∨ p2651)
    (h73268 : p2534 ∨ p2528)
    (h46841 : (¬ p2252) ∨ (¬ p2307) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2786) ∨ (¬ p2819) ∨ (¬ p3550) ∨ (¬ p3822) ∨ (¬ p3941) ∨ (¬ p4256))
    : (¬ p2753) ∨ (¬ p2819) ∨ (¬ p3550) ∨ (¬ p2307) ∨ p2122 ∨ (¬ p3941) ∨ (¬ p2786) ∨ p3083 ∨ (¬ p2750) ∨ (¬ p2252) ∨ p2651 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u14 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u15 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h46841 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u5))) (fun r10 => (False.elim (r10 u13)))))))))))))))))))))))))

theorem step86255 (p2230 p2383 p2387 p2440 p2577 p2819 p4426 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h61761 : (¬ p2230) ∨ (¬ p2387) ∨ (¬ p2440) ∨ (¬ p2577) ∨ (¬ p2819) ∨ (¬ p4426))
    : (¬ p2230) ∨ (¬ p2819) ∨ p2383 ∨ (¬ p2440) ∨ (¬ p4426) ∨ (¬ p2577) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61761 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step86259 (p2383 p2387 p2819 p2901 p2957 p4198 p4428 p4558 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h51200 : (¬ p2387) ∨ (¬ p2819) ∨ (¬ p2901) ∨ (¬ p2957) ∨ (¬ p4198) ∨ (¬ p4428) ∨ (¬ p4558))
    : (¬ p4428) ∨ (¬ p2819) ∨ p2383 ∨ (¬ p4198) ∨ (¬ p2957) ∨ (¬ p2901) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4428 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51200 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step86261 (p2122 p2230 p2307 p2440 p2542 p2589 p2655 p2786 p2819 p3083 p3822 p4256 p4384 p4789 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73472 : p3822 ∨ p2122)
    (h73284 : p2589 ∨ p2230)
    (h73270 : p2542 ∨ p2440)
    (h61964 : (¬ p2307) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2786) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p4789))
    : (¬ p2307) ∨ (¬ p2819) ∨ (¬ p2786) ∨ (¬ p4789) ∨ p3083 ∨ (¬ p2655) ∨ p2122 ∨ p2230 ∨ (¬ p4384) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h61964 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step86262 (p2295 p2668 p2696 p2819 p3324 p4426 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h43292 : (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2819) ∨ (¬ p3324) ∨ (¬ p4426))
    : (¬ p2819) ∨ (¬ p2295) ∨ (¬ p4426) ∨ p2668 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43292 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86265 (p2230 p2589 p2753 p2774 p2819 p2982 p3347 p3979 p4322 p4948 p5119 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73846 : p4948 ∨ p2982)
    (h71653 : (¬ p5119) ∨ (¬ p4948) ∨ (¬ p2774) ∨ (¬ p3979) ∨ (¬ p2753) ∨ (¬ p4322) ∨ (¬ p3347) ∨ (¬ p2819) ∨ (¬ p2589))
    : (¬ p4322) ∨ (¬ p2753) ∨ p2230 ∨ (¬ p2819) ∨ (¬ p3979) ∨ p2982 ∨ (¬ p2774) ∨ (¬ p3347) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71653 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step86268 (p2528 p2819 p3979 p4149 p4286 : Prop)
    (h73548 : p4286 ∨ p4149)
    (h61606 : (¬ p2528) ∨ (¬ p2819) ∨ (¬ p3979) ∨ (¬ p4286))
    : p4149 ∨ (¬ p2819) ∨ (¬ p2528) ∨ (¬ p3979) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4286 := (Or.elim h73548 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h61606 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86269 (p2819 p3573 p3979 p4149 p4286 p5225 : Prop)
    (h73548 : p4286 ∨ p4149)
    (h54402 : (¬ p2819) ∨ (¬ p3573) ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p5225))
    : p4149 ∨ (¬ p2819) ∨ (¬ p5225) ∨ (¬ p3573) ∨ (¬ p3979) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4286 := (Or.elim h73548 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h54402 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86274 (p2122 p2608 p2819 p3309 p3822 p4869 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h43079 : (¬ p2608) ∨ (¬ p2819) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p4869))
    : (¬ p3309) ∨ (¬ p4869) ∨ p2122 ∨ (¬ p2608) ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43079 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step86275 (p2509 p2528 p2534 p2774 p2819 p3379 p3452 p3979 p4733 p5122 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73268 : p2534 ∨ p2528)
    (h50366 : (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3452) ∨ (¬ p3979) ∨ (¬ p4733) ∨ (¬ p5122))
    : (¬ p2819) ∨ (¬ p2509) ∨ (¬ p3979) ∨ (¬ p4733) ∨ (¬ p2774) ∨ p3379 ∨ p2528 ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50366 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86277 (p2192 p2383 p2387 p2819 p3985 p4173 p4356 p4875 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h73246 : p2387 ∨ p2383)
    (h62782 : (¬ p2387) ∨ (¬ p2819) ∨ (¬ p3985) ∨ (¬ p4173) ∨ (¬ p4356) ∨ (¬ p4875))
    : (¬ p2819) ∨ p2192 ∨ (¬ p4875) ∨ p2383 ∨ (¬ p4356) ∨ (¬ p3985) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62782 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step86282 (p2136 p2383 p2387 p2437 p2663 p2819 p3125 p3343 p3389 p3742 p3744 p4198 p4428 p4786 p5322 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73454 : p3744 ∨ p3125)
    (h73246 : p2387 ∨ p2383)
    (h57914 : (¬ p2136) ∨ (¬ p2387) ∨ (¬ p2663) ∨ (¬ p2819) ∨ (¬ p3343) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p3744) ∨ (¬ p4198) ∨ (¬ p4428) ∨ (¬ p4786) ∨ (¬ p5322))
    : p2437 ∨ (¬ p3389) ∨ (¬ p2819) ∨ (¬ p4786) ∨ (¬ p3343) ∨ (¬ p2136) ∨ p3125 ∨ (¬ p5322) ∨ (¬ p4198) ∨ (¬ p4428) ∨ (¬ p2663) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u14 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h57914 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u3))) (fun r10 => (False.elim (r10 u7)))))))))))))))))))))))))

theorem step86287 (p2819 p4860 p4861 : Prop)
    (h73796 : p4860 ∨ (¬ p2819))
    (h7988 : (¬ p4860) ∨ p4861)
    : (¬ p2819) ∨ p4861 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4861) := (fun h => hn (Or.inr h));
    let u2 : p4860 := (Or.elim h73796 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7988 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step86290 (p2187 p2274 p2911 p3097 p3550 p3644 p4276 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73434 : p3644 ∨ p2911)
    (h41718 : (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3550) ∨ (¬ p3644) ∨ (¬ p4276))
    : p2274 ∨ p2911 ∨ (¬ p2187) ∨ (¬ p3550) ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41718 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86294 (p2774 p2780 p2788 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h42713 : (¬ p2780) ∨ p2788)
    : p2774 ∨ p2788 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2788) := (fun h => hn (Or.inr h));
    let u2 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42713 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step86295 (p2774 p2780 p4472 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h45807 : (¬ p2780) ∨ p4472)
    : p2774 ∨ p4472 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4472) := (fun h => hn (Or.inr h));
    let u2 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45807 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step86296 (p2774 p2780 p2787 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h48116 : (¬ p2780) ∨ p2787)
    : p2774 ∨ p2787 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2787) := (fun h => hn (Or.inr h));
    let u2 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48116 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

end ElevenRUP
