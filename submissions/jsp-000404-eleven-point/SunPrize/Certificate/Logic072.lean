import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step124587 (p2264 p2284 p2459 p2954 p3051 p3125 p3204 p3309 p3654 p4333 : Prop)
    (h106494 : p2954)
    (h99444 : p2264 ∨ (¬ p3125) ∨ p2459 ∨ (¬ p3309) ∨ p3654 ∨ (¬ p4333) ∨ (¬ p3204) ∨ (¬ p2284) ∨ (¬ p2954) ∨ p3051)
    : p3654 ∨ (¬ p3309) ∨ p2459 ∨ (¬ p3125) ∨ (¬ p3204) ∨ p3051 ∨ p2264 ∨ (¬ p2284) ∨ (¬ p4333) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2954 := h106494;
    (Or.elim h99444 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u5 r8)))))))))))))))))))))

theorem step124595 (p2761 p2911 p3276 p4635 p4666 : Prop)
    (h105658 : p4666)
    (h99491 : p3276 ∨ (¬ p2761) ∨ (¬ p2911) ∨ (¬ p4635) ∨ (¬ p4666))
    : p3276 ∨ (¬ p2911) ∨ (¬ p4635) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4666 := h105658;
    (Or.elim h99491 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124599 (p2144 p2252 p2352 p2619 p2651 p2750 p2753 p2870 p3016 p3051 p4042 p4503 : Prop)
    (h106530 : p4503)
    (h106345 : p2750)
    (h99508 : p2870 ∨ (¬ p2619) ∨ p2651 ∨ (¬ p2144) ∨ (¬ p3051) ∨ p3016 ∨ (¬ p4503) ∨ p2352 ∨ (¬ p2252) ∨ (¬ p4042) ∨ (¬ p2750) ∨ (¬ p2753))
    : p3016 ∨ p2651 ∨ (¬ p2252) ∨ (¬ p3051) ∨ p2352 ∨ (¬ p2753) ∨ p2870 ∨ (¬ p2144) ∨ (¬ p4042) ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4503 := h106530;
    let u11 : p2750 := h106345;
    (Or.elim h99508 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (False.elim (r10 u5)))))))))))))))))))))))))

theorem step124608 (p2352 p2363 p2573 p2608 p2707 p3434 p3950 p5193 : Prop)
    (h105488 : p5193)
    (h99539 : (¬ p3434) ∨ p2363 ∨ (¬ p2608) ∨ (¬ p5193) ∨ p2352 ∨ p2573 ∨ (¬ p3950) ∨ (¬ p2707))
    : (¬ p3434) ∨ (¬ p2707) ∨ p2352 ∨ (¬ p3950) ∨ p2573 ∨ p2363 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h99539 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step124609 (p2241 p2352 p2363 p2573 p3189 p4009 p5122 p5193 : Prop)
    (h105488 : p5193)
    (h105483 : p5122)
    (h99541 : (¬ p4009) ∨ p2363 ∨ (¬ p5193) ∨ (¬ p2241) ∨ p2352 ∨ (¬ p3189) ∨ (¬ p5122) ∨ p2573)
    : (¬ p4009) ∨ (¬ p3189) ∨ p2352 ∨ p2573 ∨ (¬ p2241) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5193 := h105488;
    let u7 : p5122 := h105483;
    (Or.elim h99541 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step124614 (p2363 p2528 p2573 p2608 p3347 p3399 p3527 p3573 p4503 : Prop)
    (h106530 : p4503)
    (h99557 : p2608 ∨ p2528 ∨ (¬ p3399) ∨ (¬ p2363) ∨ p2573 ∨ (¬ p3347) ∨ (¬ p4503) ∨ (¬ p3573) ∨ (¬ p3527))
    : p2528 ∨ p2573 ∨ (¬ p3573) ∨ (¬ p3527) ∨ p2608 ∨ (¬ p3399) ∨ (¬ p3347) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4503 := h106530;
    (Or.elim h99557 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step124615 (p2246 p2470 p2528 p2630 p2662 p2751 p2901 p2946 p3246 p3950 : Prop)
    (h106343 : p2751)
    (h99559 : (¬ p2246) ∨ (¬ p3246) ∨ p2630 ∨ p2470 ∨ (¬ p2901) ∨ (¬ p2662) ∨ (¬ p2751) ∨ (¬ p3950) ∨ p2528 ∨ (¬ p2946))
    : (¬ p2901) ∨ p2470 ∨ (¬ p3950) ∨ (¬ p3246) ∨ p2630 ∨ (¬ p2246) ∨ p2528 ∨ (¬ p2662) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2751 := h106343;
    (Or.elim h99559 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u6 q8))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step124617 (p2144 p2156 p2860 p3105 p3266 p3276 p3346 p4450 p4729 : Prop)
    (h105429 : p4729)
    (h99578 : p3276 ∨ (¬ p3266) ∨ (¬ p2156) ∨ (¬ p4729) ∨ (¬ p3105) ∨ (¬ p2144) ∨ (¬ p3346) ∨ p2860 ∨ (¬ p4450))
    : p2860 ∨ (¬ p2156) ∨ (¬ p3105) ∨ (¬ p2144) ∨ (¬ p3266) ∨ (¬ p3346) ∨ p3276 ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4729 := h105429;
    (Or.elim h99578 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step124618 (p2685 p2807 p3266 p3276 p3346 p3755 p4117 p4729 p5109 : Prop)
    (h105429 : p4729)
    (h99579 : (¬ p3755) ∨ (¬ p5109) ∨ (¬ p4729) ∨ (¬ p3266) ∨ p3276 ∨ (¬ p3346) ∨ p2685 ∨ (¬ p2807) ∨ (¬ p4117))
    : (¬ p3755) ∨ p2685 ∨ (¬ p3266) ∨ (¬ p2807) ∨ (¬ p4117) ∨ (¬ p3346) ∨ p3276 ∨ (¬ p5109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4729 := h105429;
    (Or.elim h99579 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step124625 (p3266 p3286 p3366 p3379 p3399 p3631 p3950 p4236 p4376 p5284 : Prop)
    (h106320 : p4376)
    (h99598 : (¬ p3399) ∨ (¬ p5284) ∨ (¬ p3266) ∨ (¬ p4376) ∨ p3286 ∨ p3379 ∨ (¬ p3631) ∨ (¬ p4236) ∨ (¬ p3950) ∨ (¬ p3366))
    : (¬ p3366) ∨ (¬ p3631) ∨ (¬ p3950) ∨ p3286 ∨ (¬ p3399) ∨ (¬ p3266) ∨ (¬ p5284) ∨ p3379 ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3366 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h99598 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step124626 (p2252 p2373 p2459 p2598 p2750 p2753 p2850 p3166 p3256 p4902 : Prop)
    (h105456 : p4902)
    (h106345 : p2750)
    (h99612 : p3166 ∨ p3256 ∨ (¬ p2598) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2373) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p4902) ∨ (¬ p2459))
    : (¬ p2850) ∨ p3166 ∨ p3256 ∨ (¬ p2373) ∨ (¬ p2598) ∨ (¬ p2252) ∨ (¬ p2753) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4902 := h105456;
    let u9 : p2750 := h106345;
    (Or.elim h99612 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step124633 (p2449 p2598 p2685 p2737 p2911 p2922 p3590 p4666 : Prop)
    (h105658 : p4666)
    (h99624 : p2449 ∨ (¬ p2911) ∨ p2685 ∨ (¬ p2598) ∨ (¬ p4666) ∨ (¬ p2922) ∨ (¬ p3590) ∨ p2737)
    : p2685 ∨ p2737 ∨ (¬ p3590) ∨ (¬ p2922) ∨ (¬ p2598) ∨ (¬ p2911) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4666 := h105658;
    (Or.elim h99624 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step124635 (p2254 p2331 p2363 p2598 p2668 p2707 p2717 p3367 p3589 : Prop)
    (h105366 : p2254)
    (h99634 : (¬ p2717) ∨ p2363 ∨ (¬ p3589) ∨ p2668 ∨ (¬ p2707) ∨ (¬ p2598) ∨ (¬ p2254) ∨ p3367 ∨ p2331)
    : p2331 ∨ (¬ p2717) ∨ (¬ p2598) ∨ p2668 ∨ (¬ p2707) ∨ p3367 ∨ p2363 ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2254 := h105366;
    (Or.elim h99634 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (u0 r7)))))))))))))))))))

theorem step124638 (p2140 p2156 p2829 p2839 p4185 : Prop)
    (h105364 : p2140)
    (h99672 : (¬ p2829) ∨ (¬ p4185) ∨ p2839 ∨ p2156 ∨ (¬ p2140))
    : (¬ p2829) ∨ p2156 ∨ p2839 ∨ (¬ p4185) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2140 := h105364;
    (Or.elim h99672 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124639 (p2140 p2707 p2839 p3051 p4344 : Prop)
    (h105364 : p2140)
    (h99675 : (¬ p2707) ∨ p3051 ∨ (¬ p4344) ∨ p2839 ∨ (¬ p2140))
    : (¬ p2707) ∨ p3051 ∨ p2839 ∨ (¬ p4344) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2140 := h105364;
    (Or.elim h99675 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124642 (p2132 p2241 p2744 p2870 p2881 p3366 p3399 p3631 p4668 : Prop)
    (h106503 : p2744)
    (h105414 : p4668)
    (h99704 : (¬ p3631) ∨ p2132 ∨ p2241 ∨ p2881 ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p4668) ∨ p2870 ∨ (¬ p3399))
    : (¬ p3631) ∨ (¬ p3399) ∨ p2241 ∨ p2132 ∨ p2881 ∨ p2870 ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2744 := h106503;
    let u8 : p4668 := h105414;
    (Or.elim h99704 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step124643 (p2132 p2241 p2619 p2744 p3146 p3366 p3399 p3631 p3950 : Prop)
    (h106503 : p2744)
    (h99706 : (¬ p3399) ∨ p2241 ∨ p2132 ∨ (¬ p3950) ∨ p2619 ∨ p3146 ∨ (¬ p2744) ∨ (¬ p3631) ∨ (¬ p3366))
    : (¬ p3631) ∨ p2619 ∨ (¬ p3399) ∨ (¬ p3366) ∨ p2132 ∨ p3146 ∨ p2241 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    (Or.elim h99706 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step124644 (p2132 p2870 p2881 p3366 p3379 p3399 p3631 p4376 p4668 : Prop)
    (h105414 : p4668)
    (h106320 : p4376)
    (h99708 : (¬ p3631) ∨ p2132 ∨ p3379 ∨ p2870 ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p4668) ∨ p2881 ∨ (¬ p4376))
    : (¬ p3631) ∨ (¬ p3399) ∨ p2870 ∨ p2132 ∨ p3379 ∨ p2881 ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4668 := h105414;
    let u8 : p4376 := h106320;
    (Or.elim h99708 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step124645 (p2132 p2241 p2744 p2870 p2881 p3083 p3366 p3379 p3487 p4420 : Prop)
    (h106503 : p2744)
    (h105707 : p4420)
    (h99710 : p2132 ∨ (¬ p3487) ∨ (¬ p4420) ∨ (¬ p2744) ∨ (¬ p3366) ∨ p2241 ∨ p2881 ∨ (¬ p3379) ∨ p2870 ∨ (¬ p3083))
    : p2132 ∨ p2870 ∨ (¬ p3366) ∨ (¬ p3379) ∨ p2241 ∨ (¬ p3487) ∨ (¬ p3083) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4420 := h105707;
    (Or.elim h99710 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step124646 (p2132 p2187 p2246 p2437 p2651 p2744 p2860 p2911 p3366 p4503 : Prop)
    (h106503 : p2744)
    (h106530 : p4503)
    (h99712 : p2132 ∨ (¬ p3366) ∨ (¬ p2437) ∨ (¬ p2744) ∨ p2187 ∨ (¬ p2246) ∨ p2860 ∨ (¬ p4503) ∨ (¬ p2911) ∨ (¬ p2651))
    : p2860 ∨ (¬ p2437) ∨ p2187 ∨ p2132 ∨ (¬ p2246) ∨ (¬ p2911) ∨ (¬ p2651) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4503 := h106530;
    (Or.elim h99712 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step124648 (p2132 p2761 p2860 p3125 p3266 p3366 p3516 p3519 p4376 p4604 p5201 : Prop)
    (h106320 : p4376)
    (h106293 : p4604)
    (h99717 : p3266 ∨ (¬ p2761) ∨ p2860 ∨ (¬ p5201) ∨ (¬ p3519) ∨ (¬ p3366) ∨ p2132 ∨ (¬ p4376) ∨ (¬ p4604) ∨ p3125 ∨ (¬ p3516))
    : (¬ p5201) ∨ (¬ p3519) ∨ (¬ p2761) ∨ p2132 ∨ p3266 ∨ (¬ p3516) ∨ (¬ p3366) ∨ p2860 ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    let u10 : p4604 := h106293;
    (Or.elim h99717 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u8 q9))) (fun r9 => (False.elim (r9 u5)))))))))))))))))))))))

theorem step124649 (p2132 p2241 p2449 p2619 p2744 p3037 p3146 p3366 p3399 p3950 : Prop)
    (h106503 : p2744)
    (h99719 : (¬ p3399) ∨ p2132 ∨ (¬ p3950) ∨ p2619 ∨ p3146 ∨ (¬ p2744) ∨ (¬ p2449) ∨ (¬ p3366) ∨ p2241 ∨ (¬ p3037))
    : p2132 ∨ (¬ p3399) ∨ (¬ p3037) ∨ (¬ p2449) ∨ p2619 ∨ p3146 ∨ (¬ p3366) ∨ p2241 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    (Or.elim h99719 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step124650 (p2132 p2241 p2619 p2744 p3093 p3146 p3319 p3366 p4330 : Prop)
    (h106503 : p2744)
    (h106329 : p4330)
    (h99720 : (¬ p3319) ∨ p3146 ∨ (¬ p2744) ∨ (¬ p4330) ∨ p2619 ∨ (¬ p3366) ∨ (¬ p3093) ∨ p2132 ∨ p2241)
    : p2619 ∨ p2132 ∨ p3146 ∨ (¬ p3319) ∨ (¬ p3093) ∨ (¬ p3366) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2744 := h106503;
    let u8 : p4330 := h106329;
    (Or.elim h99720 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (False.elim (u6 r7)))))))))))))))))))

theorem step124652 (p2132 p2246 p2264 p2341 p2449 p2744 p2860 p3125 p3366 p4104 p4625 : Prop)
    (h106503 : p2744)
    (h106455 : p4625)
    (h99744 : (¬ p2341) ∨ p2132 ∨ (¬ p3366) ∨ p2860 ∨ (¬ p4625) ∨ (¬ p4104) ∨ (¬ p2744) ∨ (¬ p2246) ∨ p2264 ∨ p3125 ∨ (¬ p2449))
    : p3125 ∨ p2132 ∨ (¬ p2341) ∨ (¬ p2246) ∨ p2264 ∨ (¬ p2449) ∨ (¬ p3366) ∨ p2860 ∨ (¬ p4104) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    let u10 : p4625 := h106455;
    (Or.elim h99744 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u0 q9))) (fun r9 => (False.elim (r9 u5)))))))))))))))))))))))

theorem step124659 (p2417 p2696 p2753 p2761 p2829 p3363 p3389 p3914 p4752 p5250 : Prop)
    (h105434 : p4752)
    (h99761 : (¬ p3914) ∨ p2753 ∨ (¬ p5250) ∨ (¬ p3363) ∨ p2761 ∨ (¬ p2829) ∨ p3389 ∨ p2696 ∨ (¬ p4752) ∨ p2417)
    : (¬ p3914) ∨ p2753 ∨ p3389 ∨ p2417 ∨ (¬ p2829) ∨ (¬ p5250) ∨ (¬ p3363) ∨ p2761 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2753) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4752 := h105434;
    (Or.elim h99761 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u3 r8)))))))))))))))))))))

theorem step124662 (p2470 p2528 p2696 p2753 p2829 p3266 p3363 p3914 p4752 p5250 : Prop)
    (h105434 : p4752)
    (h99769 : (¬ p3914) ∨ p3266 ∨ p2528 ∨ p2696 ∨ (¬ p2829) ∨ p2470 ∨ p2753 ∨ (¬ p3363) ∨ (¬ p4752) ∨ (¬ p5250))
    : (¬ p3914) ∨ p2753 ∨ p2470 ∨ p3266 ∨ (¬ p5250) ∨ p2528 ∨ p2696 ∨ (¬ p3363) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2753) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4752 := h105434;
    (Or.elim h99769 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step124674 (p2246 p2598 p2744 p2946 p3156 p3276 p3366 p3969 p5119 p5160 : Prop)
    (h106503 : p2744)
    (h99807 : (¬ p3969) ∨ p3276 ∨ (¬ p2946) ∨ (¬ p5160) ∨ (¬ p3156) ∨ p2598 ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p5119))
    : (¬ p5160) ∨ (¬ p3969) ∨ (¬ p5119) ∨ p2598 ∨ (¬ p3366) ∨ (¬ p2246) ∨ p3276 ∨ (¬ p3156) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5160 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    (Or.elim h99807 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step124676 (p2727 p2992 p3016 p3879 p4717 : Prop)
    (h105424 : p4717)
    (h99817 : p2992 ∨ (¬ p3016) ∨ (¬ p2727) ∨ (¬ p3879) ∨ (¬ p4717))
    : p2992 ∨ (¬ p3879) ∨ (¬ p3016) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4717 := h105424;
    (Or.elim h99817 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124679 (p2459 p2741 p2911 p2992 p3136 p3389 p3519 p3755 p4376 p5113 : Prop)
    (h106320 : p4376)
    (h105481 : p5113)
    (h99831 : (¬ p2911) ∨ (¬ p5113) ∨ p2992 ∨ (¬ p3136) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2741) ∨ (¬ p2459) ∨ p3755 ∨ (¬ p3389))
    : p3755 ∨ (¬ p3519) ∨ (¬ p3389) ∨ (¬ p2911) ∨ (¬ p2741) ∨ (¬ p2459) ∨ p2992 ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p5113 := h105481;
    (Or.elim h99831 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u0 q8))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step124681 (p2253 p2741 p2946 p2992 p3379 p4376 : Prop)
    (h106320 : p4376)
    (h99834 : p2992 ∨ p3379 ∨ (¬ p2741) ∨ (¬ p4376) ∨ (¬ p2946) ∨ (¬ p2253))
    : p2992 ∨ (¬ p2946) ∨ (¬ p2253) ∨ p3379 ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4376 := h106320;
    (Or.elim h99834 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step124687 (p2417 p2761 p3461 p4025 p4712 : Prop)
    (h105422 : p4712)
    (h99857 : p3461 ∨ (¬ p2761) ∨ (¬ p4712) ∨ (¬ p4025) ∨ (¬ p2417))
    : p3461 ∨ (¬ p4025) ∨ (¬ p2761) ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4712 := h105422;
    (Or.elim h99857 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124688 (p2230 p2563 p2761 p3125 p3286 p4236 p4419 p4621 p5284 : Prop)
    (h105407 : p4621)
    (h99861 : (¬ p5284) ∨ (¬ p2761) ∨ (¬ p4236) ∨ (¬ p2563) ∨ (¬ p2230) ∨ p3286 ∨ (¬ p3125) ∨ (¬ p4419) ∨ (¬ p4621))
    : (¬ p5284) ∨ (¬ p4236) ∨ (¬ p2230) ∨ (¬ p3125) ∨ p3286 ∨ (¬ p2563) ∨ (¬ p2761) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4621 := h105407;
    (Or.elim h99861 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step124690 (p2284 p2761 p2946 p3125 p3266 p3516 p3819 p4604 p4789 : Prop)
    (h106293 : p4604)
    (h105646 : p4789)
    (h99876 : p3266 ∨ (¬ p2761) ∨ p3125 ∨ (¬ p4604) ∨ (¬ p4789) ∨ (¬ p3516) ∨ (¬ p3819) ∨ p2284 ∨ p2946)
    : p3125 ∨ p2284 ∨ p3266 ∨ (¬ p2761) ∨ (¬ p3516) ∨ p2946 ∨ (¬ p3819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4604 := h106293;
    let u8 : p4789 := h105646;
    (Or.elim h99876 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (False.elim (u5 r7)))))))))))))))))))

theorem step124693 (p2761 p2797 p3051 p3136 p3246 p3370 p3953 p4228 p4377 p4435 : Prop)
    (h106170 : p4377)
    (h99887 : (¬ p4228) ∨ (¬ p4435) ∨ (¬ p3953) ∨ (¬ p2761) ∨ (¬ p3370) ∨ (¬ p3051) ∨ (¬ p2797) ∨ p3136 ∨ (¬ p3246) ∨ (¬ p4377))
    : (¬ p4435) ∨ (¬ p3370) ∨ (¬ p2761) ∨ p3136 ∨ (¬ p4228) ∨ (¬ p3051) ∨ (¬ p3953) ∨ (¬ p2797) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4435 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4377 := h106170;
    (Or.elim h99887 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step124695 (p2352 p2363 p2573 p2761 p3286 p4236 p4419 p4669 p5284 : Prop)
    (h105415 : p4669)
    (h99897 : (¬ p5284) ∨ (¬ p2352) ∨ p3286 ∨ (¬ p2573) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p2761) ∨ (¬ p4669) ∨ (¬ p2363))
    : (¬ p4236) ∨ (¬ p5284) ∨ (¬ p2352) ∨ (¬ p2761) ∨ p3286 ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4669 := h105415;
    (Or.elim h99897 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step124702 (p2137 p2220 p2449 p2696 p2748 p2839 p2996 p3146 p4669 : Prop)
    (h105415 : p4669)
    (h99930 : (¬ p2839) ∨ (¬ p3146) ∨ (¬ p2220) ∨ (¬ p2996) ∨ (¬ p2137) ∨ p2696 ∨ p2449 ∨ (¬ p2748) ∨ (¬ p4669))
    : (¬ p2137) ∨ (¬ p2748) ∨ (¬ p2996) ∨ (¬ p2839) ∨ p2449 ∨ p2696 ∨ (¬ p3146) ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4669 := h105415;
    (Or.elim h99930 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step124704 (p2230 p2373 p2685 p2741 p2996 p3146 p3519 p3755 p4376 p5113 : Prop)
    (h106320 : p4376)
    (h105481 : p5113)
    (h99936 : (¬ p3519) ∨ p3755 ∨ (¬ p2373) ∨ (¬ p5113) ∨ (¬ p2741) ∨ (¬ p2685) ∨ (¬ p2996) ∨ (¬ p2230) ∨ (¬ p4376) ∨ (¬ p3146))
    : p3755 ∨ (¬ p2685) ∨ (¬ p2230) ∨ (¬ p2741) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p2996) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p5113 := h105481;
    (Or.elim h99936 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step124705 (p2696 p2745 p2996 p3425 p4325 : Prop)
    (h105523 : p2745)
    (h99937 : p3425 ∨ (¬ p2996) ∨ (¬ p4325) ∨ (¬ p2745) ∨ p2696)
    : p3425 ∨ p2696 ∨ (¬ p4325) ∨ (¬ p2996) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    (Or.elim h99937 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step124706 (p2253 p2741 p2807 p2996 p3379 p4376 : Prop)
    (h106320 : p4376)
    (h99939 : (¬ p2996) ∨ (¬ p2253) ∨ (¬ p2741) ∨ (¬ p4376) ∨ (¬ p2807) ∨ p3379)
    : (¬ p2741) ∨ p3379 ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p2253) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2741 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4376 := h106320;
    (Or.elim h99939 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u1 r4)))))))))))))

theorem step124708 (p2255 p2449 p2996 p3516 p4104 : Prop)
    (h105367 : p2255)
    (h99941 : (¬ p3516) ∨ (¬ p2996) ∨ (¬ p2255) ∨ (¬ p4104) ∨ p2449)
    : (¬ p3516) ∨ (¬ p2996) ∨ (¬ p4104) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2255 := h105367;
    (Or.elim h99941 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step124709 (p2449 p2745 p2996 p3434 p4781 : Prop)
    (h105523 : p2745)
    (h99945 : (¬ p3434) ∨ (¬ p2996) ∨ (¬ p2745) ∨ (¬ p4781) ∨ p2449)
    : (¬ p3434) ∨ (¬ p4781) ∨ p2449 ∨ (¬ p2996) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    (Or.elim h99945 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step124710 (p2253 p2608 p2750 p2807 p2996 : Prop)
    (h106345 : p2750)
    (h99947 : p2608 ∨ (¬ p2253) ∨ (¬ p2807) ∨ (¬ p2750) ∨ (¬ p2996))
    : p2608 ∨ (¬ p2253) ∨ (¬ p2807) ∨ (¬ p2996) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2750 := h106345;
    (Or.elim h99947 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124713 (p2122 p2177 p2241 p2449 p2774 p2996 p4666 p4733 : Prop)
    (h105430 : p4733)
    (h105658 : p4666)
    (h99952 : (¬ p2996) ∨ p2241 ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p4666) ∨ (¬ p4733) ∨ p2449 ∨ (¬ p2774))
    : (¬ p2996) ∨ (¬ p2122) ∨ (¬ p2177) ∨ p2241 ∨ (¬ p2774) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4733 := h105430;
    let u7 : p4666 := h105658;
    (Or.elim h99952 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step124714 (p2132 p2241 p2449 p2870 p2881 p2996 p4666 p4733 : Prop)
    (h105430 : p4733)
    (h105658 : p4666)
    (h99953 : (¬ p2996) ∨ p2241 ∨ (¬ p2132) ∨ (¬ p4733) ∨ (¬ p4666) ∨ (¬ p2870) ∨ p2449 ∨ (¬ p2881))
    : (¬ p2996) ∨ p2241 ∨ (¬ p2881) ∨ p2449 ∨ (¬ p2870) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4733 := h105430;
    let u7 : p4666 := h105658;
    (Or.elim h99953 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step124720 (p2156 p2246 p2284 p2744 p2958 p3156 p3201 p3366 p3389 p3641 p3905 p4434 : Prop)
    (h106503 : p2744)
    (h106144 : p4434)
    (h99988 : (¬ p3156) ∨ p2284 ∨ (¬ p2156) ∨ p3389 ∨ (¬ p2246) ∨ (¬ p2958) ∨ (¬ p4434) ∨ (¬ p2744) ∨ (¬ p3201) ∨ p3641 ∨ (¬ p3905) ∨ (¬ p3366))
    : p3641 ∨ (¬ p3201) ∨ p2284 ∨ (¬ p2958) ∨ (¬ p2246) ∨ (¬ p2156) ∨ p3389 ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3905) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    let u11 : p4434 := h106144;
    (Or.elim h99988 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u0 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u8)))))))))))))))))))))))))

theorem step124721 (p2255 p2363 p2662 p2727 p2911 p3166 p3256 p3389 p4133 : Prop)
    (h105367 : p2255)
    (h105712 : p4133)
    (h99989 : (¬ p3256) ∨ p2363 ∨ p2911 ∨ (¬ p3166) ∨ p3389 ∨ (¬ p4133) ∨ (¬ p2255) ∨ p2727 ∨ (¬ p2662))
    : (¬ p2662) ∨ p3389 ∨ p2911 ∨ p2727 ∨ (¬ p3256) ∨ p2363 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2255 := h105367;
    let u8 : p4133 := h105712;
    (Or.elim h99989 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step124722 (p2187 p2192 p2255 p2662 p2727 p2911 p2946 p3389 p3412 p4133 : Prop)
    (h105367 : p2255)
    (h105712 : p4133)
    (h99990 : p2911 ∨ p2727 ∨ (¬ p2187) ∨ (¬ p3412) ∨ (¬ p2255) ∨ (¬ p2192) ∨ (¬ p4133) ∨ (¬ p2946) ∨ (¬ p2662) ∨ p3389)
    : p3389 ∨ (¬ p2192) ∨ p2911 ∨ (¬ p2187) ∨ (¬ p2946) ∨ p2727 ∨ (¬ p2662) ∨ (¬ p3412) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2255 := h105367;
    let u9 : p4133 := h105712;
    (Or.elim h99990 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (u0 r8)))))))))))))))))))))

theorem step124723 (p2459 p2696 p2753 p2797 p2911 p3323 p3347 p3389 p4330 : Prop)
    (h106329 : p4330)
    (h99992 : p2911 ∨ (¬ p2753) ∨ (¬ p3347) ∨ p2459 ∨ (¬ p2696) ∨ (¬ p3323) ∨ (¬ p2797) ∨ (¬ p4330) ∨ p3389)
    : p2911 ∨ (¬ p2696) ∨ (¬ p2753) ∨ p2459 ∨ (¬ p3323) ∨ (¬ p3347) ∨ (¬ p2797) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4330 := h106329;
    (Or.elim h99992 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (u7 r7)))))))))))))))))))

theorem step124726 (p2210 p2253 p2741 p3166 p3189 p4377 : Prop)
    (h106170 : p4377)
    (h100005 : (¬ p2253) ∨ (¬ p3166) ∨ p3189 ∨ p2210 ∨ (¬ p4377) ∨ (¬ p2741))
    : p3189 ∨ (¬ p2741) ∨ p2210 ∨ (¬ p2253) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4377 := h106170;
    (Or.elim h100005 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step124727 (p2210 p2253 p2651 p2727 p2741 p4377 : Prop)
    (h106170 : p4377)
    (h100006 : p2727 ∨ p2210 ∨ (¬ p4377) ∨ (¬ p2741) ∨ (¬ p2253) ∨ (¬ p2651))
    : (¬ p2651) ∨ p2727 ∨ (¬ p2741) ∨ p2210 ∨ (¬ p2253) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4377 := h106170;
    (Or.elim h100006 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step124728 (p2253 p2741 p3166 p3189 p3379 p4376 : Prop)
    (h106320 : p4376)
    (h100008 : p3189 ∨ (¬ p3166) ∨ (¬ p2253) ∨ p3379 ∨ (¬ p4376) ∨ (¬ p2741))
    : p3189 ∨ (¬ p2741) ∨ (¬ p3166) ∨ p3379 ∨ (¬ p2253) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4376 := h106320;
    (Or.elim h100008 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step124729 (p2253 p2608 p2750 p3166 p3189 : Prop)
    (h106345 : p2750)
    (h100010 : p3189 ∨ p2608 ∨ (¬ p2750) ∨ (¬ p2253) ∨ (¬ p3166))
    : p3189 ∨ (¬ p2253) ∨ (¬ p3166) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2750 := h106345;
    (Or.elim h100010 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124731 (p2253 p2331 p2608 p2641 p2750 : Prop)
    (h106345 : p2750)
    (h100014 : p2641 ∨ p2608 ∨ (¬ p2253) ∨ (¬ p2750) ∨ (¬ p2331))
    : p2608 ∨ (¬ p2253) ∨ p2641 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2750 := h106345;
    (Or.elim h100014 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124737 (p2331 p2363 p2417 p2598 p2668 p3201 p4669 p4786 : Prop)
    (h105415 : p4669)
    (h106425 : p4786)
    (h100041 : p2417 ∨ (¬ p2668) ∨ (¬ p2331) ∨ p3201 ∨ (¬ p4669) ∨ (¬ p4786) ∨ p2598 ∨ (¬ p2363))
    : p3201 ∨ p2417 ∨ (¬ p2331) ∨ (¬ p2363) ∨ p2598 ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4669 := h105415;
    let u7 : p4786 := h106425;
    (Or.elim h100041 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step124738 (p2417 p2696 p2742 p3189 p3256 p3363 p3367 p3389 p4669 : Prop)
    (h105415 : p4669)
    (h100042 : (¬ p3256) ∨ (¬ p3189) ∨ (¬ p2696) ∨ p2417 ∨ (¬ p4669) ∨ (¬ p3363) ∨ p3367 ∨ (¬ p2742) ∨ p3389)
    : (¬ p3363) ∨ (¬ p2696) ∨ p3389 ∨ (¬ p2742) ∨ p2417 ∨ p3367 ∨ (¬ p3189) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4669 := h105415;
    (Or.elim h100042 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (u2 r7)))))))))))))))))))

theorem step124739 (p2177 p2396 p2417 p2881 p4277 : Prop)
    (h105380 : p4277)
    (h100043 : p2417 ∨ (¬ p2396) ∨ p2177 ∨ (¬ p4277) ∨ (¬ p2881))
    : p2417 ∨ p2177 ∨ (¬ p2881) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4277 := h105380;
    (Or.elim h100043 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124741 (p2132 p2417 p2860 p2922 p3125 p3379 p4621 p4733 : Prop)
    (h105430 : p4733)
    (h105407 : p4621)
    (h100050 : p2922 ∨ p2417 ∨ (¬ p2132) ∨ (¬ p4621) ∨ (¬ p3125) ∨ p3379 ∨ (¬ p2860) ∨ (¬ p4733))
    : p2922 ∨ p2417 ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p2132) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4733 := h105430;
    let u7 : p4621 := h105407;
    (Or.elim h100050 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124750 (p2252 p2417 p2437 p2651 p2750 p3212 p3370 p3371 p3461 p3680 p4621 : Prop)
    (h106345 : p2750)
    (h105407 : p4621)
    (h100067 : (¬ p3370) ∨ p3461 ∨ (¬ p2750) ∨ p2437 ∨ (¬ p2252) ∨ (¬ p3371) ∨ (¬ p3212) ∨ p2417 ∨ p2651 ∨ (¬ p3680) ∨ (¬ p4621))
    : (¬ p3680) ∨ (¬ p3212) ∨ p2437 ∨ (¬ p2252) ∨ p2651 ∨ p3461 ∨ (¬ p3370) ∨ p2417 ∨ (¬ p3371) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2750 := h106345;
    let u10 : p4621 := h105407;
    (Or.elim h100067 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step124753 (p2248 p2417 p2922 p3286 p3379 p3506 p4322 p4395 : Prop)
    (h105365 : p2248)
    (h100079 : (¬ p4322) ∨ p2417 ∨ (¬ p3286) ∨ (¬ p4395) ∨ p3379 ∨ (¬ p3506) ∨ p2922 ∨ (¬ p2248))
    : (¬ p3506) ∨ p3379 ∨ p2922 ∨ (¬ p3286) ∨ p2417 ∨ (¬ p4395) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    (Or.elim h100079 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124754 (p2248 p2417 p2881 p2901 p2922 p2946 p3379 p4666 : Prop)
    (h105365 : p2248)
    (h105658 : p4666)
    (h100080 : p2922 ∨ p2417 ∨ p3379 ∨ (¬ p2248) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p4666) ∨ (¬ p2946))
    : p2922 ∨ p2417 ∨ (¬ p2881) ∨ (¬ p2946) ∨ p3379 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4666 := h105658;
    (Or.elim h100080 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step124758 (p2177 p2248 p2295 p2331 p2417 p2922 p3379 p4666 : Prop)
    (h105365 : p2248)
    (h105658 : p4666)
    (h100088 : p2922 ∨ p2417 ∨ (¬ p2331) ∨ p3379 ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p4666) ∨ (¬ p2177))
    : p2922 ∨ p2417 ∨ (¬ p2295) ∨ (¬ p2177) ∨ p3379 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4666 := h105658;
    (Or.elim h100088 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step124762 (p2417 p2911 p3941 p4445 p5122 : Prop)
    (h105483 : p5122)
    (h100096 : p2417 ∨ (¬ p2911) ∨ (¬ p5122) ∨ (¬ p3941) ∨ (¬ p4445))
    : (¬ p3941) ∨ p2417 ∨ (¬ p2911) ∨ (¬ p4445) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5122 := h105483;
    (Or.elim h100096 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124763 (p2264 p2352 p2363 p2449 p2573 p2696 p3434 p3589 p4781 p5193 : Prop)
    (h105488 : p5193)
    (h100117 : (¬ p3434) ∨ p2449 ∨ p2363 ∨ (¬ p2696) ∨ (¬ p2264) ∨ p2573 ∨ (¬ p5193) ∨ (¬ p3589) ∨ (¬ p4781) ∨ p2352)
    : (¬ p3434) ∨ (¬ p4781) ∨ (¬ p3589) ∨ p2363 ∨ (¬ p2696) ∨ p2352 ∨ p2449 ∨ (¬ p2264) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5193 := h105488;
    (Or.elim h100117 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (u5 r8)))))))))))))))))))))

theorem step124766 (p2449 p2761 p3680 p4192 p4280 : Prop)
    (h105599 : p4280)
    (h100120 : p2761 ∨ (¬ p3680) ∨ (¬ p4192) ∨ p2449 ∨ (¬ p4280))
    : (¬ p3680) ∨ (¬ p4192) ∨ p2449 ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4280 := h105599;
    (Or.elim h100120 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124768 (p2449 p2761 p3192 p3276 p4327 : Prop)
    (h105381 : p4327)
    (h100125 : p2761 ∨ (¬ p3276) ∨ (¬ p4327) ∨ p2449 ∨ (¬ p3192))
    : (¬ p3276) ∨ (¬ p3192) ∨ p2449 ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4327 := h105381;
    (Or.elim h100125 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124770 (p2264 p2363 p2449 p4445 p4503 : Prop)
    (h106530 : p4503)
    (h100128 : p2449 ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p4445) ∨ (¬ p4503))
    : (¬ p2363) ∨ (¬ p4445) ∨ (¬ p2264) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4503 := h106530;
    (Or.elim h100128 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124773 (p2166 p2210 p2449 p2685 p2696 p3146 p4669 p4736 : Prop)
    (h105431 : p4736)
    (h105415 : p4669)
    (h100156 : p2449 ∨ p2685 ∨ p2696 ∨ (¬ p3146) ∨ (¬ p2210) ∨ (¬ p2166) ∨ (¬ p4736) ∨ (¬ p4669))
    : p2685 ∨ p2696 ∨ (¬ p2210) ∨ p2449 ∨ (¬ p2166) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4669 := h105415;
    (Or.elim h100156 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124774 (p2449 p2685 p2696 p3193 p3266 p3276 p3366 p4376 p4669 : Prop)
    (h106320 : p4376)
    (h105415 : p4669)
    (h100158 : p3193 ∨ p3266 ∨ p2696 ∨ p2685 ∨ (¬ p4669) ∨ (¬ p3276) ∨ (¬ p3366) ∨ p2449 ∨ (¬ p4376))
    : p3193 ∨ (¬ p3276) ∨ p2696 ∨ p2685 ∨ p2449 ∨ p3266 ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4376 := h106320;
    let u8 : p4669 := h105415;
    (Or.elim h100158 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step124776 (p2352 p2363 p2449 p2573 p2685 p2696 p3366 p3519 p4376 p4669 : Prop)
    (h106320 : p4376)
    (h105415 : p4669)
    (h100161 : p2685 ∨ (¬ p2352) ∨ p2696 ∨ (¬ p4376) ∨ (¬ p3519) ∨ (¬ p3366) ∨ (¬ p4669) ∨ (¬ p2363) ∨ (¬ p2573) ∨ p2449)
    : p2696 ∨ p2685 ∨ (¬ p2573) ∨ (¬ p3366) ∨ p2449 ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p4669 := h105415;
    (Or.elim h100161 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (u4 r8)))))))))))))))))))))

theorem step124777 (p2210 p2449 p2685 p2696 p2881 p2891 p4666 p4736 : Prop)
    (h105431 : p4736)
    (h105658 : p4666)
    (h100164 : p2449 ∨ (¬ p2881) ∨ (¬ p4736) ∨ (¬ p2891) ∨ p2696 ∨ p2685 ∨ (¬ p2210) ∨ (¬ p4666))
    : p2685 ∨ p2696 ∨ (¬ p2881) ∨ p2449 ∨ (¬ p2891) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4666 := h105658;
    (Or.elim h100164 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124778 (p2166 p2210 p2254 p2449 p2761 p2807 p3969 p5119 : Prop)
    (h105366 : p2254)
    (h100167 : p2761 ∨ (¬ p3969) ∨ (¬ p2166) ∨ p2807 ∨ p2449 ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p5119))
    : (¬ p3969) ∨ (¬ p2166) ∨ p2449 ∨ p2761 ∨ (¬ p2210) ∨ p2807 ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h100167 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124781 (p2230 p2427 p2449 p2685 p2696 p2881 p4419 p4666 : Prop)
    (h105658 : p4666)
    (h100175 : p2449 ∨ (¬ p2881) ∨ p2696 ∨ (¬ p4419) ∨ p2685 ∨ (¬ p2427) ∨ (¬ p2230) ∨ (¬ p4666))
    : p2696 ∨ p2685 ∨ (¬ p2881) ∨ (¬ p2427) ∨ (¬ p2230) ∨ (¬ p4419) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4666 := h105658;
    (Or.elim h100175 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124783 (p2187 p2383 p2449 p2685 p2696 p2781 p3125 p4621 : Prop)
    (h105407 : p4621)
    (h100181 : p2449 ∨ p2685 ∨ (¬ p3125) ∨ p2187 ∨ (¬ p4621) ∨ (¬ p2383) ∨ (¬ p2781) ∨ p2696)
    : p2685 ∨ p2696 ∨ (¬ p2781) ∨ p2449 ∨ (¬ p3125) ∨ p2187 ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4621 := h105407;
    (Or.elim h100181 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step124785 (p2727 p2748 p3136 p3343 p4241 p4949 : Prop)
    (h105463 : p4949)
    (h100216 : (¬ p2748) ∨ p2727 ∨ (¬ p3136) ∨ p3343 ∨ (¬ p4949) ∨ (¬ p4241))
    : (¬ p2748) ∨ p2727 ∨ p3343 ∨ (¬ p3136) ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2748 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4949 := h105463;
    (Or.elim h100216 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step124787 (p2651 p2727 p2745 p2946 p3136 : Prop)
    (h105523 : p2745)
    (h100226 : (¬ p2651) ∨ p2946 ∨ (¬ p2745) ∨ p2727 ∨ (¬ p3136))
    : (¬ p3136) ∨ (¬ p2651) ∨ p2727 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    (Or.elim h100226 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step124788 (p2241 p2727 p2819 p3083 p3654 p3917 p4384 p5017 : Prop)
    (h106167 : p4384)
    (h100242 : (¬ p3917) ∨ (¬ p5017) ∨ p2241 ∨ p2727 ∨ (¬ p3654) ∨ (¬ p2819) ∨ p3083 ∨ (¬ p4384))
    : p3083 ∨ p2727 ∨ (¬ p5017) ∨ (¬ p3917) ∨ p2241 ∨ (¬ p3654) ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4384 := h106167;
    (Or.elim h100242 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124791 (p2241 p2761 p3189 p3256 p3276 p3355 p3950 p5190 : Prop)
    (h105487 : p5190)
    (h100254 : p2241 ∨ p3189 ∨ (¬ p3276) ∨ p2761 ∨ (¬ p5190) ∨ (¬ p3355) ∨ (¬ p3950) ∨ p3256)
    : (¬ p3276) ∨ (¬ p3355) ∨ p3189 ∨ p2761 ∨ p3256 ∨ p2241 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5190 := h105487;
    (Or.elim h100254 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step124793 (p2295 p2750 p2753 p3276 p3309 p3323 p3355 p3362 p4245 p4322 p4397 : Prop)
    (h106345 : p2750)
    (h100262 : (¬ p4322) ∨ (¬ p3276) ∨ (¬ p2295) ∨ (¬ p2753) ∨ (¬ p4245) ∨ (¬ p3362) ∨ (¬ p2750) ∨ (¬ p4397) ∨ p3323 ∨ (¬ p3355) ∨ p3309)
    : (¬ p3276) ∨ (¬ p3355) ∨ (¬ p2295) ∨ (¬ p4245) ∨ (¬ p4322) ∨ p3309 ∨ (¬ p2753) ∨ p3323 ∨ (¬ p3362) ∨ (¬ p4397) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4397 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2750 := h106345;
    (Or.elim h100262 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (False.elim (u5 r9)))))))))))))))))))))))

theorem step124795 (p2122 p2246 p2651 p2744 p2774 p3276 p3343 p3366 p4260 p4831 : Prop)
    (h106503 : p2744)
    (h105445 : p4831)
    (h100266 : (¬ p4260) ∨ p2774 ∨ (¬ p3276) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p4831) ∨ (¬ p2246) ∨ (¬ p3343) ∨ p2122 ∨ (¬ p3366))
    : (¬ p4260) ∨ (¬ p3343) ∨ (¬ p2246) ∨ (¬ p2651) ∨ p2774 ∨ (¬ p3366) ∨ (¬ p3276) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4831 := h105445;
    (Or.elim h100266 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step124800 (p2248 p2651 p3093 p3276 p3343 p3923 p5123 p5580 : Prop)
    (h105365 : p2248)
    (h100271 : (¬ p5580) ∨ (¬ p3343) ∨ (¬ p5123) ∨ p3093 ∨ (¬ p2651) ∨ (¬ p3923) ∨ (¬ p3276) ∨ (¬ p2248))
    : (¬ p3276) ∨ p3093 ∨ (¬ p2651) ∨ (¬ p3343) ∨ (¬ p3923) ∨ (¬ p5580) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    (Or.elim h100271 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124801 (p3276 p3461 p3917 p4422 p5222 : Prop)
    (h105793 : p5222)
    (h100277 : p3461 ∨ (¬ p3276) ∨ (¬ p4422) ∨ (¬ p5222) ∨ (¬ p3917))
    : (¬ p3276) ∨ (¬ p4422) ∨ (¬ p3917) ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5222 := h105793;
    (Or.elim h100277 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124802 (p3276 p3323 p3461 p4422 p4973 : Prop)
    (h105835 : p4973)
    (h100278 : (¬ p3276) ∨ p3461 ∨ (¬ p4422) ∨ (¬ p4973) ∨ p3323)
    : (¬ p3276) ∨ (¬ p4422) ∨ p3461 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4973 := h105835;
    (Or.elim h100278 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step124804 (p2241 p2761 p3189 p3192 p3256 p3276 p3389 p3950 p5190 : Prop)
    (h105487 : p5190)
    (h100282 : p2761 ∨ (¬ p3192) ∨ p3256 ∨ (¬ p3276) ∨ p2241 ∨ (¬ p5190) ∨ (¬ p3950) ∨ p3189 ∨ (¬ p3389))
    : (¬ p3276) ∨ (¬ p3389) ∨ p2761 ∨ p2241 ∨ p3256 ∨ p3189 ∨ (¬ p3950) ∨ (¬ p3192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5190 := h105487;
    (Or.elim h100282 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step124805 (p2252 p2741 p3073 p3286 p3379 p3449 p3461 p4376 p4604 p5284 : Prop)
    (h106320 : p4376)
    (h106293 : p4604)
    (h100291 : (¬ p5284) ∨ (¬ p3073) ∨ (¬ p4604) ∨ p3379 ∨ (¬ p4376) ∨ (¬ p3461) ∨ (¬ p2252) ∨ p3286 ∨ (¬ p2741) ∨ (¬ p3449))
    : (¬ p2252) ∨ (¬ p3073) ∨ p3379 ∨ (¬ p3449) ∨ (¬ p3461) ∨ (¬ p5284) ∨ p3286 ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p4604 := h106293;
    (Or.elim h100291 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step124807 (p3146 p3266 p3461 p3990 p4433 : Prop)
    (h106150 : p4433)
    (h100293 : p3266 ∨ p3146 ∨ (¬ p3990) ∨ (¬ p3461) ∨ (¬ p4433))
    : (¬ p3461) ∨ p3266 ∨ (¬ p3990) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4433 := h106150;
    (Or.elim h100293 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124808 (p2459 p3266 p3461 p3990 p4503 : Prop)
    (h106530 : p4503)
    (h100295 : p3266 ∨ (¬ p3461) ∨ (¬ p3990) ∨ p2459 ∨ (¬ p4503))
    : (¬ p3461) ∨ (¬ p3990) ∨ p3266 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4503 := h106530;
    (Or.elim h100295 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124813 (p2264 p2459 p2807 p3276 p3346 p3461 p3905 p4604 p4786 : Prop)
    (h106293 : p4604)
    (h106425 : p4786)
    (h100308 : p3276 ∨ (¬ p3461) ∨ (¬ p4604) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3346) ∨ (¬ p2264) ∨ (¬ p3905) ∨ (¬ p4786))
    : (¬ p3905) ∨ (¬ p3346) ∨ p3276 ∨ (¬ p2807) ∨ (¬ p3461) ∨ (¬ p2459) ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3905 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4604 := h106293;
    let u8 : p4786 := h106425;
    (Or.elim h100308 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step124814 (p2761 p3246 p3461 p4187 p4556 : Prop)
    (h105399 : p4556)
    (h100309 : p2761 ∨ (¬ p4187) ∨ (¬ p3461) ∨ p3246 ∨ (¬ p4556))
    : (¬ p3461) ∨ p3246 ∨ (¬ p4187) ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4556 := h105399;
    (Or.elim h100309 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124815 (p2315 p2761 p3461 p3516 p4187 : Prop)
    (h105368 : p2315)
    (h100310 : p2761 ∨ (¬ p3461) ∨ (¬ p2315) ∨ p3516 ∨ (¬ p4187))
    : (¬ p3461) ∨ p3516 ∨ (¬ p4187) ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2315 := h105368;
    (Or.elim h100310 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124816 (p2254 p2417 p2922 p3286 p3379 p3461 p4625 p5284 : Prop)
    (h105366 : p2254)
    (h106455 : p4625)
    (h100311 : (¬ p5284) ∨ (¬ p3461) ∨ (¬ p3379) ∨ (¬ p4625) ∨ p3286 ∨ (¬ p2417) ∨ (¬ p2254) ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p3379) ∨ (¬ p5284) ∨ (¬ p3461) ∨ p3286 ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4625 := h106455;
    (Or.elim h100311 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step124817 (p2132 p2252 p2748 p3286 p3425 p3434 p3461 p4625 p5284 : Prop)
    (h106455 : p4625)
    (h100315 : p2132 ∨ (¬ p2748) ∨ (¬ p3434) ∨ (¬ p4625) ∨ (¬ p5284) ∨ (¬ p3461) ∨ p3286 ∨ p3425 ∨ (¬ p2252))
    : p3286 ∨ (¬ p3434) ∨ p3425 ∨ (¬ p5284) ∨ p2132 ∨ (¬ p3461) ∨ (¬ p2252) ∨ (¬ p2748) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4625 := h106455;
    (Or.elim h100315 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step124819 (p2230 p2459 p2563 p3125 p3399 p3527 p4604 p5193 : Prop)
    (h105488 : p5193)
    (h106293 : p4604)
    (h100332 : (¬ p3527) ∨ p3125 ∨ (¬ p4604) ∨ (¬ p2459) ∨ (¬ p5193) ∨ p2563 ∨ p2230 ∨ (¬ p3399))
    : p2230 ∨ (¬ p3527) ∨ (¬ p2459) ∨ (¬ p3399) ∨ p2563 ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2230) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5193 := h105488;
    let u7 : p4604 := h106293;
    (Or.elim h100332 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step124821 (p3016 p3125 p3343 p4331 p4718 : Prop)
    (h105425 : p4718)
    (h100335 : (¬ p4331) ∨ (¬ p3343) ∨ p3016 ∨ (¬ p4718) ∨ p3125)
    : (¬ p4331) ∨ p3016 ∨ (¬ p3343) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4718 := h105425;
    (Or.elim h100335 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step124822 (p2427 p3125 p3564 p3660 p4555 : Prop)
    (h105542 : p4555)
    (h100339 : (¬ p3564) ∨ p3125 ∨ (¬ p3660) ∨ p2427 ∨ (¬ p4555))
    : (¬ p3564) ∨ p2427 ∨ (¬ p3660) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    (Or.elim h100339 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124824 (p2440 p2573 p3343 p3346 p4717 : Prop)
    (h105424 : p4717)
    (h61174 : (¬ p2440) ∨ (¬ p2573) ∨ (¬ p3343) ∨ (¬ p3346) ∨ (¬ p4717))
    : (¬ p3346) ∨ (¬ p3343) ∨ (¬ p2573) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3346 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4717 := h105424;
    (Or.elim h61174 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124825 (p2497 p2498 p2573 p3343 p3346 p4811 : Prop)
    (h105633 : p4811)
    (h56945 : (¬ p2497) ∨ (¬ p2498) ∨ (¬ p2573) ∨ (¬ p3343) ∨ (¬ p3346) ∨ (¬ p4811))
    : (¬ p2498) ∨ (¬ p3346) ∨ (¬ p2573) ∨ (¬ p2497) ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2498 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4811 := h105633;
    (Or.elim h56945 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step124828 (p2331 p2641 p2737 p2750 p2811 : Prop)
    (h106345 : p2750)
    (h100383 : p2641 ∨ (¬ p2811) ∨ (¬ p2750) ∨ (¬ p2737) ∨ (¬ p2331))
    : (¬ p2811) ∨ (¬ p2737) ∨ p2641 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2750 := h106345;
    (Or.elim h100383 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step124829 (p2254 p2417 p2437 p2651 p3266 p3707 p3830 p4669 : Prop)
    (h105366 : p2254)
    (h105415 : p4669)
    (h100404 : (¬ p3707) ∨ p3266 ∨ (¬ p3830) ∨ p2651 ∨ p2437 ∨ (¬ p2254) ∨ p2417 ∨ (¬ p4669))
    : (¬ p3707) ∨ p2417 ∨ p2437 ∨ p3266 ∨ (¬ p3830) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4669 := h105415;
    (Or.elim h100404 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124833 (p2417 p2598 p3201 p3461 p3707 p3830 p4621 p4736 : Prop)
    (h105431 : p4736)
    (h105407 : p4621)
    (h100425 : (¬ p3707) ∨ p3461 ∨ p2417 ∨ p2598 ∨ (¬ p3830) ∨ (¬ p4736) ∨ p3201 ∨ (¬ p4621))
    : (¬ p3707) ∨ p2417 ∨ p2598 ∨ p3201 ∨ p3461 ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4621 := h105407;
    (Or.elim h100425 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124834 (p2252 p2295 p2331 p2608 p2750 p3707 p3830 p4260 p4831 : Prop)
    (h106345 : p2750)
    (h105445 : p4831)
    (h100426 : (¬ p3707) ∨ (¬ p4260) ∨ (¬ p4831) ∨ p2331 ∨ (¬ p3830) ∨ (¬ p2252) ∨ (¬ p2750) ∨ p2608 ∨ p2295)
    : (¬ p3707) ∨ (¬ p2252) ∨ p2331 ∨ (¬ p4260) ∨ (¬ p3830) ∨ p2608 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2750 := h106345;
    let u8 : p4831 := h105445;
    (Or.elim h100426 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (u6 r7)))))))))))))))))))

theorem step124835 (p2156 p2553 p2608 p3347 p3707 p3830 p3904 p4203 p4260 p4831 : Prop)
    (h105445 : p4831)
    (h100436 : (¬ p3830) ∨ p2608 ∨ (¬ p3347) ∨ (¬ p4260) ∨ (¬ p3904) ∨ (¬ p4203) ∨ p2553 ∨ (¬ p3707) ∨ p2156 ∨ (¬ p4831))
    : (¬ p3707) ∨ (¬ p3347) ∨ p2553 ∨ p2156 ∨ (¬ p3830) ∨ (¬ p3904) ∨ p2608 ∨ (¬ p4260) ∨ (¬ p4203) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4831 := h105445;
    (Or.elim h100436 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step124837 (p2774 p2819 p3366 p3379 p3707 p3830 p4376 p5123 p5580 : Prop)
    (h106320 : p4376)
    (h100445 : (¬ p5580) ∨ (¬ p3707) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p3366) ∨ p2774 ∨ p2819 ∨ (¬ p3830) ∨ p3379)
    : (¬ p3830) ∨ (¬ p3707) ∨ (¬ p5580) ∨ p2774 ∨ p3379 ∨ (¬ p3366) ∨ p2819 ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    (Or.elim h100445 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (u4 r7)))))))))))))))))))

theorem step124838 (p2331 p2641 p2696 p2745 p2774 : Prop)
    (h105523 : p2745)
    (h100460 : (¬ p2331) ∨ p2641 ∨ (¬ p2745) ∨ (¬ p2774) ∨ p2696)
    : p2696 ∨ (¬ p2774) ∨ (¬ p2331) ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    (Or.elim h100460 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step124840 (p2641 p2696 p2745 p2774 p4328 : Prop)
    (h105523 : p2745)
    (h100467 : p2641 ∨ (¬ p4328) ∨ (¬ p2774) ∨ (¬ p2745) ∨ p2696)
    : p2696 ∨ (¬ p2774) ∨ (¬ p4328) ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    (Or.elim h100467 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step124845 (p2641 p2727 p3016 p4976 : Prop)
    (h105465 : p4976)
    (h100481 : p2641 ∨ (¬ p3016) ∨ (¬ p4976) ∨ (¬ p2727))
    : (¬ p2727) ∨ (¬ p3016) ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4976 := h105465;
    (Or.elim h100481 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step124846 (p2341 p2459 p2641 p2696 p2707 p2748 p3323 p3577 p4604 : Prop)
    (h106293 : p4604)
    (h100482 : (¬ p3577) ∨ p2696 ∨ (¬ p2341) ∨ p3323 ∨ (¬ p2459) ∨ (¬ p2748) ∨ (¬ p4604) ∨ (¬ p2707) ∨ p2641)
    : (¬ p3577) ∨ p2641 ∨ p3323 ∨ (¬ p2707) ∨ (¬ p2748) ∨ (¬ p2341) ∨ (¬ p2459) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4604 := h106293;
    (Or.elim h100482 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (u1 r7)))))))))))))))))))

theorem step124849 (p2255 p2641 p2958 p2962 p3323 p3654 : Prop)
    (h105367 : p2255)
    (h100493 : (¬ p3654) ∨ p3323 ∨ (¬ p2958) ∨ (¬ p2962) ∨ (¬ p2255) ∨ p2641)
    : (¬ p2958) ∨ p2641 ∨ (¬ p3654) ∨ (¬ p2962) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2958 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2255 := h105367;
    (Or.elim h100493 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u1 r4)))))))))))))

theorem step124852 (p2230 p2246 p2373 p2641 p3323 p3366 p3461 p3519 p3969 p4236 p4376 p5119 : Prop)
    (h106320 : p4376)
    (h100498 : (¬ p3969) ∨ p2641 ∨ (¬ p5119) ∨ (¬ p4236) ∨ (¬ p3519) ∨ p3461 ∨ (¬ p2246) ∨ (¬ p2230) ∨ (¬ p3366) ∨ (¬ p2373) ∨ p3323 ∨ (¬ p4376))
    : (¬ p3969) ∨ p2641 ∨ (¬ p5119) ∨ p3461 ∨ (¬ p2373) ∨ (¬ p3366) ∨ (¬ p4236) ∨ (¬ p3519) ∨ (¬ p2246) ∨ (¬ p2230) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4376 := h106320;
    (Or.elim h100498 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u10 q10))) (fun r10 => (False.elim (r10 u11)))))))))))))))))))))))))

theorem step124854 (p2230 p2241 p2427 p3189 p3246 p3256 p3950 p5190 : Prop)
    (h105487 : p5190)
    (h100504 : p3189 ∨ p2241 ∨ (¬ p2427) ∨ p3256 ∨ (¬ p3950) ∨ (¬ p3246) ∨ (¬ p5190) ∨ (¬ p2230))
    : (¬ p2230) ∨ p3189 ∨ (¬ p3950) ∨ p2241 ∨ (¬ p3246) ∨ p3256 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5190 := h105487;
    (Or.elim h100504 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step124855 (p2241 p2396 p2553 p2573 p3189 p3256 p3950 p5190 : Prop)
    (h105487 : p5190)
    (h100513 : p3189 ∨ p2241 ∨ (¬ p3950) ∨ (¬ p5190) ∨ (¬ p2573) ∨ (¬ p2553) ∨ (¬ p2396) ∨ p3256)
    : (¬ p2553) ∨ p2241 ∨ p3256 ∨ (¬ p2396) ∨ p3189 ∨ (¬ p2573) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5190 := h105487;
    (Or.elim h100513 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (u2 r6)))))))))))))))))

theorem step124856 (p2156 p2241 p2352 p3096 p3189 p3256 p3979 p4521 p5122 : Prop)
    (h105483 : p5122)
    (h100518 : p3189 ∨ (¬ p2352) ∨ (¬ p5122) ∨ p3256 ∨ (¬ p3979) ∨ (¬ p4521) ∨ (¬ p2156) ∨ (¬ p3096) ∨ p2241)
    : (¬ p3979) ∨ p3189 ∨ (¬ p3096) ∨ p2241 ∨ (¬ p2156) ∨ (¬ p2352) ∨ p3256 ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5122 := h105483;
    (Or.elim h100518 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (u3 r7)))))))))))))))))))

theorem step124859 (p2132 p2245 p2331 p2641 p2870 p2881 p3189 p4041 p4733 : Prop)
    (h105430 : p4733)
    (h100540 : (¬ p2641) ∨ p2331 ∨ (¬ p2881) ∨ (¬ p4041) ∨ (¬ p4733) ∨ (¬ p2245) ∨ p3189 ∨ (¬ p2870) ∨ (¬ p2132))
    : p3189 ∨ (¬ p2245) ∨ (¬ p4041) ∨ (¬ p2881) ∨ (¬ p2132) ∨ (¬ p2641) ∨ (¬ p2870) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4733 := h105430;
    (Or.elim h100540 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step124862 (p2598 p2630 p2727 p2749 p2751 p4343 : Prop)
    (h106343 : p2751)
    (h100573 : (¬ p2751) ∨ (¬ p2727) ∨ p2598 ∨ (¬ p4343) ∨ p2630 ∨ (¬ p2749))
    : p2630 ∨ (¬ p2749) ∨ (¬ p2727) ∨ p2598 ∨ (¬ p4343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    (Or.elim h100573 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step124874 (p2187 p2210 p2295 p2696 p2797 p3093 p3366 p4377 p4405 p4516 : Prop)
    (h105512 : p4405)
    (h106170 : p4377)
    (h100626 : p2797 ∨ p2210 ∨ (¬ p4405) ∨ p2295 ∨ (¬ p2187) ∨ (¬ p4377) ∨ (¬ p3366) ∨ (¬ p3093) ∨ p2696 ∨ (¬ p4516))
    : p2797 ∨ p2210 ∨ (¬ p3366) ∨ (¬ p3093) ∨ p2696 ∨ p2295 ∨ (¬ p4516) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4405 := h105512;
    let u9 : p4377 := h106170;
    (Or.elim h100626 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step124876 (p2264 p2685 p2696 p3063 p3093 p3366 p3379 p4133 p4376 : Prop)
    (h105712 : p4133)
    (h106320 : p4376)
    (h100629 : (¬ p3063) ∨ p2685 ∨ p2264 ∨ p3379 ∨ (¬ p4376) ∨ p2696 ∨ (¬ p3366) ∨ (¬ p4133) ∨ (¬ p3093))
    : p2696 ∨ p2685 ∨ (¬ p3063) ∨ p2264 ∨ (¬ p3366) ∨ (¬ p3093) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4133 := h105712;
    let u8 : p4376 := h106320;
    (Or.elim h100629 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step124877 (p2230 p2427 p2608 p3093 p3246 p3319 p3347 p4621 : Prop)
    (h105407 : p4621)
    (h100633 : p2608 ∨ (¬ p3319) ∨ (¬ p4621) ∨ p2427 ∨ (¬ p3347) ∨ (¬ p3093) ∨ p2230 ∨ p3246)
    : (¬ p3347) ∨ p2608 ∨ p2427 ∨ p2230 ∨ (¬ p3319) ∨ p3246 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3347 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4621 := h105407;
    (Or.elim h100633 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (u5 r6)))))))))))))))))

theorem step124878 (p2254 p2363 p2901 p2946 p3063 p3093 p3246 p4669 : Prop)
    (h105366 : p2254)
    (h105415 : p4669)
    (h100634 : (¬ p3063) ∨ p2901 ∨ p2946 ∨ p3246 ∨ (¬ p2363) ∨ (¬ p3093) ∨ (¬ p4669) ∨ (¬ p2254))
    : (¬ p3063) ∨ (¬ p3093) ∨ p2901 ∨ p3246 ∨ (¬ p2363) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4669 := h105415;
    (Or.elim h100634 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124879 (p2363 p3063 p3093 p3276 p3346 p3680 p5059 p5193 : Prop)
    (h105488 : p5193)
    (h100635 : p3276 ∨ (¬ p3063) ∨ (¬ p3680) ∨ (¬ p5193) ∨ (¬ p3346) ∨ (¬ p3093) ∨ (¬ p5059) ∨ (¬ p2363))
    : (¬ p3680) ∨ (¬ p3063) ∨ (¬ p5059) ∨ (¬ p3346) ∨ p3276 ∨ (¬ p3093) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h100635 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124883 (p2685 p2696 p2753 p3367 p4343 p4652 : Prop)
    (h105413 : p4652)
    (h100681 : (¬ p2753) ∨ p3367 ∨ (¬ p4343) ∨ (¬ p2696) ∨ (¬ p2685) ∨ (¬ p4652))
    : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p4343) ∨ (¬ p2685) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4652 := h105413;
    (Or.elim h100681 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step124889 (p2156 p2553 p2696 p2753 p3096 p3519 p3590 p3599 p3670 p3791 p4399 p4749 p4826 : Prop)
    (h105432 : p4749)
    (h105444 : p4826)
    (h100698 : p3599 ∨ (¬ p2753) ∨ (¬ p2553) ∨ (¬ p3519) ∨ (¬ p3096) ∨ (¬ p4399) ∨ (¬ p2696) ∨ (¬ p3590) ∨ (¬ p2156) ∨ (¬ p4826) ∨ p3670 ∨ (¬ p3791) ∨ (¬ p4749))
    : (¬ p3791) ∨ (¬ p2696) ∨ p3599 ∨ p3670 ∨ (¬ p2156) ∨ (¬ p2753) ∨ (¬ p3519) ∨ (¬ p3590) ∨ (¬ p4399) ∨ (¬ p3096) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4749 := h105432;
    let u12 : p4826 := h105444;
    (Or.elim h100698 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u3 q10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u0))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step124899 (p2331 p2598 p2797 p4117 p4749 : Prop)
    (h105432 : p4749)
    (h100724 : p2797 ∨ (¬ p2331) ∨ (¬ p4749) ∨ p2598 ∨ (¬ p4117))
    : (¬ p4117) ∨ p2598 ∨ p2797 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4117 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4749 := h105432;
    (Or.elim h100724 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step124900 (p2598 p2946 p3136 p4117 p4749 : Prop)
    (h105432 : p4749)
    (h100727 : p3136 ∨ (¬ p2946) ∨ p2598 ∨ (¬ p4117) ∨ (¬ p4749))
    : p3136 ∨ (¬ p2946) ∨ (¬ p4117) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4749 := h105432;
    (Or.elim h100727 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124901 (p2598 p2685 p2807 p4117 p4749 : Prop)
    (h105432 : p4749)
    (h100728 : p2685 ∨ p2598 ∨ (¬ p4749) ∨ (¬ p2807) ∨ (¬ p4117))
    : p2598 ∨ (¬ p4117) ∨ p2685 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2598) := (fun h => hn (Or.inl h));
    let u1 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4749 := h105432;
    (Or.elim h100728 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124904 (p2373 p2427 p2753 p3051 p3166 p3347 p3904 p4009 p4117 p4134 p5580 : Prop)
    (h105379 : p4134)
    (h100743 : (¬ p4009) ∨ (¬ p2753) ∨ p2373 ∨ (¬ p5580) ∨ (¬ p3347) ∨ (¬ p2427) ∨ (¬ p4117) ∨ (¬ p3166) ∨ (¬ p3904) ∨ p3051 ∨ (¬ p4134))
    : (¬ p4009) ∨ (¬ p4117) ∨ p2373 ∨ (¬ p3166) ∨ (¬ p2753) ∨ (¬ p2427) ∨ (¬ p5580) ∨ p3051 ∨ (¬ p3347) ∨ (¬ p3904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4134 := h105379;
    (Or.elim h100743 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u7 q9))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step124909 (p2459 p2696 p3115 p3136 p3399 p3527 p4736 p5059 : Prop)
    (h105431 : p4736)
    (h100771 : (¬ p3527) ∨ p2696 ∨ (¬ p3399) ∨ (¬ p4736) ∨ (¬ p2459) ∨ p3136 ∨ (¬ p5059) ∨ p3115)
    : (¬ p3527) ∨ p3115 ∨ (¬ p2459) ∨ (¬ p3399) ∨ p2696 ∨ p3136 ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h100771 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step124910 (p2563 p2797 p3136 p3567 p4356 p4705 : Prop)
    (h106238 : p4705)
    (h100784 : (¬ p2797) ∨ (¬ p3567) ∨ p2563 ∨ (¬ p4705) ∨ (¬ p4356) ∨ p3136)
    : p3136 ∨ p2563 ∨ (¬ p3567) ∨ (¬ p2797) ∨ (¬ p4356) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    (Or.elim h100784 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step124913 (p2177 p2696 p2901 p2911 p2922 p3136 p3366 p4376 p4559 : Prop)
    (h105701 : p4559)
    (h106320 : p4376)
    (h100791 : (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3366) ∨ (¬ p4559) ∨ p2696 ∨ p2901 ∨ p2177 ∨ p3136 ∨ (¬ p4376))
    : (¬ p2922) ∨ (¬ p2911) ∨ p3136 ∨ (¬ p3366) ∨ p2901 ∨ p2177 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4559 := h105701;
    let u8 : p4376 := h106320;
    (Or.elim h100791 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step124914 (p2363 p2696 p3093 p3115 p3136 p3366 p3449 p4318 p4866 p5059 : Prop)
    (h106063 : p4866)
    (h100796 : (¬ p4318) ∨ p3093 ∨ p3136 ∨ p3115 ∨ p2696 ∨ (¬ p3449) ∨ (¬ p3366) ∨ (¬ p5059) ∨ (¬ p2363) ∨ (¬ p4866))
    : p3115 ∨ p3093 ∨ (¬ p2363) ∨ p3136 ∨ (¬ p5059) ∨ (¬ p4318) ∨ (¬ p3366) ∨ p2696 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4866 := h106063;
    (Or.elim h100796 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step124920 (p2166 p2210 p2254 p2331 p2363 p2819 p3969 p4328 p5122 : Prop)
    (h105366 : p2254)
    (h105483 : p5122)
    (h100837 : (¬ p3969) ∨ p2363 ∨ (¬ p2210) ∨ (¬ p2254) ∨ p2331 ∨ (¬ p2166) ∨ (¬ p5122) ∨ (¬ p4328) ∨ p2819)
    : (¬ p3969) ∨ (¬ p4328) ∨ p2819 ∨ (¬ p2166) ∨ p2363 ∨ (¬ p2210) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p5122 := h105483;
    (Or.elim h100837 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (u2 r7)))))))))))))))))))

theorem step124921 (p2166 p2210 p2363 p2774 p2819 p3969 p4736 p5122 : Prop)
    (h105431 : p4736)
    (h105483 : p5122)
    (h100841 : (¬ p3969) ∨ p2363 ∨ p2819 ∨ p2774 ∨ (¬ p2166) ∨ (¬ p4736) ∨ (¬ p5122) ∨ (¬ p2210))
    : (¬ p3969) ∨ p2774 ∨ (¬ p2210) ∨ p2819 ∨ (¬ p2166) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p5122 := h105483;
    (Or.elim h100841 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step124925 (p2396 p2881 p2911 p3246 p4276 : Prop)
    (h105516 : p4276)
    (h100857 : p3246 ∨ p2911 ∨ (¬ p2396) ∨ (¬ p4276) ∨ (¬ p2881))
    : p2911 ∨ (¬ p2881) ∨ p3246 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4276 := h105516;
    (Or.elim h100857 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124928 (p2341 p2696 p2797 p2881 p3246 p3323 p4621 p5260 : Prop)
    (h105407 : p4621)
    (h100872 : (¬ p2797) ∨ p3246 ∨ (¬ p2696) ∨ (¬ p5260) ∨ p2341 ∨ (¬ p3323) ∨ (¬ p4621) ∨ (¬ p2881))
    : (¬ p2696) ∨ p2341 ∨ (¬ p5260) ∨ (¬ p2881) ∨ (¬ p2797) ∨ p3246 ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4621 := h105407;
    (Or.elim h100872 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step124929 (p2241 p2341 p2641 p2881 p3246 p3323 p4621 p5210 : Prop)
    (h105407 : p4621)
    (h100874 : p3246 ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p4621) ∨ p2341 ∨ (¬ p5210) ∨ (¬ p2881) ∨ (¬ p2241))
    : (¬ p3323) ∨ p2341 ∨ (¬ p2241) ∨ p3246 ∨ (¬ p2641) ∨ (¬ p2881) ∨ (¬ p5210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4621 := h105407;
    (Or.elim h100874 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step124930 (p2284 p2449 p2995 p3246 p4558 : Prop)
    (h105400 : p4558)
    (h100879 : p3246 ∨ (¬ p2449) ∨ p2284 ∨ (¬ p4558) ∨ (¬ p2995))
    : (¬ p2449) ∨ p2284 ∨ (¬ p2995) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h100879 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124932 (p2881 p3246 p3941 p4445 p5122 : Prop)
    (h105483 : p5122)
    (h100883 : (¬ p3941) ∨ p3246 ∨ (¬ p5122) ∨ (¬ p4445) ∨ (¬ p2881))
    : (¬ p3941) ∨ (¬ p2881) ∨ (¬ p4445) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5122 := h105483;
    (Or.elim h100883 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124933 (p2417 p2563 p3246 p3741 p4558 : Prop)
    (h105400 : p4558)
    (h100885 : (¬ p3741) ∨ (¬ p2417) ∨ p2563 ∨ p3246 ∨ (¬ p4558))
    : (¬ p3741) ∨ (¬ p2417) ∨ p2563 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3741 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h100885 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124937 (p2396 p2598 p2850 p2982 p3093 p3309 p4395 p4733 : Prop)
    (h105430 : p4733)
    (h100908 : p3093 ∨ (¬ p2982) ∨ (¬ p2850) ∨ (¬ p4395) ∨ (¬ p4733) ∨ p2396 ∨ p3309 ∨ (¬ p2598))
    : p3093 ∨ (¬ p2598) ∨ p3309 ∨ p2396 ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p4395) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    (Or.elim h100908 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step124940 (p2248 p2396 p2528 p2651 p3083 p3093 p3309 p4669 : Prop)
    (h105365 : p2248)
    (h105415 : p4669)
    (h100914 : p3093 ∨ (¬ p2528) ∨ (¬ p2248) ∨ p2396 ∨ (¬ p4669) ∨ p3309 ∨ (¬ p2651) ∨ (¬ p3083))
    : (¬ p3083) ∨ (¬ p2651) ∨ p3093 ∨ p2396 ∨ p3309 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4669 := h105415;
    (Or.elim h100914 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step124941 (p2210 p2396 p2553 p2573 p2881 p2891 p4666 p5193 : Prop)
    (h105488 : p5193)
    (h105658 : p4666)
    (h100917 : (¬ p2891) ∨ (¬ p2881) ∨ p2553 ∨ p2573 ∨ p2396 ∨ (¬ p4666) ∨ (¬ p2210) ∨ (¬ p5193))
    : p2573 ∨ (¬ p2210) ∨ p2553 ∨ p2396 ∨ (¬ p2891) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5193 := h105488;
    let u7 : p4666 := h105658;
    (Or.elim h100917 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step124944 (p2156 p2253 p2274 p2396 p2528 p2651 p3083 p4669 : Prop)
    (h105415 : p4669)
    (h100935 : p2396 ∨ p2274 ∨ (¬ p2528) ∨ (¬ p2253) ∨ (¬ p4669) ∨ (¬ p3083) ∨ p2156 ∨ (¬ p2651))
    : p2156 ∨ (¬ p2651) ∨ (¬ p2528) ∨ (¬ p2253) ∨ (¬ p3083) ∨ p2274 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4669 := h105415;
    (Or.elim h100935 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step124949 (p2396 p2761 p3680 p4192 p4559 : Prop)
    (h105701 : p4559)
    (h100958 : p2761 ∨ (¬ p3680) ∨ (¬ p4192) ∨ (¬ p4559) ∨ p2396)
    : (¬ p3680) ∨ (¬ p4192) ∨ p2396 ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4559 := h105701;
    (Or.elim h100958 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step124950 (p2321 p2396 p2761 p3767 p5300 : Prop)
    (h105369 : p2321)
    (h100960 : p2761 ∨ (¬ p3767) ∨ (¬ p5300) ∨ p2396 ∨ (¬ p2321))
    : (¬ p3767) ∨ (¬ p5300) ∨ p2761 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3767 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5300 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2321 := h105369;
    (Or.elim h100960 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step124951 (p2248 p2396 p2946 p3093 p3146 p3156 p3309 p4669 : Prop)
    (h105365 : p2248)
    (h105415 : p4669)
    (h100961 : p3093 ∨ (¬ p3146) ∨ p3309 ∨ p2396 ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p2248) ∨ (¬ p4669))
    : p3093 ∨ (¬ p2946) ∨ p3309 ∨ (¬ p3146) ∨ p2396 ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4669 := h105415;
    (Or.elim h100961 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124952 (p2177 p2254 p2528 p3093 p3166 p3256 p3309 p4438 : Prop)
    (h105366 : p2254)
    (h100981 : (¬ p3309) ∨ p3166 ∨ (¬ p2528) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p2254) ∨ (¬ p4438) ∨ p3256)
    : (¬ p3309) ∨ (¬ p2528) ∨ (¬ p4438) ∨ p3256 ∨ (¬ p3093) ∨ p3166 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h100981 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step124953 (p2210 p2254 p2528 p2881 p2891 p3166 p3256 p4438 : Prop)
    (h105366 : p2254)
    (h100982 : (¬ p2891) ∨ (¬ p2881) ∨ p3256 ∨ (¬ p2528) ∨ (¬ p2210) ∨ p3166 ∨ (¬ p2254) ∨ (¬ p4438))
    : (¬ p2528) ∨ p3166 ∨ (¬ p4438) ∨ p3256 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h100982 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step124954 (p2254 p2307 p3063 p3146 p3166 p3256 p3309 p4134 p5020 : Prop)
    (h105366 : p2254)
    (h105379 : p4134)
    (h100990 : (¬ p3063) ∨ (¬ p3146) ∨ p3256 ∨ p3309 ∨ (¬ p2254) ∨ (¬ p5020) ∨ p3166 ∨ (¬ p4134) ∨ (¬ p2307))
    : (¬ p2307) ∨ (¬ p3146) ∨ p3256 ∨ (¬ p5020) ∨ p3166 ∨ p3309 ∨ (¬ p3063) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p4134 := h105379;
    (Or.elim h100990 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step124955 (p2166 p2210 p2252 p2459 p2608 p2750 p3166 p3256 p4902 : Prop)
    (h105456 : p4902)
    (h106345 : p2750)
    (h100994 : p3256 ∨ p2608 ∨ p3166 ∨ (¬ p2459) ∨ (¬ p4902) ∨ (¬ p2252) ∨ (¬ p2166) ∨ (¬ p2750) ∨ (¬ p2210))
    : (¬ p2166) ∨ p3166 ∨ (¬ p2210) ∨ p3256 ∨ (¬ p2459) ∨ (¬ p2252) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4902 := h105456;
    let u8 : p2750 := h106345;
    (Or.elim h100994 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step124956 (p2166 p2210 p2459 p3166 p3256 p3366 p3379 p4236 p4376 p4902 : Prop)
    (h105456 : p4902)
    (h106320 : p4376)
    (h100995 : p3256 ∨ p3379 ∨ (¬ p4236) ∨ (¬ p2210) ∨ (¬ p2459) ∨ (¬ p4902) ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p2166) ∨ p3166)
    : (¬ p2166) ∨ p3166 ∨ (¬ p2210) ∨ (¬ p4236) ∨ p3379 ∨ (¬ p2459) ∨ (¬ p3366) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4902 := h105456;
    let u9 : p4376 := h106320;
    (Or.elim h100995 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (u1 r8)))))))))))))))))))))

theorem step124958 (p2254 p2363 p2911 p2922 p3166 p3256 p3379 p4503 : Prop)
    (h105366 : p2254)
    (h106530 : p4503)
    (h100997 : (¬ p2922) ∨ (¬ p2911) ∨ p3166 ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p4503) ∨ p3256 ∨ (¬ p2363))
    : p3256 ∨ (¬ p2922) ∨ (¬ p2911) ∨ (¬ p3379) ∨ (¬ p2363) ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4503 := h106530;
    (Or.elim h100997 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step124960 (p2533 p3256 p3266 p3680 p5063 : Prop)
    (h105474 : p5063)
    (h101015 : p3266 ∨ (¬ p3680) ∨ (¬ p5063) ∨ (¬ p2533) ∨ p3256)
    : (¬ p3680) ∨ (¬ p2533) ∨ p3266 ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5063 := h105474;
    (Or.elim h101015 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step124961 (p2088 p3005 p3178 p3256 p4790 : Prop)
    (h106424 : p4790)
    (h101016 : p3256 ∨ p3005 ∨ (¬ p2088) ∨ (¬ p4790) ∨ (¬ p3178))
    : (¬ p2088) ∨ p3005 ∨ (¬ p3178) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3178 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    (Or.elim h101016 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124962 (p2187 p2363 p3256 p4196 p4564 : Prop)
    (h105401 : p4564)
    (h101019 : (¬ p4196) ∨ (¬ p2187) ∨ p3256 ∨ (¬ p4564) ∨ (¬ p2363))
    : p3256 ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p4196) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4564 := h105401;
    (Or.elim h101019 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step124964 (p2248 p2264 p2608 p2807 p3537 p3609 p3941 p5122 : Prop)
    (h105365 : p2248)
    (h105483 : p5122)
    (h101039 : p3537 ∨ p3609 ∨ (¬ p3941) ∨ (¬ p2807) ∨ (¬ p2248) ∨ (¬ p2264) ∨ p2608 ∨ (¬ p5122))
    : p3537 ∨ p2608 ∨ (¬ p2264) ∨ (¬ p2807) ∨ p3609 ∨ (¬ p3941) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p5122 := h105483;
    (Or.elim h101039 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step124965 (p2696 p2881 p3051 p3366 p3370 p3755 p3941 p4377 p5119 p5284 : Prop)
    (h106170 : p4377)
    (h101041 : (¬ p5284) ∨ (¬ p3941) ∨ (¬ p2881) ∨ (¬ p4377) ∨ (¬ p5119) ∨ p3755 ∨ (¬ p3366) ∨ (¬ p3051) ∨ p2696 ∨ (¬ p3370))
    : p3755 ∨ (¬ p3370) ∨ (¬ p2881) ∨ p2696 ∨ (¬ p3051) ∨ (¬ p3941) ∨ (¬ p3366) ∨ (¬ p5284) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4377 := h106170;
    (Or.elim h101041 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step124966 (p2166 p2210 p2254 p2573 p2655 p3016 p3146 p3343 p4697 : Prop)
    (h105366 : p2254)
    (h101061 : (¬ p2254) ∨ (¬ p2655) ∨ (¬ p2166) ∨ (¬ p3016) ∨ (¬ p2210) ∨ p2573 ∨ (¬ p4697) ∨ p3343 ∨ (¬ p3146))
    : (¬ p2655) ∨ p3343 ∨ (¬ p2210) ∨ p2573 ∨ (¬ p3146) ∨ (¬ p3016) ∨ (¬ p2166) ∨ (¬ p4697) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2655 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2254 := h105366;
    (Or.elim h101061 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step124969 (p2166 p2177 p2210 p2553 p2573 p2608 p3347 p4902 : Prop)
    (h105456 : p4902)
    (h101075 : p2608 ∨ p2573 ∨ p2177 ∨ p2553 ∨ (¬ p2166) ∨ (¬ p4902) ∨ (¬ p3347) ∨ (¬ p2210))
    : (¬ p2166) ∨ (¬ p2210) ∨ p2573 ∨ p2608 ∨ (¬ p3347) ∨ p2553 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4902 := h105456;
    (Or.elim h101075 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step124970 (p2230 p2331 p2427 p2797 p2881 p3005 p3366 p3519 p4041 p4236 p4376 : Prop)
    (h106320 : p4376)
    (h101088 : p3005 ∨ (¬ p3366) ∨ (¬ p4236) ∨ (¬ p3519) ∨ (¬ p2230) ∨ (¬ p4376) ∨ (¬ p4041) ∨ (¬ p2797) ∨ p2331 ∨ (¬ p2881) ∨ (¬ p2427))
    : p3005 ∨ (¬ p3519) ∨ (¬ p2881) ∨ p2331 ∨ (¬ p2427) ∨ (¬ p4041) ∨ (¬ p3366) ∨ (¬ p2230) ∨ (¬ p4236) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4376 := h106320;
    (Or.elim h101088 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u4)))))))))))))))))))))))

theorem step124972 (p2230 p2254 p2331 p2406 p2518 p2797 p3005 p4079 p5012 : Prop)
    (h105366 : p2254)
    (h101090 : p3005 ∨ p2406 ∨ (¬ p2797) ∨ p2331 ∨ (¬ p2230) ∨ (¬ p5012) ∨ (¬ p2518) ∨ (¬ p2254) ∨ (¬ p4079))
    : p3005 ∨ p2331 ∨ (¬ p4079) ∨ (¬ p2797) ∨ (¬ p2230) ∨ (¬ p2518) ∨ p2406 ∨ (¬ p5012) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5012 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2254 := h105366;
    (Or.elim h101090 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step124973 (p2331 p2797 p2911 p2922 p3005 p3379 p4041 p4236 p4736 : Prop)
    (h105431 : p4736)
    (h101092 : p3005 ∨ (¬ p4736) ∨ (¬ p4041) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p2797) ∨ (¬ p4236) ∨ p2331)
    : p3005 ∨ (¬ p4236) ∨ (¬ p2922) ∨ (¬ p3379) ∨ p2331 ∨ (¬ p2911) ∨ (¬ p4041) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    (Or.elim h101092 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (u4 r7)))))))))))))))))))

theorem step124974 (p2331 p2459 p2797 p2911 p3366 p3389 p3519 p3755 p4236 p4376 p5113 : Prop)
    (h106320 : p4376)
    (h105481 : p5113)
    (h101096 : (¬ p5113) ∨ (¬ p3366) ∨ p2331 ∨ (¬ p2911) ∨ (¬ p3519) ∨ (¬ p2459) ∨ p3755 ∨ (¬ p3389) ∨ (¬ p4376) ∨ (¬ p4236) ∨ (¬ p2797))
    : (¬ p4236) ∨ (¬ p2797) ∨ p2331 ∨ (¬ p2911) ∨ p3755 ∨ (¬ p3389) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    let u10 : p5113 := h105481;
    (Or.elim h101096 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (False.elim (r9 u1)))))))))))))))))))))))

theorem step124975 (p2254 p2331 p2470 p2528 p2797 p3005 p3146 p4041 p4042 p4079 : Prop)
    (h105366 : p2254)
    (h101101 : p3005 ∨ (¬ p2470) ∨ (¬ p4041) ∨ (¬ p4042) ∨ p2331 ∨ (¬ p2254) ∨ (¬ p2528) ∨ (¬ p4079) ∨ p3146 ∨ (¬ p2797))
    : (¬ p2797) ∨ p3005 ∨ (¬ p2528) ∨ (¬ p2470) ∨ p3146 ∨ p2331 ∨ (¬ p4042) ∨ (¬ p4079) ∨ (¬ p4041) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2254 := h105366;
    (Or.elim h101101 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step124976 (p2254 p2298 p2331 p2685 p2797 p2881 p3399 p3527 p4556 : Prop)
    (h105366 : p2254)
    (h105399 : p4556)
    (h101102 : (¬ p3527) ∨ p2881 ∨ (¬ p2797) ∨ (¬ p2298) ∨ p2331 ∨ (¬ p2254) ∨ (¬ p4556) ∨ p2685 ∨ (¬ p3399))
    : (¬ p2797) ∨ p2685 ∨ p2881 ∨ (¬ p3399) ∨ (¬ p2298) ∨ (¬ p3527) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p4556 := h105399;
    (Or.elim h101102 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step124982 (p2249 p2331 p2396 p2470 p2528 p2656 p2727 p3309 p3922 p4669 : Prop)
    (h106513 : p2249)
    (h105415 : p4669)
    (h101113 : (¬ p2470) ∨ (¬ p2656) ∨ p2396 ∨ (¬ p4669) ∨ (¬ p3922) ∨ (¬ p2528) ∨ p2331 ∨ p3309 ∨ (¬ p2249) ∨ (¬ p2727))
    : (¬ p2528) ∨ p2331 ∨ (¬ p2470) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3922) ∨ p2396 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2249 := h106513;
    let u9 : p4669 := h105415;
    (Or.elim h101113 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step124985 (p2331 p2946 p3115 p3745 p5046 : Prop)
    (h105472 : p5046)
    (h101118 : (¬ p3115) ∨ p2331 ∨ (¬ p3745) ∨ (¬ p5046) ∨ (¬ p2946))
    : p2331 ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5046 := h105472;
    (Or.elim h101118 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step124987 (p2210 p2254 p2331 p2363 p2881 p2891 p3256 p4196 p4503 : Prop)
    (h105366 : p2254)
    (h106530 : p4503)
    (h101128 : (¬ p2891) ∨ (¬ p2881) ∨ (¬ p4503) ∨ p2331 ∨ p3256 ∨ (¬ p2363) ∨ (¬ p4196) ∨ (¬ p2210) ∨ (¬ p2254))
    : p3256 ∨ (¬ p2210) ∨ (¬ p2881) ∨ p2331 ∨ (¬ p2363) ∨ (¬ p4196) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p4503 := h106530;
    (Or.elim h101128 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step124989 (p2230 p2331 p2373 p2797 p3146 p3366 p3519 p3755 p4236 p4376 p5113 : Prop)
    (h106320 : p4376)
    (h105481 : p5113)
    (h101132 : (¬ p3519) ∨ p3755 ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p2230) ∨ (¬ p5113) ∨ (¬ p2373) ∨ p2331 ∨ (¬ p2797) ∨ (¬ p4376) ∨ (¬ p4236))
    : p3755 ∨ (¬ p3519) ∨ (¬ p2797) ∨ (¬ p2373) ∨ (¬ p3146) ∨ p2331 ∨ (¬ p3366) ∨ (¬ p2230) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    let u10 : p5113 := h105481;
    (Or.elim h101132 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u8)))))))))))))))))))))))

theorem step124992 (p2132 p2245 p2331 p2363 p2870 p2881 p3256 p4196 p4503 p4733 : Prop)
    (h105430 : p4733)
    (h106530 : p4503)
    (h101136 : (¬ p2870) ∨ (¬ p2881) ∨ p3256 ∨ (¬ p4733) ∨ (¬ p2245) ∨ p2331 ∨ (¬ p2363) ∨ (¬ p4503) ∨ (¬ p4196) ∨ (¬ p2132))
    : (¬ p2870) ∨ p3256 ∨ p2331 ∨ (¬ p2881) ∨ (¬ p2132) ∨ (¬ p2245) ∨ (¬ p4196) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4733 := h105430;
    let u9 : p4503 := h106530;
    (Or.elim h101136 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step124993 (p2230 p2249 p2331 p2363 p2656 p2668 p2727 p2982 p4450 : Prop)
    (h106513 : p2249)
    (h101137 : p2363 ∨ p2331 ∨ (¬ p4450) ∨ (¬ p2727) ∨ (¬ p2982) ∨ (¬ p2249) ∨ (¬ p2230) ∨ p2668 ∨ (¬ p2656))
    : p2331 ∨ (¬ p2230) ∨ (¬ p2982) ∨ p2363 ∨ (¬ p2727) ∨ (¬ p2656) ∨ p2668 ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2249 := h106513;
    (Or.elim h101137 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step124996 (p2254 p2331 p2363 p2608 p2668 p2707 p3434 p3950 : Prop)
    (h105366 : p2254)
    (h101146 : (¬ p2254) ∨ p2363 ∨ (¬ p2608) ∨ (¬ p2707) ∨ p2331 ∨ p2668 ∨ (¬ p3950) ∨ (¬ p3434))
    : (¬ p3434) ∨ p2331 ∨ (¬ p3950) ∨ p2363 ∨ p2668 ∨ (¬ p2707) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h101146 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step125000 (p2668 p3979 p4197 p4581 p5590 : Prop)
    (h105405 : p4581)
    (h51534 : (¬ p2668) ∨ (¬ p3979) ∨ (¬ p4197) ∨ (¬ p4581) ∨ (¬ p5590))
    : (¬ p3979) ∨ (¬ p4197) ∨ (¬ p5590) ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4581 := h105405;
    (Or.elim h51534 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step125004 (p2255 p2331 p2662 p2727 p3063 p3276 p3346 p3979 p4319 p5119 : Prop)
    (h105367 : p2255)
    (h101163 : p3276 ∨ (¬ p3979) ∨ (¬ p4319) ∨ (¬ p2662) ∨ p2727 ∨ (¬ p3063) ∨ (¬ p2331) ∨ (¬ p2255) ∨ (¬ p5119) ∨ (¬ p3346))
    : (¬ p3979) ∨ (¬ p3346) ∨ p2727 ∨ p3276 ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p4319) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2255 := h105367;
    (Or.elim h101163 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step125006 (p2352 p2573 p2761 p3366 p3425 p3434 p3519 p3979 p4376 p5119 : Prop)
    (h106320 : p4376)
    (h101167 : (¬ p2352) ∨ (¬ p3979) ∨ (¬ p2573) ∨ (¬ p3519) ∨ (¬ p5119) ∨ p2761 ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p3425) ∨ p3434)
    : (¬ p3979) ∨ (¬ p3519) ∨ p3434 ∨ p2761 ∨ (¬ p2573) ∨ (¬ p3366) ∨ (¬ p2352) ∨ (¬ p3425) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h101167 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (u2 r8)))))))))))))))))))))

theorem step125010 (p3325 p3654 p3979 p4197 p4624 p5590 : Prop)
    (h105408 : p4624)
    (h50811 : (¬ p3325) ∨ (¬ p3654) ∨ (¬ p3979) ∨ (¬ p4197) ∨ (¬ p4624) ∨ (¬ p5590))
    : (¬ p3979) ∨ (¬ p4197) ∨ (¬ p5590) ∨ (¬ p3325) ∨ (¬ p3654) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4624 := h105408;
    (Or.elim h50811 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step125014 (p2307 p2440 p2497 p2962 p3309 p4109 p4811 : Prop)
    (h105633 : p4811)
    (h101193 : (¬ p2307) ∨ p3309 ∨ (¬ p2497) ∨ p2440 ∨ (¬ p4811) ∨ (¬ p4109) ∨ (¬ p2962))
    : (¬ p4109) ∨ (¬ p2497) ∨ p2440 ∨ (¬ p2962) ∨ p3309 ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4109 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4811 := h105633;
    (Or.elim h101193 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step125015 (p2177 p2248 p2901 p2946 p3093 p3246 p3309 p4668 : Prop)
    (h105365 : p2248)
    (h105414 : p4668)
    (h101195 : p3093 ∨ p3309 ∨ (¬ p4668) ∨ (¬ p3246) ∨ (¬ p2248) ∨ (¬ p2946) ∨ p2177 ∨ (¬ p2901))
    : (¬ p2901) ∨ (¬ p2946) ∨ p2177 ∨ p3093 ∨ p3309 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4668 := h105414;
    (Or.elim h101195 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step125018 (p3309 p4181 p4317 p4405 p5580 : Prop)
    (h105512 : p4405)
    (h101205 : (¬ p4181) ∨ (¬ p5580) ∨ p3309 ∨ (¬ p4317) ∨ (¬ p4405))
    : (¬ p4181) ∨ (¬ p4317) ∨ p3309 ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    (Or.elim h101205 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125019 (p3093 p3309 p3449 p4405 : Prop)
    (h105512 : p4405)
    (h101206 : p3093 ∨ (¬ p3449) ∨ (¬ p4405) ∨ p3309)
    : p3093 ∨ (¬ p3449) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4405 := h105512;
    (Or.elim h101206 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step125030 (p2187 p3016 p3083 p3958 p4432 : Prop)
    (h105378 : p3958)
    (h101242 : p3083 ∨ (¬ p3958) ∨ (¬ p4432) ∨ (¬ p2187) ∨ (¬ p3016))
    : p3083 ∨ (¬ p2187) ∨ (¬ p4432) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3958 := h105378;
    (Or.elim h101242 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step125032 (p2573 p2655 p2807 p3016 p4652 : Prop)
    (h105413 : p4652)
    (h101246 : (¬ p2655) ∨ (¬ p3016) ∨ p2573 ∨ (¬ p4652) ∨ (¬ p2807))
    : p2573 ∨ (¬ p2655) ∨ (¬ p3016) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4652 := h105413;
    (Or.elim h101246 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step125034 (p2252 p2573 p2608 p2655 p2750 p3016 p3083 p3399 p3527 p4438 : Prop)
    (h106345 : p2750)
    (h101256 : p2608 ∨ (¬ p2655) ∨ (¬ p3527) ∨ (¬ p3399) ∨ (¬ p2750) ∨ (¬ p3016) ∨ (¬ p4438) ∨ (¬ p2252) ∨ p3083 ∨ p2573)
    : p2573 ∨ (¬ p3016) ∨ (¬ p4438) ∨ (¬ p2655) ∨ (¬ p3527) ∨ p3083 ∨ p2608 ∨ (¬ p2252) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2750 := h106345;
    (Or.elim h101256 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (False.elim (u0 r8)))))))))))))))))))))

theorem step125035 (p2249 p2573 p2655 p2727 p3016 : Prop)
    (h106513 : p2249)
    (h101259 : (¬ p3016) ∨ p2573 ∨ (¬ p2249) ∨ (¬ p2727) ∨ (¬ p2655))
    : p2573 ∨ (¬ p2655) ∨ (¬ p2727) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2249 := h106513;
    (Or.elim h101259 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step125037 (p2156 p2440 p3016 p4203 p4533 : Prop)
    (h105394 : p4533)
    (h101267 : (¬ p3016) ∨ (¬ p2440) ∨ p2156 ∨ (¬ p4533) ∨ (¬ p4203))
    : p2156 ∨ (¬ p3016) ∨ (¬ p2440) ∨ (¬ p4203) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4533 := h105394;
    (Or.elim h101267 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step125039 (p2440 p2563 p3016 p3958 : Prop)
    (h105378 : p3958)
    (h101272 : (¬ p3016) ∨ (¬ p2440) ∨ (¬ p3958) ∨ p2563)
    : (¬ p2440) ∨ p2563 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3958 := h105378;
    (Or.elim h101272 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step125041 (p2248 p2553 p2651 p2881 p3016 p3399 p3527 p4559 : Prop)
    (h105365 : p2248)
    (h105701 : p4559)
    (h101277 : (¬ p2553) ∨ p3399 ∨ (¬ p3016) ∨ (¬ p2651) ∨ (¬ p2881) ∨ (¬ p4559) ∨ (¬ p2248) ∨ p3527)
    : p3399 ∨ (¬ p2651) ∨ (¬ p2881) ∨ (¬ p2553) ∨ p3527 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4559 := h105701;
    (Or.elim h101277 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step125042 (p2255 p2341 p2553 p2651 p2881 p2996 p3016 p4155 p4559 : Prop)
    (h105367 : p2255)
    (h105701 : p4559)
    (h101278 : p2341 ∨ (¬ p2255) ∨ (¬ p4155) ∨ (¬ p2651) ∨ (¬ p2553) ∨ (¬ p4559) ∨ (¬ p2881) ∨ (¬ p3016) ∨ (¬ p2996))
    : (¬ p2996) ∨ p2341 ∨ (¬ p2881) ∨ (¬ p2651) ∨ (¬ p2553) ∨ (¬ p3016) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2255 := h105367;
    let u8 : p4559 := h105701;
    (Or.elim h101278 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step125045 (p2437 p2930 p3083 p3527 p4404 : Prop)
    (h105376 : p2930)
    (h101305 : (¬ p3083) ∨ (¬ p4404) ∨ (¬ p2930) ∨ p2437 ∨ p3527)
    : (¬ p3083) ∨ p2437 ∨ (¬ p4404) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2930 := h105376;
    (Or.elim h101305 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step125046 (p2136 p2156 p2177 p2241 p2274 p2744 p3083 p3366 p3379 p3487 p4420 : Prop)
    (h106503 : p2744)
    (h105707 : p4420)
    (h101310 : p2241 ∨ p2274 ∨ p2156 ∨ (¬ p3379) ∨ p2177 ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p4420) ∨ (¬ p3366) ∨ (¬ p2136) ∨ (¬ p3487))
    : p2156 ∨ (¬ p2136) ∨ p2274 ∨ (¬ p3379) ∨ (¬ p3083) ∨ p2177 ∨ (¬ p3366) ∨ (¬ p3487) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    let u10 : p4420 := h105707;
    (Or.elim h101310 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step125048 (p2440 p2459 p2528 p2668 p2696 p2797 p3083 p4503 : Prop)
    (h106530 : p4503)
    (h101323 : p2797 ∨ (¬ p3083) ∨ p2668 ∨ (¬ p4503) ∨ p2459 ∨ (¬ p2528) ∨ (¬ p2440) ∨ p2696)
    : p2797 ∨ (¬ p3083) ∨ (¬ p2440) ∨ (¬ p2528) ∨ p2459 ∨ p2696 ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4503 := h106530;
    (Or.elim h101323 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u5 r6)))))))))))))))))

theorem step125050 (p3083 p3343 p4149 p4440 p5122 : Prop)
    (h105483 : p5122)
    (h101328 : p3343 ∨ (¬ p4149) ∨ (¬ p4440) ∨ (¬ p3083) ∨ (¬ p5122))
    : (¬ p4149) ∨ (¬ p3083) ∨ (¬ p4440) ∨ p3343 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5122 := h105483;
    (Or.elim h101328 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125053 (p2651 p2774 p3083 p3461 p3917 p4149 p4786 p5119 : Prop)
    (h106425 : p4786)
    (h101334 : (¬ p4149) ∨ p3461 ∨ (¬ p4786) ∨ (¬ p5119) ∨ (¬ p3083) ∨ (¬ p3917) ∨ p2774 ∨ (¬ p2651))
    : (¬ p2651) ∨ (¬ p4149) ∨ (¬ p3083) ∨ p2774 ∨ (¬ p5119) ∨ p3461 ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    (Or.elim h101334 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step125055 (p2177 p2341 p2417 p3516 p4712 : Prop)
    (h105422 : p4712)
    (h101354 : (¬ p2417) ∨ p3516 ∨ p2177 ∨ (¬ p4712) ∨ (¬ p2341))
    : p3516 ∨ (¬ p2341) ∨ p2177 ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4712 := h105422;
    (Or.elim h101354 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step125059 (p2363 p2459 p2911 p3325 p4276 : Prop)
    (h105516 : p4276)
    (h101391 : p2911 ∨ (¬ p3325) ∨ (¬ p4276) ∨ (¬ p2363) ∨ p2459)
    : p2911 ∨ p2459 ∨ (¬ p3325) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4276 := h105516;
    (Or.elim h101391 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step125060 (p2459 p2608 p2911 p3347 p3389 p3449 p4181 p5122 : Prop)
    (h105483 : p5122)
    (h101392 : (¬ p4181) ∨ p2911 ∨ (¬ p3449) ∨ p2608 ∨ p2459 ∨ (¬ p3347) ∨ p3389 ∨ (¬ p5122))
    : (¬ p4181) ∨ (¬ p3449) ∨ p2459 ∨ p2911 ∨ p3389 ∨ p2608 ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5122 := h105483;
    (Or.elim h101392 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step125061 (p2122 p2608 p2829 p2881 p2911 p3389 p4559 p5193 : Prop)
    (h105488 : p5193)
    (h105701 : p4559)
    (h101397 : (¬ p2829) ∨ (¬ p2122) ∨ p2911 ∨ (¬ p5193) ∨ p3389 ∨ (¬ p4559) ∨ (¬ p2881) ∨ (¬ p2608))
    : p2911 ∨ p3389 ∨ (¬ p2122) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5193 := h105488;
    let u7 : p4559 := h105701;
    (Or.elim h101397 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step125062 (p2459 p2664 p2911 p2946 p3156 p3389 p3969 p5122 : Prop)
    (h105483 : p5122)
    (h106537 : p2664)
    (h101400 : (¬ p3969) ∨ p2911 ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p2664) ∨ p2459 ∨ (¬ p5122) ∨ p3389)
    : (¬ p3969) ∨ (¬ p3156) ∨ p2911 ∨ (¬ p2946) ∨ p3389 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5122 := h105483;
    let u7 : p2664 := h106537;
    (Or.elim h101400 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step125065 (p2088 p2363 p2911 p3325 p4276 p4403 : Prop)
    (h105516 : p4276)
    (h101403 : (¬ p4403) ∨ p2088 ∨ p2911 ∨ (¬ p4276) ∨ (¬ p2363) ∨ (¬ p3325))
    : p2088 ∨ (¬ p4403) ∨ (¬ p3325) ∨ (¬ p2363) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4276 := h105516;
    (Or.elim h101403 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step125069 (p2264 p2441 p2850 p2911 p3580 p4750 : Prop)
    (h105433 : p4750)
    (h101416 : p2911 ∨ (¬ p3580) ∨ p2850 ∨ (¬ p4750) ∨ (¬ p2441) ∨ (¬ p2264))
    : (¬ p3580) ∨ p2850 ∨ (¬ p2441) ∨ (¬ p2264) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4750 := h105433;
    (Or.elim h101416 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step125072 (p2341 p2417 p2696 p2797 p2911 p3323 p4625 p5257 : Prop)
    (h106455 : p4625)
    (h101425 : p2797 ∨ (¬ p5257) ∨ p2911 ∨ (¬ p4625) ∨ p3323 ∨ (¬ p2341) ∨ (¬ p2417) ∨ p2696)
    : p2797 ∨ p2696 ∨ (¬ p2417) ∨ (¬ p2341) ∨ (¬ p5257) ∨ p3323 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4625 := h106455;
    (Or.elim h101425 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step125073 (p2241 p2459 p2911 p2992 p3115 p3389 p4450 p5193 : Prop)
    (h105488 : p5193)
    (h101426 : (¬ p3115) ∨ (¬ p2992) ∨ p2911 ∨ p2459 ∨ p3389 ∨ (¬ p2241) ∨ (¬ p5193) ∨ (¬ p4450))
    : (¬ p2992) ∨ (¬ p2241) ∨ (¬ p4450) ∨ p2911 ∨ p3389 ∨ p2459 ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h101426 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step125074 (p2417 p2911 p3146 p4443 p4902 : Prop)
    (h105456 : p4902)
    (h101439 : (¬ p2417) ∨ p3146 ∨ (¬ p4902) ∨ (¬ p4443) ∨ p2911)
    : (¬ p2417) ∨ p2911 ∨ p3146 ∨ (¬ p4443) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4902 := h105456;
    (Or.elim h101439 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step125075 (p2363 p2417 p2911 p4133 p4443 : Prop)
    (h105712 : p4133)
    (h101442 : (¬ p2417) ∨ p2363 ∨ (¬ p4133) ∨ (¬ p4443) ∨ p2911)
    : (¬ p2417) ∨ p2911 ∨ (¬ p4443) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4133 := h105712;
    (Or.elim h101442 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step125076 (p2241 p2598 p2744 p3073 p3366 p3422 p3449 p3564 p4604 : Prop)
    (h106503 : p2744)
    (h106293 : p4604)
    (h101449 : (¬ p3073) ∨ p3422 ∨ (¬ p3449) ∨ p3564 ∨ (¬ p4604) ∨ p2598 ∨ (¬ p3366) ∨ (¬ p2744) ∨ p2241)
    : p3422 ∨ p3564 ∨ (¬ p3449) ∨ p2598 ∨ p2241 ∨ (¬ p3073) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2744 := h106503;
    let u8 : p4604 := h106293;
    (Or.elim h101449 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u4 r7)))))))))))))))))))

theorem step125077 (p2386 p2641 p2727 p3422 p3567 p4750 : Prop)
    (h105433 : p4750)
    (h101457 : (¬ p3567) ∨ (¬ p2641) ∨ (¬ p2386) ∨ p3422 ∨ p2727 ∨ (¬ p4750))
    : (¬ p3567) ∨ p3422 ∨ p2727 ∨ (¬ p2386) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4750 := h105433;
    (Or.elim h101457 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step125078 (p2264 p2459 p2598 p2744 p2996 p3366 p3422 p3564 p4604 : Prop)
    (h106503 : p2744)
    (h106293 : p4604)
    (h101459 : p3564 ∨ p3422 ∨ (¬ p2264) ∨ p2996 ∨ (¬ p2744) ∨ (¬ p2459) ∨ (¬ p4604) ∨ (¬ p3366) ∨ p2598)
    : (¬ p3366) ∨ p2598 ∨ p3422 ∨ (¬ p2264) ∨ p3564 ∨ p2996 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3366 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2744 := h106503;
    let u8 : p4604 := h106293;
    (Or.elim h101459 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (u1 r7)))))))))))))))))))

theorem step125080 (p2363 p2470 p2528 p2608 p2707 p2717 p4503 p5193 : Prop)
    (h106530 : p4503)
    (h105488 : p5193)
    (h101469 : p2528 ∨ (¬ p2608) ∨ (¬ p2363) ∨ (¬ p2707) ∨ (¬ p4503) ∨ (¬ p2717) ∨ (¬ p5193) ∨ p2470)
    : (¬ p2717) ∨ p2528 ∨ p2470 ∨ (¬ p2707) ∨ (¬ p2608) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4503 := h106530;
    let u7 : p5193 := h105488;
    (Or.elim h101469 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u2 r6)))))))))))))))))

theorem step125082 (p2341 p2363 p3516 p4445 p4503 : Prop)
    (h106530 : p4503)
    (h101475 : p3516 ∨ (¬ p2341) ∨ (¬ p4503) ∨ (¬ p4445) ∨ (¬ p2363))
    : (¬ p4445) ∨ (¬ p2341) ∨ (¬ p2363) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4445 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4503 := h106530;
    (Or.elim h101475 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step125083 (p2132 p2252 p2363 p2750 p2753 p2870 p2881 p3166 p3256 p4503 : Prop)
    (h106530 : p4503)
    (h106345 : p2750)
    (h101478 : (¬ p2753) ∨ (¬ p2363) ∨ (¬ p2132) ∨ (¬ p4503) ∨ (¬ p2252) ∨ (¬ p2881) ∨ p3166 ∨ (¬ p2750) ∨ p3256 ∨ (¬ p2870))
    : p3256 ∨ (¬ p2870) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2363) ∨ p3166 ∨ (¬ p2881) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4503 := h106530;
    let u9 : p2750 := h106345;
    (Or.elim h101478 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u0 q8))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step125086 (p2254 p2363 p2608 p2707 p2717 p3166 p3256 p4503 : Prop)
    (h105366 : p2254)
    (h106530 : p4503)
    (h101482 : (¬ p2717) ∨ (¬ p2707) ∨ (¬ p2608) ∨ p3166 ∨ (¬ p2254) ∨ (¬ p2363) ∨ p3256 ∨ (¬ p4503))
    : (¬ p2717) ∨ p3256 ∨ (¬ p2608) ∨ (¬ p2363) ∨ (¬ p2707) ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4503 := h106530;
    (Or.elim h101482 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step125090 (p2252 p2352 p2363 p2573 p2741 p3286 p3519 p3680 p4376 p5059 p5284 : Prop)
    (h106320 : p4376)
    (h101497 : (¬ p5284) ∨ (¬ p2352) ∨ (¬ p3519) ∨ (¬ p3680) ∨ p3286 ∨ (¬ p5059) ∨ (¬ p2252) ∨ (¬ p2363) ∨ (¬ p2741) ∨ (¬ p4376) ∨ (¬ p2573))
    : (¬ p3680) ∨ p3286 ∨ (¬ p2352) ∨ (¬ p2741) ∨ (¬ p3519) ∨ (¬ p2363) ∨ (¬ p5284) ∨ (¬ p2252) ∨ (¬ p2573) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4376 := h106320;
    (Or.elim h101497 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u8)))))))))))))))))))))))

theorem step125092 (p2230 p2363 p2440 p2655 p2774 p2819 p3343 p4697 p4789 : Prop)
    (h105646 : p4789)
    (h101512 : (¬ p2819) ∨ p3343 ∨ (¬ p4789) ∨ (¬ p2655) ∨ p2440 ∨ p2230 ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p4697))
    : p2230 ∨ p2440 ∨ (¬ p2363) ∨ (¬ p4697) ∨ p3343 ∨ (¬ p2774) ∨ (¬ p2655) ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2230) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4789 := h105646;
    (Or.elim h101512 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step125098 (p2255 p2761 p2946 p2996 p3156 p3516 p3969 p4155 p5119 : Prop)
    (h105367 : p2255)
    (h101545 : p2761 ∨ (¬ p3969) ∨ (¬ p2996) ∨ (¬ p2255) ∨ (¬ p5119) ∨ (¬ p3156) ∨ (¬ p4155) ∨ (¬ p2946) ∨ p3516)
    : (¬ p3969) ∨ p3516 ∨ (¬ p2996) ∨ (¬ p4155) ∨ (¬ p3156) ∨ p2761 ∨ (¬ p2946) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2255 := h105367;
    (Or.elim h101545 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u1 r7)))))))))))))))))))

theorem step125099 (p2166 p2255 p2761 p2946 p2996 p3412 p3516 p3969 p4155 p5119 : Prop)
    (h105367 : p2255)
    (h101546 : p2761 ∨ (¬ p3969) ∨ p3516 ∨ (¬ p5119) ∨ (¬ p2166) ∨ (¬ p2996) ∨ (¬ p2255) ∨ (¬ p3412) ∨ (¬ p2946) ∨ (¬ p4155))
    : (¬ p3969) ∨ (¬ p2996) ∨ p2761 ∨ (¬ p4155) ∨ (¬ p2166) ∨ (¬ p5119) ∨ p3516 ∨ (¬ p3412) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2255 := h105367;
    (Or.elim h101546 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step125101 (p2696 p2797 p3073 p3323 p3366 p3379 p3449 p4376 p4604 : Prop)
    (h106320 : p4376)
    (h106293 : p4604)
    (h101564 : (¬ p3073) ∨ (¬ p3449) ∨ (¬ p4604) ∨ p3323 ∨ p3379 ∨ p2797 ∨ p2696 ∨ (¬ p4376) ∨ (¬ p3366))
    : p2797 ∨ p2696 ∨ (¬ p3366) ∨ p3323 ∨ (¬ p3073) ∨ (¬ p3449) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4376 := h106320;
    let u8 : p4604 := h106293;
    (Or.elim h101564 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step125102 (p2797 p3323 p3654 p3987 p4790 : Prop)
    (h106424 : p4790)
    (h101573 : (¬ p3654) ∨ p3323 ∨ (¬ p4790) ∨ p2797 ∨ (¬ p3987))
    : p2797 ∨ (¬ p3654) ∨ p3323 ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    (Or.elim h101573 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step125103 (p2459 p2696 p2797 p3323 p3399 p3527 p4604 p4736 : Prop)
    (h105431 : p4736)
    (h106293 : p4604)
    (h101574 : (¬ p3527) ∨ p2797 ∨ (¬ p4736) ∨ (¬ p2459) ∨ (¬ p4604) ∨ p3323 ∨ p2696 ∨ (¬ p3399))
    : p2797 ∨ p2696 ∨ p3323 ∨ (¬ p2459) ∨ (¬ p3527) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4604 := h106293;
    (Or.elim h101574 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step125104 (p2459 p2696 p2797 p2911 p3323 p3366 p3389 p3519 p4376 p4604 : Prop)
    (h106320 : p4376)
    (h106293 : p4604)
    (h101585 : p2797 ∨ (¬ p3519) ∨ p3323 ∨ p2696 ∨ (¬ p4376) ∨ (¬ p4604) ∨ (¬ p2459) ∨ (¬ p3389) ∨ (¬ p2911) ∨ (¬ p3366))
    : (¬ p3389) ∨ p2797 ∨ (¬ p2911) ∨ p2696 ∨ (¬ p2459) ∨ p3323 ∨ (¬ p3366) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p4604 := h106293;
    (Or.elim h101585 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step125108 (p2641 p2749 p2797 p3367 p4749 : Prop)
    (h105432 : p4749)
    (h101597 : (¬ p2641) ∨ p2797 ∨ p3367 ∨ (¬ p4749) ∨ (¬ p2749))
    : p2797 ∨ (¬ p2749) ∨ p3367 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4749 := h105432;
    (Or.elim h101597 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step125110 (p2210 p2696 p3005 p3256 p3366 p3399 p3631 p3950 p4377 : Prop)
    (h106170 : p4377)
    (h101608 : p3005 ∨ p3256 ∨ (¬ p3366) ∨ p2696 ∨ (¬ p3950) ∨ (¬ p4377) ∨ (¬ p3399) ∨ p2210 ∨ (¬ p3631))
    : p3005 ∨ p2210 ∨ (¬ p3366) ∨ (¬ p3950) ∨ p3256 ∨ (¬ p3631) ∨ (¬ p3399) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4377 := h106170;
    (Or.elim h101608 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step125111 (p2210 p2449 p2685 p2696 p3366 p3399 p3527 p4377 p4666 : Prop)
    (h105658 : p4666)
    (h106170 : p4377)
    (h101609 : (¬ p3366) ∨ p2449 ∨ (¬ p3399) ∨ (¬ p4666) ∨ (¬ p3527) ∨ p2696 ∨ p2210 ∨ p2685 ∨ (¬ p4377))
    : p2696 ∨ p2685 ∨ (¬ p3399) ∨ p2449 ∨ (¬ p3366) ∨ p2210 ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4666 := h105658;
    let u8 : p4377 := h106170;
    (Or.elim h101609 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step125115 (p2230 p2246 p2744 p2850 p3266 p3286 p3366 p3506 p3905 p4697 p5160 : Prop)
    (h106503 : p2744)
    (h101616 : p3266 ∨ (¬ p5160) ∨ (¬ p3286) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2850) ∨ (¬ p4697) ∨ (¬ p3506) ∨ (¬ p3366) ∨ p2230 ∨ (¬ p3905))
    : (¬ p3905) ∨ p2230 ∨ (¬ p4697) ∨ (¬ p2850) ∨ (¬ p3366) ∨ (¬ p5160) ∨ (¬ p3286) ∨ p3266 ∨ (¬ p2246) ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3905 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2230) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    (Or.elim h101616 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u1 q9))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step125118 (p2761 p3366 p3379 p3425 p3434 p3449 p4181 p4376 p5119 : Prop)
    (h106320 : p4376)
    (h101624 : (¬ p4181) ∨ p3434 ∨ (¬ p5119) ∨ p3379 ∨ (¬ p3425) ∨ (¬ p3449) ∨ (¬ p3366) ∨ (¬ p4376) ∨ p2761)
    : (¬ p4181) ∨ (¬ p3449) ∨ p3379 ∨ p2761 ∨ (¬ p3425) ∨ (¬ p3366) ∨ p3434 ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    (Or.elim h101624 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (u3 r7)))))))))))))))))))

theorem step125123 (p2396 p2553 p2573 p2696 p3005 p3256 p3366 p3519 p3950 p4376 : Prop)
    (h106320 : p4376)
    (h101631 : (¬ p2553) ∨ (¬ p2396) ∨ p3256 ∨ (¬ p3950) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p2573) ∨ p3005 ∨ (¬ p4376) ∨ p2696)
    : p3005 ∨ p2696 ∨ (¬ p3519) ∨ (¬ p2396) ∨ p3256 ∨ (¬ p2553) ∨ (¬ p3366) ∨ (¬ p2573) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h101631 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u1 r8)))))))))))))))))))))

theorem step125124 (p2132 p2619 p3146 p3366 p3379 p3449 p4181 p4376 p5122 : Prop)
    (h106320 : p4376)
    (h105483 : p5122)
    (h101632 : (¬ p4181) ∨ p2619 ∨ (¬ p4376) ∨ p3146 ∨ p3379 ∨ (¬ p5122) ∨ (¬ p3449) ∨ (¬ p3366) ∨ p2132)
    : (¬ p4181) ∨ p2619 ∨ (¬ p3449) ∨ p3146 ∨ p3379 ∨ p2132 ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4376 := h106320;
    let u8 : p5122 := h105483;
    (Or.elim h101632 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u5 r7)))))))))))))))))))

theorem step125125 (p2264 p2685 p2696 p3366 p3379 p3399 p3631 p4376 p4668 : Prop)
    (h105414 : p4668)
    (h106320 : p4376)
    (h101633 : (¬ p3631) ∨ p2696 ∨ (¬ p4668) ∨ p3379 ∨ p2685 ∨ p2264 ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p4376))
    : (¬ p3631) ∨ p2685 ∨ p3379 ∨ (¬ p3399) ∨ p2696 ∨ p2264 ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4668 := h105414;
    let u8 : p4376 := h106320;
    (Or.elim h101633 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step125127 (p2246 p2459 p2717 p2744 p2958 p3212 p3366 p3425 p3461 p3680 p4330 : Prop)
    (h106503 : p2744)
    (h106329 : p4330)
    (h101635 : (¬ p2246) ∨ p3461 ∨ (¬ p3212) ∨ (¬ p4330) ∨ p2717 ∨ p2459 ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p3680) ∨ (¬ p3425) ∨ (¬ p2958))
    : (¬ p3680) ∨ (¬ p3212) ∨ (¬ p2958) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p3366) ∨ p3461 ∨ (¬ p2246) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    let u10 : p4330 := h106329;
    (Or.elim h101635 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (False.elim (r9 u2)))))))))))))))))))))))

theorem step125132 (p2210 p2598 p3276 p3366 p3449 p4181 p4377 p5119 p5160 : Prop)
    (h106170 : p4377)
    (h101645 : p3276 ∨ (¬ p4181) ∨ (¬ p3449) ∨ (¬ p5119) ∨ p2598 ∨ p2210 ∨ (¬ p5160) ∨ (¬ p4377) ∨ (¬ p3366))
    : (¬ p4181) ∨ p2210 ∨ (¬ p3449) ∨ (¬ p5160) ∨ (¬ p3366) ∨ p2598 ∨ p3276 ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4377 := h106170;
    (Or.elim h101645 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step125136 (p2685 p2807 p3266 p3276 p3355 p3366 p3519 p3755 p4236 p4376 p5113 : Prop)
    (h106320 : p4376)
    (h105481 : p5113)
    (h101650 : p3266 ∨ (¬ p3519) ∨ p2807 ∨ p3755 ∨ (¬ p3276) ∨ (¬ p3366) ∨ (¬ p3355) ∨ (¬ p2685) ∨ (¬ p5113) ∨ (¬ p4376) ∨ (¬ p4236))
    : (¬ p3276) ∨ (¬ p3519) ∨ p2807 ∨ (¬ p2685) ∨ (¬ p3366) ∨ p3755 ∨ (¬ p3355) ∨ (¬ p4236) ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    let u10 : p5113 := h105481;
    (Or.elim h101650 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step125139 (p2598 p2850 p2982 p3073 p3093 p3366 p3449 p4866 p5059 : Prop)
    (h106063 : p4866)
    (h101655 : (¬ p3449) ∨ p3093 ∨ (¬ p4866) ∨ (¬ p3073) ∨ p2598 ∨ (¬ p3366) ∨ (¬ p5059) ∨ p2982 ∨ p2850)
    : p2982 ∨ p2850 ∨ p3093 ∨ p2598 ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3366) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4866 := h106063;
    (Or.elim h101655 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (False.elim (u1 r7)))))))))))))))))))

theorem step125141 (p2352 p2573 p2696 p3366 p3519 p3755 p3979 p4376 p5119 p5284 : Prop)
    (h106320 : p4376)
    (h101658 : (¬ p5284) ∨ (¬ p2352) ∨ p2696 ∨ (¬ p3519) ∨ (¬ p2573) ∨ (¬ p3979) ∨ p3755 ∨ (¬ p3366) ∨ (¬ p5119) ∨ (¬ p4376))
    : p3755 ∨ (¬ p3519) ∨ p2696 ∨ (¬ p3366) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3979) ∨ (¬ p5284) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h101658 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step125143 (p2177 p2459 p3146 p4119 p4556 : Prop)
    (h105399 : p4556)
    (h101663 : (¬ p4119) ∨ p3146 ∨ (¬ p2459) ∨ (¬ p2177) ∨ (¬ p4556))
    : p3146 ∨ (¬ p2177) ∨ (¬ p2459) ∨ (¬ p4119) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4556 := h105399;
    (Or.elim h101663 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125144 (p2264 p2459 p3146 p4119 p4362 : Prop)
    (h106173 : p4362)
    (h101665 : (¬ p4119) ∨ p3146 ∨ (¬ p2459) ∨ (¬ p4362) ∨ (¬ p2264))
    : p3146 ∨ (¬ p4119) ∨ (¬ p2264) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4362 := h106173;
    (Or.elim h101665 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step125157 (p2177 p2254 p2946 p3005 p3093 p3136 p3309 p4041 : Prop)
    (h105366 : p2254)
    (h101742 : (¬ p3309) ∨ p3005 ∨ (¬ p2254) ∨ (¬ p3093) ∨ p2946 ∨ (¬ p2177) ∨ (¬ p4041) ∨ (¬ p3136))
    : p3005 ∨ p2946 ∨ (¬ p3093) ∨ (¬ p4041) ∨ (¬ p3309) ∨ (¬ p3136) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h101742 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step125160 (p2132 p2891 p3425 p4344 p4875 : Prop)
    (h106227 : p4875)
    (h101759 : (¬ p4344) ∨ p2132 ∨ p3425 ∨ p2891 ∨ (¬ p4875))
    : p3425 ∨ p2891 ∨ (¬ p4344) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4875 := h106227;
    (Or.elim h101759 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125167 (p2230 p2264 p2685 p2696 p2891 p3246 p4034 p4079 p4668 p4736 : Prop)
    (h105431 : p4736)
    (h105414 : p4668)
    (h101780 : (¬ p2891) ∨ p2264 ∨ (¬ p2230) ∨ (¬ p4668) ∨ (¬ p3246) ∨ p2685 ∨ p2696 ∨ (¬ p4079) ∨ (¬ p4736) ∨ (¬ p4034))
    : p2685 ∨ p2696 ∨ (¬ p4079) ∨ (¬ p4034) ∨ (¬ p3246) ∨ (¬ p2230) ∨ p2264 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    let u9 : p4668 := h105414;
    (Or.elim h101780 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step125170 (p2139 p2220 p2449 p2533 p2685 p2696 p3266 p3680 p4669 : Prop)
    (h105415 : p4669)
    (h101792 : (¬ p3680) ∨ p2449 ∨ p3266 ∨ (¬ p4669) ∨ (¬ p2139) ∨ p2696 ∨ (¬ p2533) ∨ p2685 ∨ (¬ p2220))
    : (¬ p2220) ∨ (¬ p3680) ∨ (¬ p2533) ∨ p2696 ∨ p2685 ∨ (¬ p2139) ∨ p2449 ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4669 := h105415;
    (Or.elim h101792 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step125179 (p2246 p2717 p2744 p2946 p3115 p3366 p3425 p3680 p5123 p5558 : Prop)
    (h106503 : p2744)
    (h101829 : (¬ p3115) ∨ (¬ p5558) ∨ (¬ p3680) ∨ (¬ p2246) ∨ (¬ p2946) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p3425) ∨ (¬ p5123) ∨ p2717)
    : (¬ p3680) ∨ (¬ p3115) ∨ (¬ p3366) ∨ p2717 ∨ (¬ p3425) ∨ (¬ p2246) ∨ (¬ p2946) ∨ (¬ p5558) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    (Or.elim h101829 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (u3 r8)))))))))))))))))))))

theorem step125185 (p2230 p2252 p2440 p2655 p2750 p2819 p3083 p3654 p3917 p4384 p4869 p5016 : Prop)
    (h106345 : p2750)
    (h106167 : p4384)
    (h101857 : (¬ p3917) ∨ (¬ p2819) ∨ p3083 ∨ (¬ p5016) ∨ (¬ p2750) ∨ (¬ p2252) ∨ p2440 ∨ (¬ p2655) ∨ (¬ p4869) ∨ p2230 ∨ (¬ p3654) ∨ (¬ p4384))
    : (¬ p3917) ∨ (¬ p3654) ∨ (¬ p4869) ∨ (¬ p5016) ∨ (¬ p2819) ∨ p2230 ∨ p2440 ∨ p3083 ∨ (¬ p2252) ∨ (¬ p2655) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3917 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2750 := h106345;
    let u11 : p4384 := h106167;
    (Or.elim h101857 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u5 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u1))) (fun r10 => (False.elim (r10 u11)))))))))))))))))))))))))

theorem step125191 (p4344 p4473 p4556 : Prop)
    (h105399 : p4556)
    (h31691 : (¬ p4344) ∨ p4473 ∨ (¬ p4556))
    : (¬ p4344) ∨ p4473 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4344 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4473) := (fun h => hn (Or.inr h));
    let u2 : p4556 := h105399;
    (Or.elim h31691 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step125196 (p2248 p2417 p2922 p3286 p3379 p3461 p3506 p4621 : Prop)
    (h105365 : p2248)
    (h105407 : p4621)
    (h101928 : p2922 ∨ p3461 ∨ (¬ p3506) ∨ (¬ p4621) ∨ p2417 ∨ (¬ p2248) ∨ (¬ p3286) ∨ p3379)
    : (¬ p3506) ∨ p3379 ∨ p2922 ∨ (¬ p3286) ∨ p2417 ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4621 := h105407;
    (Or.elim h101928 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step125200 (p2187 p2331 p3166 p4564 p4769 : Prop)
    (h105401 : p4564)
    (h101952 : (¬ p2331) ∨ p3166 ∨ (¬ p4564) ∨ (¬ p4769) ∨ (¬ p2187))
    : p3166 ∨ (¬ p2187) ∨ (¬ p4769) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4564 := h105401;
    (Or.elim h101952 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step125201 (p2331 p2352 p3166 p4769 p4973 : Prop)
    (h105835 : p4973)
    (h101955 : p3166 ∨ (¬ p2352) ∨ (¬ p2331) ∨ (¬ p4973) ∨ (¬ p4769))
    : p3166 ∨ (¬ p2352) ∨ (¬ p4769) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4973 := h105835;
    (Or.elim h101955 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step125206 (p3016 p3343 p4331 p5249 p5514 : Prop)
    (h105496 : p5249)
    (h101971 : (¬ p3343) ∨ (¬ p5514) ∨ (¬ p5249) ∨ p3016 ∨ (¬ p4331))
    : (¬ p5514) ∨ p3016 ∨ (¬ p3343) ∨ (¬ p4331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5514 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5249 := h105496;
    (Or.elim h101971 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step125208 (p2246 p2608 p2744 p3266 p3286 p3399 p3506 p3631 p4669 : Prop)
    (h106503 : p2744)
    (h105415 : p4669)
    (h101979 : p3266 ∨ (¬ p2246) ∨ (¬ p4669) ∨ (¬ p2608) ∨ (¬ p3286) ∨ p3399 ∨ (¬ p2744) ∨ p3631 ∨ (¬ p3506))
    : (¬ p3506) ∨ (¬ p3286) ∨ p3399 ∨ p3266 ∨ p3631 ∨ (¬ p2608) ∨ (¬ p2246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2744 := h106503;
    let u8 : p4669 := h105415;
    (Or.elim h101979 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step125209 (p2696 p2761 p2797 p3399 p3631 p4228 p4733 p5250 : Prop)
    (h105430 : p4733)
    (h101989 : (¬ p4228) ∨ p2761 ∨ (¬ p2696) ∨ p3399 ∨ (¬ p2797) ∨ p3631 ∨ (¬ p5250) ∨ (¬ p4733))
    : (¬ p4228) ∨ (¬ p2696) ∨ p3631 ∨ p2761 ∨ (¬ p2797) ∨ p3399 ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    (Or.elim h101989 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step125212 (p2248 p2459 p2651 p2850 p2982 p3399 p3527 p4343 p4450 : Prop)
    (h105365 : p2248)
    (h102008 : p3527 ∨ (¬ p2982) ∨ p3399 ∨ (¬ p2850) ∨ (¬ p4450) ∨ (¬ p2248) ∨ (¬ p2651) ∨ p2459 ∨ (¬ p4343))
    : (¬ p2850) ∨ (¬ p4343) ∨ p3527 ∨ (¬ p2982) ∨ p3399 ∨ p2459 ∨ (¬ p2651) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2248 := h105365;
    (Or.elim h102008 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step125213 (p2341 p2696 p2797 p3323 p3527 p3631 p4172 p4625 p4736 p4988 : Prop)
    (h105431 : p4736)
    (h106455 : p4625)
    (h102011 : (¬ p3631) ∨ p3527 ∨ (¬ p4625) ∨ (¬ p4988) ∨ (¬ p4172) ∨ p3323 ∨ (¬ p2341) ∨ (¬ p4736) ∨ p2797 ∨ p2696)
    : p2797 ∨ (¬ p3631) ∨ p2696 ∨ p3323 ∨ p3527 ∨ (¬ p4988) ∨ (¬ p4172) ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    let u9 : p4625 := h106455;
    (Or.elim h102011 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u0 q8))) (fun r8 => (False.elim (u2 r8)))))))))))))))))))))

theorem step125214 (p2220 p2249 p2459 p2807 p2951 p2992 p3037 p3527 p3969 p5122 : Prop)
    (h106513 : p2249)
    (h105483 : p5122)
    (h102015 : (¬ p3969) ∨ (¬ p5122) ∨ (¬ p3037) ∨ (¬ p2992) ∨ (¬ p2220) ∨ (¬ p2249) ∨ p2807 ∨ (¬ p2951) ∨ p3527 ∨ p2459)
    : (¬ p2951) ∨ (¬ p3969) ∨ (¬ p2220) ∨ p2459 ∨ p2807 ∨ (¬ p2992) ∨ p3527 ∨ (¬ p3037) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2951 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2249 := h106513;
    let u9 : p5122 := h105483;
    (Or.elim h102015 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u6 q8))) (fun r8 => (False.elim (u3 r8)))))))))))))))))))))

theorem step125215 (p2248 p2459 p2651 p3083 p3399 p3527 p4149 p5122 : Prop)
    (h105365 : p2248)
    (h105483 : p5122)
    (h102016 : (¬ p4149) ∨ p3527 ∨ (¬ p5122) ∨ (¬ p2651) ∨ p2459 ∨ (¬ p2248) ∨ (¬ p3083) ∨ p3399)
    : (¬ p4149) ∨ (¬ p3083) ∨ p2459 ∨ (¬ p2651) ∨ p3399 ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p5122 := h105483;
    (Or.elim h102016 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step125217 (p3960 p4133 p4617 : Prop)
    (h105712 : p4133)
    (h24223 : (¬ p3960) ∨ (¬ p4133) ∨ p4617)
    : (¬ p3960) ∨ p4617 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3960 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4617) := (fun h => hn (Or.inr h));
    let u2 : p4133 := h105712;
    (Or.elim h24223 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step125219 (p2177 p3960 p3998 p4119 p4556 p5568 : Prop)
    (h105399 : p4556)
    (h49701 : (¬ p2177) ∨ (¬ p3960) ∨ (¬ p3998) ∨ (¬ p4119) ∨ (¬ p4556) ∨ (¬ p5568))
    : (¬ p3998) ∨ (¬ p5568) ∨ (¬ p4119) ∨ (¬ p2177) ∨ (¬ p3960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3998 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4556 := h105399;
    (Or.elim h49701 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step125221 (p2132 p2252 p2295 p2331 p2750 p2753 p3105 p3680 p4260 p4831 : Prop)
    (h106345 : p2750)
    (h105445 : p4831)
    (h102071 : (¬ p4260) ∨ (¬ p3105) ∨ (¬ p4831) ∨ (¬ p3680) ∨ (¬ p2132) ∨ (¬ p2750) ∨ p2331 ∨ (¬ p2252) ∨ (¬ p2753) ∨ p2295)
    : (¬ p4260) ∨ (¬ p3680) ∨ (¬ p2132) ∨ p2331 ∨ (¬ p3105) ∨ p2295 ∨ (¬ p2753) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    let u9 : p4831 := h105445;
    (Or.elim h102071 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (u5 r8)))))))))))))))))))))

theorem step125228 (p2248 p2509 p2528 p2761 p2958 p3212 p3379 p3680 p3950 : Prop)
    (h105365 : p2248)
    (h102107 : p2761 ∨ (¬ p3950) ∨ (¬ p2958) ∨ (¬ p3680) ∨ (¬ p2509) ∨ (¬ p2248) ∨ p3379 ∨ p2528 ∨ (¬ p3212))
    : (¬ p3680) ∨ (¬ p3212) ∨ (¬ p2958) ∨ p2528 ∨ (¬ p2509) ∨ p2761 ∨ p3379 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2248 := h105365;
    (Or.elim h102107 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step125231 (p2248 p2608 p2651 p3083 p3599 p3670 p4149 p5119 : Prop)
    (h105365 : p2248)
    (h102120 : p3599 ∨ (¬ p4149) ∨ p2608 ∨ p3670 ∨ (¬ p2651) ∨ (¬ p5119) ∨ (¬ p2248) ∨ (¬ p3083))
    : (¬ p4149) ∨ p3599 ∨ p3670 ∨ (¬ p5119) ∨ (¬ p3083) ∨ (¬ p2651) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    (Or.elim h102120 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step125232 (p2246 p2651 p2744 p2761 p3083 p3366 p3425 p3434 p4149 p5119 : Prop)
    (h106503 : p2744)
    (h102122 : (¬ p4149) ∨ (¬ p5119) ∨ (¬ p3425) ∨ (¬ p2744) ∨ p3434 ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2651) ∨ p2761 ∨ (¬ p3083))
    : p3434 ∨ (¬ p3083) ∨ (¬ p2651) ∨ (¬ p4149) ∨ (¬ p2246) ∨ (¬ p3366) ∨ p2761 ∨ (¬ p3425) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    (Or.elim h102122 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u6 q8))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step125236 (p2252 p2459 p2470 p2717 p2745 p2807 p2951 p3136 p3904 p4149 p4325 p5122 : Prop)
    (h105523 : p2745)
    (h105483 : p5122)
    (h102128 : (¬ p4149) ∨ (¬ p2951) ∨ p2717 ∨ (¬ p3136) ∨ (¬ p2252) ∨ (¬ p2745) ∨ p2807 ∨ p2459 ∨ (¬ p2470) ∨ (¬ p3904) ∨ (¬ p4325) ∨ (¬ p5122))
    : (¬ p2951) ∨ (¬ p4149) ∨ p2807 ∨ (¬ p4325) ∨ p2459 ∨ (¬ p3136) ∨ (¬ p2470) ∨ p2717 ∨ (¬ p2252) ∨ (¬ p3904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2951 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2745 := h105523;
    let u11 : p5122 := h105483;
    (Or.elim h102128 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u3))) (fun r10 => (False.elim (r10 u11)))))))))))))))))))))))))

theorem step125238 (p3005 p3755 p4009 p5107 p5122 : Prop)
    (h105483 : p5122)
    (h102134 : p3755 ∨ (¬ p4009) ∨ (¬ p5122) ∨ (¬ p3005) ∨ (¬ p5107))
    : (¬ p4009) ∨ (¬ p3005) ∨ (¬ p5107) ∨ p3755 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5122 := h105483;
    (Or.elim h102134 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step125241 (p2254 p2449 p2608 p2761 p2807 p2829 p3914 p5250 : Prop)
    (h105366 : p2254)
    (h102143 : (¬ p3914) ∨ p2761 ∨ (¬ p5250) ∨ p2449 ∨ p2807 ∨ (¬ p2608) ∨ (¬ p2254) ∨ (¬ p2829))
    : (¬ p3914) ∨ (¬ p2829) ∨ p2807 ∨ (¬ p5250) ∨ p2449 ∨ (¬ p2608) ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h102143 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step125242 (p2246 p2341 p2651 p2717 p2744 p3016 p3366 p3434 p3564 p3820 p4621 : Prop)
    (h106503 : p2744)
    (h105407 : p4621)
    (h102155 : (¬ p2717) ∨ (¬ p2246) ∨ p2341 ∨ (¬ p2744) ∨ (¬ p4621) ∨ (¬ p3820) ∨ p3434 ∨ (¬ p3366) ∨ (¬ p2651) ∨ (¬ p3564) ∨ (¬ p3016))
    : (¬ p3564) ∨ (¬ p2717) ∨ (¬ p2651) ∨ p3434 ∨ (¬ p3820) ∨ p2341 ∨ (¬ p2246) ∨ (¬ p3016) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    let u10 : p4621 := h105407;
    (Or.elim h102155 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step125244 (p2751 p2996 p3434 p3516 p4066 p4781 : Prop)
    (h106343 : p2751)
    (h102157 : p4781 ∨ (¬ p3516) ∨ (¬ p2751) ∨ (¬ p4066) ∨ p3434 ∨ p2996)
    : (¬ p3516) ∨ (¬ p4066) ∨ p4781 ∨ p3434 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4781) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    (Or.elim h102157 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (u4 r4)))))))))))))

theorem step125246 (p2761 p2946 p3156 p3425 p3434 p3969 p4786 p5119 : Prop)
    (h106425 : p4786)
    (h102162 : p3434 ∨ p2761 ∨ (¬ p5119) ∨ (¬ p3969) ∨ (¬ p3425) ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p4786))
    : (¬ p3969) ∨ p3434 ∨ p2761 ∨ (¬ p3425) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    (Or.elim h102162 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step125255 (p2341 p2881 p3212 p3872 p4984 p5046 : Prop)
    (h105472 : p5046)
    (h102242 : p2341 ∨ (¬ p3212) ∨ (¬ p3872) ∨ (¬ p5046) ∨ (¬ p2881) ∨ (¬ p4984))
    : (¬ p4984) ∨ (¬ p3872) ∨ p2341 ∨ (¬ p3212) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4984 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5046 := h105472;
    (Or.elim h102242 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step125258 (p2246 p2341 p2651 p2749 p2881 p3016 p3246 p3546 p3564 p4330 p4445 p4796 : Prop)
    (h106329 : p4330)
    (h105439 : p4796)
    (h102247 : (¬ p3546) ∨ (¬ p3564) ∨ (¬ p2749) ∨ (¬ p2246) ∨ (¬ p4796) ∨ p2341 ∨ p3246 ∨ (¬ p2651) ∨ (¬ p2881) ∨ (¬ p4445) ∨ (¬ p3016) ∨ (¬ p4330))
    : p2341 ∨ (¬ p2749) ∨ (¬ p3016) ∨ p3246 ∨ (¬ p2881) ∨ (¬ p3546) ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p3564) ∨ (¬ p4445) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4330 := h106329;
    let u11 : p4796 := h105439;
    (Or.elim h102247 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u2))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step125259 (p3575 p4327 p4854 : Prop)
    (h105381 : p4327)
    (h34279 : (¬ p3575) ∨ (¬ p4327) ∨ p4854)
    : (¬ p3575) ∨ p4854 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3575 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4854) := (fun h => hn (Or.inr h));
    let u2 : p4327 := h105381;
    (Or.elim h34279 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step125261 (p4433 p4498 p4993 : Prop)
    (h106150 : p4433)
    (h22709 : (¬ p4433) ∨ p4498 ∨ (¬ p4993))
    : (¬ p4993) ∨ p4498 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4993 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4498) := (fun h => hn (Or.inr h));
    let u2 : p4433 := h106150;
    (Or.elim h22709 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step125262 (p2220 p2440 p3016 p3096 p4109 p4509 : Prop)
    (h105392 : p4509)
    (h102279 : p2440 ∨ p3016 ∨ (¬ p4109) ∨ (¬ p4509) ∨ (¬ p3096) ∨ (¬ p2220))
    : (¬ p4109) ∨ p3016 ∨ (¬ p3096) ∨ (¬ p2220) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4109 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4509 := h105392;
    (Or.elim h102279 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step125267 (p2241 p2751 p3005 p3449 p4288 : Prop)
    (h106343 : p2751)
    (h102304 : (¬ p3449) ∨ p2241 ∨ (¬ p4288) ∨ (¬ p2751) ∨ p3005)
    : p3005 ∨ (¬ p3449) ∨ p2241 ∨ (¬ p4288) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    (Or.elim h102304 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step125269 (p2210 p2696 p2797 p3073 p3323 p3366 p3449 p4377 p4604 : Prop)
    (h106293 : p4604)
    (h106170 : p4377)
    (h102307 : (¬ p3073) ∨ (¬ p3449) ∨ p3323 ∨ (¬ p4377) ∨ p2797 ∨ (¬ p4604) ∨ (¬ p3366) ∨ p2210 ∨ p2696)
    : p2797 ∨ p2696 ∨ (¬ p3449) ∨ p2210 ∨ p3323 ∨ (¬ p3073) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4604 := h106293;
    let u8 : p4377 := h106170;
    (Or.elim h102307 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (False.elim (u1 r7)))))))))))))))))))

theorem step125272 (p2717 p3146 p3366 p3379 p3425 p3449 p4042 p4181 p4376 p5122 : Prop)
    (h106320 : p4376)
    (h105483 : p5122)
    (h102311 : (¬ p4181) ∨ p3379 ∨ (¬ p5122) ∨ (¬ p3425) ∨ (¬ p3449) ∨ p3146 ∨ (¬ p4042) ∨ (¬ p3366) ∨ (¬ p4376) ∨ p2717)
    : (¬ p4181) ∨ p3379 ∨ p3146 ∨ (¬ p3425) ∨ (¬ p3449) ∨ (¬ p3366) ∨ (¬ p4042) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p5122 := h105483;
    (Or.elim h102311 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (u7 r8)))))))))))))))))))))

theorem step125273 (p2166 p2210 p2774 p3461 p3917 p3969 p4736 p5119 : Prop)
    (h105431 : p4736)
    (h102357 : (¬ p3969) ∨ p3461 ∨ p2774 ∨ (¬ p2166) ∨ (¬ p5119) ∨ (¬ p3917) ∨ (¬ p4736) ∨ (¬ p2210))
    : (¬ p3969) ∨ (¬ p2166) ∨ p2774 ∨ (¬ p5119) ∨ p3461 ∨ (¬ p3917) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h102357 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step125279 (p2230 p2252 p2331 p2373 p2741 p3323 p3461 p3519 p3969 p4376 p5119 : Prop)
    (h106320 : p4376)
    (h102381 : (¬ p3969) ∨ p3461 ∨ p2331 ∨ (¬ p4376) ∨ (¬ p2373) ∨ (¬ p5119) ∨ (¬ p2741) ∨ p3323 ∨ (¬ p2230) ∨ (¬ p3519) ∨ (¬ p2252))
    : (¬ p3969) ∨ (¬ p2230) ∨ p2331 ∨ (¬ p2741) ∨ (¬ p3519) ∨ p3461 ∨ p3323 ∨ (¬ p2252) ∨ (¬ p2373) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4376 := h106320;
    (Or.elim h102381 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step125280 (p2230 p2373 p2696 p3005 p3256 p3969 p4419 p5122 : Prop)
    (h105483 : p5122)
    (h102383 : (¬ p3969) ∨ (¬ p5122) ∨ (¬ p4419) ∨ p3005 ∨ (¬ p2230) ∨ p3256 ∨ (¬ p2373) ∨ p2696)
    : (¬ p3969) ∨ p3005 ∨ p2696 ∨ (¬ p2373) ∨ (¬ p2230) ∨ p3256 ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5122 := h105483;
    (Or.elim h102383 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (u2 r6)))))))))))))))))

theorem step125281 (p2230 p2246 p2331 p2373 p2741 p3323 p3461 p3519 p3969 p4376 p5119 : Prop)
    (h106320 : p4376)
    (h102384 : (¬ p3969) ∨ p2246 ∨ (¬ p2741) ∨ p3323 ∨ (¬ p3519) ∨ (¬ p2230) ∨ p2331 ∨ (¬ p2373) ∨ p3461 ∨ (¬ p4376) ∨ (¬ p5119))
    : (¬ p3969) ∨ p2246 ∨ p3461 ∨ (¬ p5119) ∨ (¬ p3519) ∨ (¬ p2373) ∨ p3323 ∨ (¬ p2230) ∨ p2331 ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4376 := h106320;
    (Or.elim h102384 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u8 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u2 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step125285 (p3949 p4330 p4368 : Prop)
    (h106329 : p4330)
    (h27046 : (¬ p3949) ∨ (¬ p4330) ∨ p4368)
    : (¬ p3949) ∨ p4368 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3949 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4368) := (fun h => hn (Or.inr h));
    let u2 : p4330 := h106329;
    (Or.elim h27046 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step125293 (p2797 p2951 p3136 p3212 p3745 p5046 : Prop)
    (h105472 : p5046)
    (h102432 : p2797 ∨ (¬ p3136) ∨ (¬ p2951) ∨ (¬ p3212) ∨ (¬ p5046) ∨ (¬ p3745))
    : (¬ p3136) ∨ p2797 ∨ (¬ p2951) ∨ (¬ p3212) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5046 := h105472;
    (Or.elim h102432 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step125297 (p2255 p3298 p3767 p3848 p5284 : Prop)
    (h105367 : p2255)
    (h48508 : (¬ p2255) ∨ (¬ p3298) ∨ (¬ p3767) ∨ (¬ p3848) ∨ (¬ p5284))
    : (¬ p3767) ∨ (¬ p3848) ∨ (¬ p3298) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3767 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2255 := h105367;
    (Or.elim h48508 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step125298 (p2958 p3755 p3767 p4207 p4790 p5284 : Prop)
    (h106424 : p4790)
    (h102510 : (¬ p5284) ∨ p3755 ∨ (¬ p4207) ∨ (¬ p3767) ∨ (¬ p4790) ∨ (¬ p2958))
    : (¬ p3767) ∨ (¬ p2958) ∨ p3755 ∨ (¬ p5284) ∨ (¬ p4207) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3767 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4790 := h106424;
    (Or.elim h102510 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step125306 (p2230 p2274 p2553 p3389 p4718 : Prop)
    (h105425 : p4718)
    (h102837 : (¬ p2553) ∨ p2274 ∨ (¬ p3389) ∨ (¬ p4718) ∨ p2230)
    : (¬ p3389) ∨ (¬ p2553) ∨ p2274 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4718 := h105425;
    (Or.elim h102837 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step125313 (p2829 p3016 p3367 p4753 : Prop)
    (h105514 : p4753)
    (h102848 : (¬ p2829) ∨ p3016 ∨ p3367 ∨ (¬ p4753))
    : (¬ p2829) ∨ p3016 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4753 := h105514;
    (Or.elim h102848 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125316 (p2210 p2230 p2850 p3379 p5217 : Prop)
    (h105493 : p5217)
    (h102858 : p2850 ∨ (¬ p2230) ∨ (¬ p5217) ∨ p3379 ∨ (¬ p2210))
    : p2850 ∨ (¬ p2230) ∨ p3379 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5217 := h105493;
    (Or.elim h102858 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step125317 (p2210 p2241 p2608 p2651 p2750 p2946 : Prop)
    (h106345 : p2750)
    (h102859 : p2946 ∨ p2210 ∨ (¬ p2651) ∨ p2608 ∨ (¬ p2241) ∨ (¬ p2750))
    : p2946 ∨ p2210 ∨ p2608 ∨ (¬ p2651) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2750 := h106345;
    (Or.elim h102859 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step125319 (p2427 p2891 p3051 p3201 p4730 : Prop)
    (h106074 : p4730)
    (h102864 : (¬ p2891) ∨ p3201 ∨ (¬ p3051) ∨ (¬ p4730) ∨ p2427)
    : (¬ p2891) ∨ (¬ p3051) ∨ p2427 ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4730 := h106074;
    (Or.elim h102864 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step125320 (p2210 p2922 p3379 p4646 : Prop)
    (h105534 : p4646)
    (h67577 : (¬ p3379) ∨ (¬ p2922) ∨ (¬ p4646) ∨ p2210)
    : p2210 ∨ (¬ p2922) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4646 := h105534;
    (Or.elim h67577 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step125321 (p2608 p2651 p2727 p2750 : Prop)
    (h106345 : p2750)
    (h102868 : p2727 ∨ p2608 ∨ (¬ p2651) ∨ (¬ p2750))
    : (¬ p2651) ∨ p2727 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2750 := h106345;
    (Or.elim h102868 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125322 (p2331 p2440 p2651 p4715 : Prop)
    (h105423 : p4715)
    (h102869 : p2331 ∨ (¬ p2651) ∨ (¬ p4715) ∨ p2440)
    : p2331 ∨ (¬ p2651) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4715 := h105423;
    (Or.elim h102869 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step125324 (p2230 p2651 p2946 p3389 p4646 : Prop)
    (h105534 : p4646)
    (h102874 : p2946 ∨ (¬ p3389) ∨ (¬ p2651) ∨ p2230 ∨ (¬ p4646))
    : p2946 ∨ (¬ p2651) ∨ (¬ p3389) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4646 := h105534;
    (Or.elim h102874 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125328 (p2187 p2331 p2668 p2797 p3136 p4790 : Prop)
    (h106424 : p4790)
    (h102883 : p2797 ∨ (¬ p2331) ∨ p2668 ∨ (¬ p3136) ∨ (¬ p2187) ∨ (¬ p4790))
    : p2797 ∨ (¬ p2187) ∨ (¬ p2331) ∨ (¬ p3136) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4790 := h106424;
    (Or.elim h102883 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step125329 (p2192 p2249 p2284 p2331 p3745 p4365 p4960 : Prop)
    (h106513 : p2249)
    (h106209 : p4960)
    (h102884 : (¬ p4365) ∨ p2331 ∨ (¬ p3745) ∨ (¬ p4960) ∨ p2284 ∨ (¬ p2192) ∨ (¬ p2249))
    : p2331 ∨ (¬ p3745) ∨ (¬ p4365) ∨ p2284 ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2249 := h106513;
    let u6 : p4960 := h106209;
    (Or.elim h102884 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step125331 (p2651 p2946 p3083 p4608 : Prop)
    (h105540 : p4608)
    (h102895 : (¬ p2946) ∨ p3083 ∨ (¬ p4608) ∨ p2651)
    : p3083 ∨ (¬ p2946) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4608 := h105540;
    (Or.elim h102895 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step125335 (p2437 p2717 p2850 p2881 p3201 p4750 : Prop)
    (h105433 : p4750)
    (h102898 : p2717 ∨ (¬ p2881) ∨ (¬ p2437) ∨ p3201 ∨ (¬ p4750) ∨ (¬ p2850))
    : p3201 ∨ p2717 ∨ (¬ p2881) ∨ (¬ p2850) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4750 := h105433;
    (Or.elim h102898 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step125336 (p2331 p2563 p2946 p4702 : Prop)
    (h106079 : p4702)
    (h102900 : (¬ p2946) ∨ p2331 ∨ (¬ p2563) ∨ (¬ p4702))
    : (¬ p2946) ∨ p2331 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4702 := h106079;
    (Or.elim h102900 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125337 (p2210 p2241 p2608 p2750 p2946 : Prop)
    (h106345 : p2750)
    (h102901 : (¬ p2241) ∨ p2210 ∨ (¬ p2750) ∨ p2608 ∨ (¬ p2946))
    : (¬ p2946) ∨ p2210 ∨ p2608 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2750 := h106345;
    (Or.elim h102901 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step125338 (p2230 p2373 p2440 p2528 p2850 p3156 p3362 p3422 p3693 p4715 : Prop)
    (h105423 : p4715)
    (h102904 : (¬ p3156) ∨ (¬ p2528) ∨ p3422 ∨ (¬ p2230) ∨ (¬ p3693) ∨ (¬ p2850) ∨ p2440 ∨ p2373 ∨ (¬ p4715) ∨ (¬ p3362))
    : (¬ p3156) ∨ (¬ p2850) ∨ (¬ p3362) ∨ p2373 ∨ (¬ p3693) ∨ (¬ p2230) ∨ p2440 ∨ (¬ p2528) ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4715 := h105423;
    (Or.elim h102904 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step125342 (p2132 p2156 p2563 p2598 p4392 p4749 : Prop)
    (h105432 : p4749)
    (h102911 : (¬ p4392) ∨ (¬ p2132) ∨ (¬ p2156) ∨ p2563 ∨ (¬ p4749) ∨ p2598)
    : (¬ p4392) ∨ (¬ p2132) ∨ p2563 ∨ p2598 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4392 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4749 := h105432;
    (Or.elim h102911 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step125345 (p2427 p2493 p2891 p4715 : Prop)
    (h105423 : p4715)
    (h102919 : (¬ p2891) ∨ p2427 ∨ p2493 ∨ (¬ p4715))
    : (¬ p2891) ∨ p2493 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4715 := h105423;
    (Or.elim h102919 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125347 (p2156 p2210 p2241 p2563 p2750 p3369 p3371 : Prop)
    (h106345 : p2750)
    (h102925 : (¬ p2563) ∨ p2210 ∨ p2156 ∨ (¬ p3371) ∨ (¬ p3369) ∨ (¬ p2750) ∨ (¬ p2241))
    : p2210 ∨ (¬ p3371) ∨ p2156 ∨ (¬ p3369) ∨ (¬ p2241) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2750 := h106345;
    (Or.elim h102925 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step125349 (p2284 p2363 p2383 p2727 p2891 p2992 p3743 p4558 : Prop)
    (h105400 : p4558)
    (h102928 : (¬ p2383) ∨ (¬ p3743) ∨ (¬ p2363) ∨ p2284 ∨ (¬ p2992) ∨ (¬ p4558) ∨ (¬ p2891) ∨ p2727)
    : (¬ p2891) ∨ (¬ p3743) ∨ p2727 ∨ (¬ p2363) ∨ p2284 ∨ (¬ p2992) ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4558 := h105400;
    (Or.elim h102928 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (u2 r6)))))))))))))))))

theorem step125351 (p2210 p2440 p2922 p3399 p3741 p4811 : Prop)
    (h105633 : p4811)
    (h102931 : (¬ p3399) ∨ p2210 ∨ p2922 ∨ (¬ p3741) ∨ (¬ p4811) ∨ p2440)
    : p2210 ∨ p2922 ∨ p2440 ∨ (¬ p3399) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4811 := h105633;
    (Or.elim h102931 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u2 r4)))))))))))))

theorem step125353 (p2088 p2156 p3146 p4509 : Prop)
    (h105392 : p4509)
    (h102934 : p3146 ∨ p2156 ∨ (¬ p4509) ∨ (¬ p2088))
    : (¬ p2088) ∨ p2156 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4509 := h105392;
    (Or.elim h102934 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step125357 (p2230 p2274 p2307 p3389 p4717 p4718 : Prop)
    (h105425 : p4718)
    (h105424 : p4717)
    (h102939 : (¬ p2307) ∨ p2274 ∨ (¬ p4717) ∨ p2230 ∨ (¬ p3389) ∨ (¬ p4718))
    : (¬ p3389) ∨ (¬ p2307) ∨ p2230 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4718 := h105425;
    let u5 : p4717 := h105424;
    (Or.elim h102939 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step125358 (p2295 p2352 p2383 p2668 p3389 p4711 : Prop)
    (h105655 : p4711)
    (h102940 : (¬ p3389) ∨ (¬ p4711) ∨ (¬ p2352) ∨ (¬ p2295) ∨ p2383 ∨ p2668)
    : p2668 ∨ (¬ p2295) ∨ p2383 ∨ (¬ p2352) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2668) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4711 := h105655;
    (Or.elim h102940 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step125359 (p2481 p2881 p3201 p3641 p4277 p4383 p5203 : Prop)
    (h105490 : p5203)
    (h105380 : p4277)
    (h102942 : (¬ p2481) ∨ (¬ p4383) ∨ p3641 ∨ (¬ p3201) ∨ (¬ p4277) ∨ (¬ p2881) ∨ (¬ p5203))
    : p3641 ∨ (¬ p4383) ∨ (¬ p2881) ∨ (¬ p3201) ∨ (¬ p2481) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2481 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5203 := h105490;
    let u6 : p4277 := h105380;
    (Or.elim h102942 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step125366 (p2274 p2284 p2427 p2651 p2807 p3872 p4705 : Prop)
    (h106238 : p4705)
    (h102960 : (¬ p2284) ∨ (¬ p3872) ∨ (¬ p4705) ∨ (¬ p2274) ∨ (¬ p2807) ∨ p2427 ∨ p2651)
    : p2651 ∨ (¬ p2807) ∨ (¬ p3872) ∨ p2427 ∨ (¬ p2284) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4705 := h106238;
    (Or.elim h102960 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (False.elim (u0 r5)))))))))))))))

theorem step125367 (p2249 p2307 p2331 p2352 p2641 p2807 p4976 : Prop)
    (h106513 : p2249)
    (h105465 : p4976)
    (h102961 : p2331 ∨ (¬ p2641) ∨ p2352 ∨ (¬ p2807) ∨ (¬ p2249) ∨ (¬ p4976) ∨ (¬ p2307))
    : p2331 ∨ (¬ p2307) ∨ (¬ p2641) ∨ (¬ p2807) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2249 := h106513;
    let u6 : p4976 := h105465;
    (Or.elim h102961 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step125371 (p2363 p2641 p2727 p3063 p4975 : Prop)
    (h105464 : p4975)
    (h102969 : (¬ p3063) ∨ p2727 ∨ (¬ p4975) ∨ (¬ p2363) ∨ (¬ p2641))
    : p2727 ∨ (¬ p3063) ∨ (¬ p2363) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4975 := h105464;
    (Or.elim h102969 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step125374 (p2187 p2440 p2668 p3016 p4715 : Prop)
    (h105423 : p4715)
    (h102974 : p2668 ∨ p3016 ∨ (¬ p2187) ∨ p2440 ∨ (¬ p4715))
    : p2440 ∨ p3016 ∨ p2668 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    (Or.elim h102974 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125376 (p2177 p2274 p2668 p2881 p4138 p4564 : Prop)
    (h105401 : p4564)
    (h102976 : (¬ p2881) ∨ (¬ p2274) ∨ p2177 ∨ (¬ p4564) ∨ (¬ p4138) ∨ p2668)
    : (¬ p4138) ∨ (¬ p2881) ∨ p2668 ∨ p2177 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4564 := h105401;
    (Or.elim h102976 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (u2 r4)))))))))))))

theorem step125377 (p2352 p2440 p2668 p3083 p4715 : Prop)
    (h105423 : p4715)
    (h102977 : p3083 ∨ p2440 ∨ (¬ p2352) ∨ (¬ p4715) ∨ p2668)
    : p2440 ∨ p3083 ∨ p2668 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    (Or.elim h102977 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step125378 (p2598 p2774 p2850 p3590 p4257 p4715 : Prop)
    (h105423 : p4715)
    (h72349 : (¬ p2850) ∨ (¬ p2598) ∨ (¬ p3590) ∨ (¬ p4715) ∨ p2774 ∨ (¬ p4257))
    : (¬ p2598) ∨ p2774 ∨ (¬ p2850) ∨ (¬ p4257) ∨ (¬ p3590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4715 := h105423;
    (Or.elim h72349 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step125386 (p2264 p2727 p2881 p2911 p3016 p3872 p4711 : Prop)
    (h105655 : p4711)
    (h102990 : p2911 ∨ (¬ p2264) ∨ p2727 ∨ p3016 ∨ (¬ p4711) ∨ (¬ p2881) ∨ (¬ p3872))
    : p3016 ∨ p2727 ∨ (¬ p3872) ∨ (¬ p2881) ∨ p2911 ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4711 := h105655;
    (Or.elim h102990 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step125391 (p2210 p2241 p2509 p2563 p3379 p4608 : Prop)
    (h105540 : p4608)
    (h102999 : (¬ p2241) ∨ p3379 ∨ (¬ p2509) ∨ p2563 ∨ (¬ p4608) ∨ (¬ p2210))
    : (¬ p2509) ∨ (¬ p2210) ∨ p3379 ∨ (¬ p2241) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4608 := h105540;
    (Or.elim h102999 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step125395 (p2241 p2608 p3367 p4749 : Prop)
    (h105432 : p4749)
    (h103009 : p2608 ∨ (¬ p2241) ∨ (¬ p4749) ∨ p3367)
    : p3367 ∨ (¬ p2241) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3367) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4749 := h105432;
    (Or.elim h103009 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step125396 (p2230 p2440 p2630 p2797 p4715 : Prop)
    (h105423 : p4715)
    (h103018 : p2797 ∨ (¬ p2230) ∨ (¬ p4715) ∨ p2440 ∨ (¬ p2630))
    : p2797 ∨ (¬ p2630) ∨ p2440 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    (Or.elim h103018 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step125400 (p2363 p2459 p2881 p4559 : Prop)
    (h105701 : p4559)
    (h103030 : p2363 ∨ (¬ p2881) ∨ (¬ p4559) ∨ (¬ p2459))
    : (¬ p2881) ∨ (¬ p2459) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4559 := h105701;
    (Or.elim h103030 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step125401 (p2177 p2274 p2352 p2881 p3958 : Prop)
    (h105378 : p3958)
    (h103032 : (¬ p2881) ∨ (¬ p2274) ∨ p2352 ∨ (¬ p3958) ∨ p2177)
    : p2352 ∨ (¬ p2881) ∨ (¬ p2274) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2352) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3958 := h105378;
    (Or.elim h103032 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step125404 (p2440 p2563 p2608 p2839 p3367 p4753 : Prop)
    (h105514 : p4753)
    (h103039 : (¬ p2839) ∨ p2608 ∨ p2563 ∨ (¬ p2440) ∨ (¬ p4753) ∨ p3367)
    : (¬ p2440) ∨ p2563 ∨ p2608 ∨ p3367 ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4753 := h105514;
    (Or.elim h103039 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step125405 (p2230 p2363 p2528 p3146 p3355 p4434 : Prop)
    (h106144 : p4434)
    (h103041 : p2363 ∨ (¬ p3355) ∨ p3146 ∨ p2230 ∨ (¬ p4434) ∨ (¬ p2528))
    : (¬ p3355) ∨ p2230 ∨ p3146 ∨ (¬ p2528) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2230) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4434 := h106144;
    (Or.elim h103041 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step125407 (p2187 p2274 p2318 p2319 p3246 p3743 p3872 p4138 p4668 : Prop)
    (h105414 : p4668)
    (h103047 : (¬ p2319) ∨ (¬ p3246) ∨ (¬ p2274) ∨ (¬ p3872) ∨ (¬ p4138) ∨ p2187 ∨ (¬ p4668) ∨ (¬ p2318) ∨ (¬ p3743))
    : (¬ p2318) ∨ (¬ p3743) ∨ (¬ p2274) ∨ (¬ p3872) ∨ (¬ p4138) ∨ p2187 ∨ (¬ p3246) ∨ (¬ p2319) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4668 := h105414;
    (Or.elim h103047 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step125409 (p2177 p2761 p3246 p3266 p3461 p4559 : Prop)
    (h105701 : p4559)
    (h103049 : p3461 ∨ (¬ p2761) ∨ p2177 ∨ p3266 ∨ (¬ p3246) ∨ (¬ p4559))
    : p3266 ∨ (¬ p3246) ∨ p2177 ∨ p3461 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4559 := h105701;
    (Or.elim h103049 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step125410 (p2396 p2417 p2427 p2563 p4558 : Prop)
    (h105400 : p4558)
    (h103053 : (¬ p2417) ∨ (¬ p2427) ∨ (¬ p4558) ∨ p2563 ∨ p2396)
    : (¬ p2417) ∨ (¬ p2427) ∨ p2563 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h103053 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step125411 (p2417 p3192 p3246 p3276 p3461 p4140 p4712 : Prop)
    (h105422 : p4712)
    (h103054 : (¬ p3276) ∨ p3461 ∨ (¬ p3192) ∨ (¬ p4140) ∨ (¬ p2417) ∨ p3246 ∨ (¬ p4712))
    : (¬ p3276) ∨ (¬ p4140) ∨ (¬ p2417) ∨ p3461 ∨ p3246 ∨ (¬ p3192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4712 := h105422;
    (Or.elim h103054 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step125413 (p2177 p2264 p2363 p3256 p4361 : Prop)
    (h105382 : p4361)
    (h103056 : (¬ p3256) ∨ (¬ p2264) ∨ p2177 ∨ (¬ p4361) ∨ p2363)
    : (¬ p3256) ∨ p2177 ∨ (¬ p2264) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4361 := h105382;
    (Or.elim h103056 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step125418 (p2190 p2427 p2528 p3146 p4558 : Prop)
    (h105400 : p4558)
    (h103075 : (¬ p2190) ∨ p2528 ∨ (¬ p4558) ∨ (¬ p2427) ∨ (¬ p3146))
    : (¬ p2427) ∨ p2528 ∨ (¬ p2190) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h103075 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step125419 (p2088 p2166 p2528 p3146 p4539 p4607 p4632 : Prop)
    (h106257 : p4632)
    (h105395 : p4539)
    (h103079 : p2528 ∨ (¬ p3146) ∨ (¬ p4632) ∨ (¬ p4539) ∨ (¬ p2088) ∨ (¬ p4607) ∨ (¬ p2166))
    : (¬ p2166) ∨ p2528 ∨ (¬ p2088) ∨ (¬ p3146) ∨ (¬ p4607) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4632 := h106257;
    let u6 : p4539 := h105395;
    (Or.elim h103079 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step125420 (p2156 p2210 p2563 p2608 p4877 : Prop)
    (h105451 : p4877)
    (h103080 : p2608 ∨ (¬ p2210) ∨ (¬ p4877) ∨ (¬ p2156) ∨ p2563)
    : (¬ p2210) ∨ p2608 ∨ p2563 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4877 := h105451;
    (Or.elim h103080 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step125421 (p2190 p2284 p2528 p3146 p4705 : Prop)
    (h106238 : p4705)
    (h103084 : (¬ p2190) ∨ (¬ p3146) ∨ (¬ p4705) ∨ (¬ p2284) ∨ p2528)
    : p2528 ∨ (¬ p2284) ∨ (¬ p3146) ∨ (¬ p2190) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4705 := h106238;
    (Or.elim h103084 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step125422 (p2156 p2220 p2352 p3958 : Prop)
    (h105378 : p3958)
    (h103091 : (¬ p2220) ∨ p2156 ∨ p2352 ∨ (¬ p3958))
    : (¬ p2220) ∨ p2156 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3958 := h105378;
    (Or.elim h103091 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125424 (p2177 p2307 p2459 p3093 p3527 p5022 : Prop)
    (h105470 : p5022)
    (h103093 : (¬ p2307) ∨ (¬ p5022) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p2459) ∨ p3527)
    : (¬ p2307) ∨ p3527 ∨ (¬ p2459) ∨ (¬ p3093) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5022 := h105470;
    (Or.elim h103093 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u1 r4)))))))))))))

theorem step125432 (p2839 p2972 p2982 p3367 p4884 : Prop)
    (h105454 : p4884)
    (h103110 : (¬ p2972) ∨ (¬ p2839) ∨ p3367 ∨ p2982 ∨ (¬ p4884))
    : (¬ p2839) ∨ (¬ p2972) ∨ p2982 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4884 := h105454;
    (Or.elim h103110 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125439 (p2274 p2440 p2563 p2630 p4790 : Prop)
    (h106424 : p4790)
    (h103121 : (¬ p2440) ∨ p2274 ∨ p2563 ∨ p2630 ∨ (¬ p4790))
    : p2630 ∨ (¬ p2440) ∨ p2563 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    (Or.elim h103121 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125440 (p2192 p2440 p2563 p4814 : Prop)
    (h105440 : p4814)
    (h103122 : (¬ p2192) ∨ (¬ p4814) ∨ p2563 ∨ (¬ p2440))
    : (¬ p2192) ∨ (¬ p2440) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4814 := h105440;
    (Or.elim h103122 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step125449 (p2829 p2839 p3319 p3367 p3564 p5224 : Prop)
    (h105494 : p5224)
    (h103137 : (¬ p2829) ∨ (¬ p3319) ∨ p3564 ∨ (¬ p5224) ∨ p3367 ∨ p2839)
    : (¬ p3319) ∨ p3564 ∨ p2839 ∨ (¬ p2829) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5224 := h105494;
    (Or.elim h103137 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (u2 r4)))))))))))))

theorem step125451 (p2230 p2696 p2850 p4749 : Prop)
    (h105432 : p4749)
    (h103141 : (¬ p2850) ∨ (¬ p4749) ∨ (¬ p2696) ∨ p2230)
    : (¬ p2850) ∨ (¬ p2696) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4749 := h105432;
    (Or.elim h103141 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step125453 (p2230 p2563 p2573 p3051 p4558 : Prop)
    (h105400 : p4558)
    (h103147 : (¬ p3051) ∨ (¬ p2230) ∨ (¬ p4558) ∨ p2573 ∨ p2563)
    : p2573 ∨ (¬ p3051) ∨ p2563 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h103147 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step125454 (p2177 p2311 p2386 p2911 p3125 p3564 p3581 p4624 p5201 : Prop)
    (h105408 : p4624)
    (h103149 : (¬ p3564) ∨ p3125 ∨ (¬ p5201) ∨ (¬ p3581) ∨ (¬ p2311) ∨ (¬ p2177) ∨ p2911 ∨ (¬ p4624) ∨ (¬ p2386))
    : (¬ p5201) ∨ p2911 ∨ (¬ p2177) ∨ (¬ p3564) ∨ (¬ p2386) ∨ p3125 ∨ (¬ p3581) ∨ (¬ p2311) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4624 := h105408;
    (Or.elim h103149 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step125458 (p2696 p2870 p2901 p3425 p4906 : Prop)
    (h105632 : p4906)
    (h103157 : (¬ p3425) ∨ (¬ p2901) ∨ p2870 ∨ (¬ p4906) ∨ (¬ p2696))
    : (¬ p3425) ∨ (¬ p2696) ∨ (¬ p2901) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4906 := h105632;
    (Or.elim h103157 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step125459 (p2417 p2870 p3246 p3741 p4283 p4882 p4988 : Prop)
    (h105453 : p4882)
    (h103159 : p2870 ∨ p3246 ∨ (¬ p2417) ∨ (¬ p4882) ∨ (¬ p4283) ∨ (¬ p4988) ∨ (¬ p3741))
    : (¬ p4283) ∨ p2870 ∨ (¬ p2417) ∨ p3246 ∨ (¬ p4988) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4283 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4882 := h105453;
    (Or.elim h103159 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step125460 (p2437 p2440 p2870 p4882 : Prop)
    (h105453 : p4882)
    (h103160 : p2870 ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p4882))
    : p2870 ∨ (¬ p2437) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4882 := h105453;
    (Or.elim h103160 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125461 (p2156 p2177 p2319 p2396 p2427 p2563 p2911 p3246 p3741 p4533 : Prop)
    (h105394 : p4533)
    (h103163 : (¬ p2319) ∨ (¬ p2911) ∨ (¬ p2563) ∨ (¬ p2427) ∨ (¬ p3741) ∨ (¬ p3246) ∨ (¬ p2396) ∨ p2156 ∨ p2177 ∨ (¬ p4533))
    : p2177 ∨ (¬ p2911) ∨ (¬ p2563) ∨ (¬ p3741) ∨ (¬ p2427) ∨ (¬ p2319) ∨ p2156 ∨ (¬ p3246) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2177) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4533 := h105394;
    (Or.elim h103163 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u0 q8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step125464 (p2249 p2437 p2630 p2751 p2922 p4281 p4790 : Prop)
    (h106343 : p2751)
    (h106513 : p2249)
    (h106424 : p4790)
    (h103170 : (¬ p2922) ∨ p2437 ∨ (¬ p4281) ∨ (¬ p2249) ∨ (¬ p4790) ∨ (¬ p2751) ∨ p2630)
    : p2630 ∨ (¬ p2922) ∨ p2437 ∨ (¬ p4281) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    let u5 : p2249 := h106513;
    let u6 : p4790 := h106424;
    (Or.elim h103170 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (u0 r5)))))))))))))))

theorem step125470 (p2098 p2177 p2241 p2245 p2249 p2274 p2363 p2563 p2608 p2727 p2737 p3367 p3487 p4281 p4814 : Prop)
    (h106513 : p2249)
    (h105440 : p4814)
    (h103178 : p2098 ∨ (¬ p2245) ∨ (¬ p3487) ∨ (¬ p2737) ∨ (¬ p4281) ∨ p2563 ∨ p2608 ∨ p2241 ∨ (¬ p2274) ∨ (¬ p2249) ∨ (¬ p3367) ∨ (¬ p4814) ∨ p2177 ∨ (¬ p2363) ∨ (¬ p2727))
    : p2098 ∨ p2608 ∨ p2563 ∨ (¬ p2245) ∨ (¬ p4281) ∨ p2177 ∨ (¬ p2737) ∨ (¬ p3487) ∨ (¬ p2363) ∨ p2241 ∨ (¬ p3367) ∨ (¬ p2274) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p2249 := h106513;
    let u14 : p4814 := h105440;
    (Or.elim h103178 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u9 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u13))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u14))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (u5 q12))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u8))) (fun r13 => (False.elim (r13 u12)))))))))))))))))))))))))))))))

theorem step125471 (p2210 p2440 p3379 p4814 : Prop)
    (h105440 : p4814)
    (h103179 : p3379 ∨ (¬ p2210) ∨ (¬ p4814) ∨ (¬ p2440))
    : (¬ p2210) ∨ p3379 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4814 := h105440;
    (Or.elim h103179 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step125473 (p2187 p2331 p2797 p3005 p4564 p4584 p4769 : Prop)
    (h105401 : p4564)
    (h105406 : p4584)
    (h103181 : p3005 ∨ (¬ p2331) ∨ (¬ p4564) ∨ (¬ p4769) ∨ (¬ p4584) ∨ (¬ p2187) ∨ (¬ p2797))
    : (¬ p2797) ∨ p3005 ∨ (¬ p2331) ∨ (¬ p4769) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4564 := h105401;
    let u6 : p4584 := h105406;
    (Or.elim h103181 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step125477 (p2220 p2230 p2440 p2619 p2659 p3156 p3413 p4109 p4750 : Prop)
    (h105433 : p4750)
    (h103190 : p2619 ∨ p2440 ∨ (¬ p4750) ∨ (¬ p4109) ∨ (¬ p3413) ∨ (¬ p3156) ∨ p2230 ∨ (¬ p2220) ∨ (¬ p2659))
    : p2619 ∨ (¬ p3156) ∨ p2440 ∨ (¬ p2220) ∨ (¬ p3413) ∨ (¬ p4109) ∨ (¬ p2659) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4750 := h105433;
    (Or.elim h103190 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step125481 (p2132 p2427 p2850 p2881 p3379 p5217 : Prop)
    (h105493 : p5217)
    (h103197 : p2132 ∨ p2850 ∨ (¬ p5217) ∨ p3379 ∨ p2881 ∨ p2427)
    : p2427 ∨ p2850 ∨ p3379 ∨ p2132 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5217 := h105493;
    (Or.elim h103197 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step125483 (p2132 p2440 p2696 p2850 p4750 : Prop)
    (h105433 : p4750)
    (h103199 : p2132 ∨ p2440 ∨ (¬ p4750) ∨ (¬ p2696) ∨ p2850)
    : p2850 ∨ p2440 ∨ (¬ p2696) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    (Or.elim h103199 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step125484 (p2246 p2685 p2751 p2901 p2946 p3051 : Prop)
    (h106343 : p2751)
    (h103201 : (¬ p3051) ∨ p2901 ∨ (¬ p2246) ∨ p2685 ∨ (¬ p2751) ∨ (¬ p2946))
    : p2685 ∨ (¬ p3051) ∨ p2901 ∨ (¬ p2246) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    (Or.elim h103201 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step125486 (p2850 p2901 p3096 p3201 p3422 p4705 : Prop)
    (h106238 : p4705)
    (h103206 : p3201 ∨ (¬ p2901) ∨ (¬ p4705) ∨ (¬ p3096) ∨ (¬ p2850) ∨ p3422)
    : (¬ p2850) ∨ p3201 ∨ (¬ p2901) ∨ p3422 ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    (Or.elim h103206 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step125490 (p2284 p2954 p3125 p3654 : Prop)
    (h106494 : p2954)
    (h68999 : (¬ p3125) ∨ (¬ p2954) ∨ p3654 ∨ (¬ p2284))
    : p3654 ∨ (¬ p2284) ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2954 := h106494;
    (Or.elim h68999 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step125494 (p2166 p2220 p2246 p2619 p2630 p2751 p3136 p4392 : Prop)
    (h106343 : p2751)
    (h103229 : (¬ p2751) ∨ p3136 ∨ (¬ p4392) ∨ (¬ p2220) ∨ (¬ p2166) ∨ (¬ p2630) ∨ (¬ p2246) ∨ p2619)
    : (¬ p4392) ∨ p2619 ∨ (¬ p2246) ∨ p3136 ∨ (¬ p2166) ∨ (¬ p2630) ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4392 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2751 := h106343;
    (Or.elim h103229 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step125499 (p2341 p2427 p2590 p2901 p2911 p3370 p3581 p4632 p4705 : Prop)
    (h106238 : p4705)
    (h106257 : p4632)
    (h103236 : (¬ p2901) ∨ (¬ p3370) ∨ (¬ p2341) ∨ (¬ p2590) ∨ p2911 ∨ (¬ p3581) ∨ p2427 ∨ (¬ p4632) ∨ (¬ p4705))
    : (¬ p3370) ∨ (¬ p2341) ∨ (¬ p2590) ∨ p2911 ∨ (¬ p2901) ∨ (¬ p3581) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4705 := h106238;
    let u8 : p4632 := h106257;
    (Or.elim h103236 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step125502 (p2166 p2177 p2192 p2881 p4556 : Prop)
    (h105399 : p4556)
    (h103242 : (¬ p2192) ∨ p2166 ∨ (¬ p4556) ∨ (¬ p2177) ∨ p2881)
    : p2166 ∨ (¬ p2192) ∨ (¬ p2177) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2166) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4556 := h105399;
    (Or.elim h103242 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step125507 (p2563 p2850 p3201 p4555 : Prop)
    (h105542 : p4555)
    (h69099 : (¬ p2850) ∨ p3201 ∨ (¬ p2563) ∨ (¬ p4555))
    : (¬ p2850) ∨ p3201 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4555 := h105542;
    (Or.elim h69099 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125508 (p2132 p2753 p2774 p2850 p3201 p4644 p4715 : Prop)
    (h105423 : p4715)
    (h105411 : p4644)
    (h103255 : p2774 ∨ (¬ p2132) ∨ p3201 ∨ (¬ p2850) ∨ (¬ p2753) ∨ (¬ p4715) ∨ (¬ p4644))
    : p3201 ∨ (¬ p2850) ∨ p2774 ∨ (¬ p2132) ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4715 := h105423;
    let u6 : p4644 := h105411;
    (Or.elim h103255 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step125509 (p2166 p2619 p2751 p2992 p3136 p4392 : Prop)
    (h106343 : p2751)
    (h103258 : (¬ p2992) ∨ p2619 ∨ (¬ p2751) ∨ (¬ p2166) ∨ p3136 ∨ (¬ p4392))
    : (¬ p4392) ∨ p2619 ∨ (¬ p2992) ∨ (¬ p2166) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4392 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    (Or.elim h103258 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step125510 (p2230 p2440 p2630 p2751 p2850 p2992 p4790 : Prop)
    (h106343 : p2751)
    (h106424 : p4790)
    (h103259 : (¬ p2992) ∨ p2630 ∨ (¬ p2751) ∨ (¬ p4790) ∨ p2440 ∨ (¬ p2230) ∨ p2850)
    : p2850 ∨ p2630 ∨ (¬ p2992) ∨ p2440 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    let u6 : p4790 := h106424;
    (Or.elim h103259 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (u0 r5)))))))))))))))

theorem step125511 (p2440 p2727 p2922 p2992 p4644 : Prop)
    (h105411 : p4644)
    (h103260 : p2727 ∨ (¬ p2992) ∨ p2922 ∨ (¬ p4644) ∨ p2440)
    : p2922 ∨ (¬ p2992) ∨ p2727 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4644 := h105411;
    (Or.elim h103260 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step125512 (p2751 p2870 p2901 p2992 : Prop)
    (h106343 : p2751)
    (h68388 : p2870 ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p2751))
    : (¬ p2992) ∨ p2870 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2751 := h106343;
    (Or.elim h68388 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125515 (p2245 p2295 p2553 p2630 p2641 p2727 p4790 p4976 : Prop)
    (h106424 : p4790)
    (h105465 : p4976)
    (h103263 : p2641 ∨ (¬ p2727) ∨ p2553 ∨ p2630 ∨ (¬ p2245) ∨ (¬ p4790) ∨ (¬ p4976) ∨ p2295)
    : p2630 ∨ (¬ p2727) ∨ (¬ p2245) ∨ p2553 ∨ p2295 ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4790 := h106424;
    let u7 : p4976 := h105465;
    (Or.elim h103263 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step125519 (p2249 p2274 p2295 p2307 p2807 p2996 : Prop)
    (h106513 : p2249)
    (h103273 : p2307 ∨ p2274 ∨ (¬ p2295) ∨ (¬ p2249) ∨ p2996 ∨ p2807)
    : p2807 ∨ (¬ p2295) ∨ p2274 ∨ p2996 ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2807) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2249 := h106513;
    (Or.elim h103273 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step125521 (p2210 p2406 p2608 p2850 p5217 : Prop)
    (h105493 : p5217)
    (h103276 : p2608 ∨ (¬ p2406) ∨ (¬ p2210) ∨ (¬ p5217) ∨ p2850)
    : p2850 ∨ (¬ p2406) ∨ p2608 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5217 := h105493;
    (Or.elim h103276 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step125524 (p2274 p3093 p3399 p4518 : Prop)
    (h106113 : p4518)
    (h103290 : p3093 ∨ (¬ p3399) ∨ p2274 ∨ (¬ p4518))
    : (¬ p3399) ∨ p3093 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4518 := h106113;
    (Or.elim h103290 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125526 (p2363 p3146 p3323 p3988 p4433 : Prop)
    (h106150 : p4433)
    (h103296 : (¬ p3323) ∨ p3146 ∨ (¬ p3988) ∨ (¬ p4433) ∨ (¬ p2363))
    : (¬ p3323) ∨ p3146 ∨ (¬ p2363) ∨ (¬ p3988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4433 := h106150;
    (Or.elim h103296 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step125529 (p2363 p2563 p2598 p2850 p3146 p3266 p4433 : Prop)
    (h106150 : p4433)
    (h103301 : p3146 ∨ (¬ p3266) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p4433) ∨ (¬ p2363))
    : (¬ p3266) ∨ p3146 ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2563) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4433 := h106150;
    (Or.elim h103301 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step125536 (p2132 p2440 p2493 p2590 p2696 p2737 p2774 p3083 p3367 p4608 p5217 : Prop)
    (h105540 : p4608)
    (h105493 : p5217)
    (h103308 : p2696 ∨ (¬ p2132) ∨ p3083 ∨ (¬ p3367) ∨ (¬ p2590) ∨ (¬ p4608) ∨ (¬ p2737) ∨ (¬ p2493) ∨ p2774 ∨ (¬ p5217) ∨ (¬ p2440))
    : p2774 ∨ (¬ p2132) ∨ (¬ p2440) ∨ (¬ p2493) ∨ (¬ p2737) ∨ (¬ p3367) ∨ (¬ p2590) ∨ p2696 ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4608 := h105540;
    let u10 : p5217 := h105493;
    (Or.elim h103308 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u0 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u2)))))))))))))))))))))))

theorem step125541 (p2230 p2246 p2406 p2641 p2727 p3016 p4717 : Prop)
    (h105424 : p4717)
    (h103325 : (¬ p2246) ∨ (¬ p2641) ∨ (¬ p4717) ∨ (¬ p3016) ∨ p2230 ∨ p2406 ∨ p2727)
    : p2230 ∨ p2727 ∨ p2406 ∨ (¬ p2246) ∨ (¬ p2641) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2230) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4717 := h105424;
    (Or.elim h103325 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (False.elim (u1 r5)))))))))))))))

theorem step125542 (p2230 p2241 p2246 p2406 p2553 p2641 p2727 p4717 : Prop)
    (h105424 : p4717)
    (h103326 : (¬ p2246) ∨ (¬ p2641) ∨ p2406 ∨ p2727 ∨ (¬ p4717) ∨ p2553 ∨ p2241 ∨ p2230)
    : p2230 ∨ p2727 ∨ p2241 ∨ (¬ p2246) ∨ p2553 ∨ (¬ p2641) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2230) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4717 := h105424;
    (Or.elim h103326 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step125549 (p2363 p2373 p2982 p4433 : Prop)
    (h106150 : p4433)
    (h103343 : p2982 ∨ (¬ p2363) ∨ (¬ p4433) ∨ (¬ p2373))
    : p2982 ∨ (¬ p2373) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4433 := h106150;
    (Or.elim h103343 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step125551 (p2156 p2220 p2341 p2881 p4555 : Prop)
    (h105542 : p4555)
    (h103345 : p2220 ∨ p2341 ∨ (¬ p2156) ∨ (¬ p2881) ∨ (¬ p4555))
    : p2220 ∨ p2341 ∨ (¬ p2881) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    (Or.elim h103345 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125552 (p2177 p2274 p2911 p4718 : Prop)
    (h105425 : p4718)
    (h103347 : (¬ p2911) ∨ p2274 ∨ (¬ p4718) ∨ p2177)
    : (¬ p2911) ∨ p2177 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4718 := h105425;
    (Or.elim h103347 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step125553 (p2363 p2417 p2911 p4503 : Prop)
    (h106530 : p4503)
    (h68915 : p2417 ∨ (¬ p2911) ∨ (¬ p4503) ∨ (¬ p2363))
    : p2417 ∨ (¬ p2911) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4503 := h106530;
    (Or.elim h68915 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step125559 (p2122 p2295 p2573 p3016 p3347 p4750 p4811 : Prop)
    (h105433 : p4750)
    (h105633 : p4811)
    (h103361 : (¬ p2295) ∨ p2122 ∨ (¬ p3347) ∨ (¬ p4750) ∨ (¬ p4811) ∨ (¬ p3016) ∨ p2573)
    : p2573 ∨ p2122 ∨ (¬ p3016) ∨ (¬ p2295) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4750 := h105433;
    let u6 : p4811 := h105633;
    (Or.elim h103361 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (u0 r5)))))))))))))))

theorem step125565 (p2132 p2440 p2598 p4750 : Prop)
    (h105433 : p4750)
    (h103374 : p2132 ∨ p2440 ∨ (¬ p2598) ∨ (¬ p4750))
    : (¬ p2598) ∨ p2132 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4750 := h105433;
    (Or.elim h103374 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125566 (p2098 p2598 p3083 p4750 : Prop)
    (h105433 : p4750)
    (h103376 : p2098 ∨ (¬ p3083) ∨ (¬ p4750) ∨ (¬ p2598))
    : p2098 ∨ (¬ p2598) ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4750 := h105433;
    (Or.elim h103376 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step125568 (p2274 p2563 p3309 p4632 : Prop)
    (h106257 : p4632)
    (h103380 : (¬ p3309) ∨ p2274 ∨ p2563 ∨ (¬ p4632))
    : (¬ p3309) ∨ p2563 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4632 := h106257;
    (Or.elim h103380 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125569 (p2210 p2563 p3093 p4632 : Prop)
    (h106257 : p4632)
    (h103381 : (¬ p3093) ∨ p2210 ∨ (¬ p4632) ∨ p2563)
    : p2210 ∨ p2563 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4632 := h106257;
    (Or.elim h103381 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step125573 (p2122 p2352 p2850 p3955 p4715 : Prop)
    (h105423 : p4715)
    (h103394 : p2122 ∨ (¬ p2352) ∨ (¬ p2850) ∨ (¬ p3955) ∨ (¬ p4715))
    : (¬ p2850) ∨ (¬ p2352) ∨ p2122 ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    (Or.elim h103394 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125582 (p2274 p2363 p2459 p2563 p3093 p3125 p4503 p4632 : Prop)
    (h106257 : p4632)
    (h106530 : p4503)
    (h103413 : (¬ p3125) ∨ p3093 ∨ p2274 ∨ (¬ p4503) ∨ p2459 ∨ (¬ p2363) ∨ p2563 ∨ (¬ p4632))
    : (¬ p3125) ∨ (¬ p2363) ∨ p2274 ∨ p2563 ∨ p2459 ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4632 := h106257;
    let u7 : p4503 := h106530;
    (Or.elim h103413 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step125583 (p2230 p2406 p2505 p2553 p3309 p4717 p5191 : Prop)
    (h105424 : p4717)
    (h103418 : (¬ p3309) ∨ p2553 ∨ (¬ p5191) ∨ p2406 ∨ (¬ p2505) ∨ p2230 ∨ (¬ p4717))
    : (¬ p5191) ∨ p2406 ∨ (¬ p2505) ∨ p2230 ∨ (¬ p3309) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2406) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4717 := h105424;
    (Or.elim h103418 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step125590 (p2210 p2241 p2651 p2749 p4877 : Prop)
    (h105451 : p4877)
    (h103431 : p2241 ∨ (¬ p4877) ∨ p2651 ∨ (¬ p2749) ∨ (¬ p2210))
    : (¬ p2749) ∨ p2651 ∨ p2241 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2749 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4877 := h105451;
    (Or.elim h103431 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step125591 (p2210 p2241 p2284 p2630 p2737 p4117 p4877 : Prop)
    (h105451 : p4877)
    (h103432 : (¬ p4877) ∨ p2241 ∨ p2630 ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p2210) ∨ (¬ p4117))
    : (¬ p4117) ∨ p2630 ∨ (¬ p2737) ∨ (¬ p2210) ∨ (¬ p2284) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4117 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4877 := h105451;
    (Or.elim h103432 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step125595 (p2177 p2274 p2284 p2406 p3379 p3660 p4203 p4702 : Prop)
    (h106079 : p4702)
    (h103444 : p3379 ∨ p2284 ∨ p2274 ∨ (¬ p4702) ∨ p2406 ∨ (¬ p3660) ∨ (¬ p4203) ∨ p2177)
    : p3379 ∨ (¬ p3660) ∨ p2284 ∨ (¬ p4203) ∨ p2406 ∨ p2274 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4702 := h106079;
    (Or.elim h103444 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (u6 r6)))))))))))))))))

theorem step125600 (p2156 p2192 p2284 p2797 p4790 p4960 : Prop)
    (h106424 : p4790)
    (h106209 : p4960)
    (h103452 : p2797 ∨ p2284 ∨ (¬ p4790) ∨ (¬ p2156) ∨ (¬ p2192) ∨ (¬ p4960))
    : p2797 ∨ (¬ p2192) ∨ (¬ p2156) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    let u5 : p4960 := h106209;
    (Or.elim h103452 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step125601 (p2241 p2249 p2274 p2440 p2553 p2590 p2630 p2751 p3422 p4790 : Prop)
    (h106343 : p2751)
    (h106513 : p2249)
    (h106424 : p4790)
    (h103453 : (¬ p2274) ∨ (¬ p2249) ∨ (¬ p4790) ∨ p3422 ∨ p2440 ∨ p2630 ∨ (¬ p2590) ∨ (¬ p2751) ∨ p2241 ∨ p2553)
    : p3422 ∨ p2630 ∨ p2241 ∨ (¬ p2590) ∨ (¬ p2274) ∨ p2553 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2751 := h106343;
    let u8 : p2249 := h106513;
    let u9 : p4790 := h106424;
    (Or.elim h103453 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u2 q8))) (fun r8 => (False.elim (u5 r8)))))))))))))))))))))

theorem step125602 (p2284 p2737 p2829 p2860 p4906 : Prop)
    (h105632 : p4906)
    (h103463 : (¬ p2284) ∨ p2829 ∨ p2860 ∨ (¬ p2737) ∨ (¬ p4906))
    : p2860 ∨ (¬ p2737) ∨ (¬ p2284) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4906 := h105632;
    (Or.elim h103463 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125603 (p2098 p2187 p2598 p2753 p2850 p4715 : Prop)
    (h105423 : p4715)
    (h103466 : p2098 ∨ (¬ p2850) ∨ (¬ p2753) ∨ (¬ p2187) ∨ (¬ p4715) ∨ (¬ p2598))
    : (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2187) ∨ p2098 ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4715 := h105423;
    (Or.elim h103466 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step125604 (p2829 p2850 p3367 p4715 : Prop)
    (h105423 : p4715)
    (h68719 : (¬ p3367) ∨ p2829 ∨ (¬ p2850) ∨ (¬ p4715))
    : (¬ p3367) ∨ p2829 ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4715 := h105423;
    (Or.elim h68719 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125612 (p2274 p2417 p3125 p4276 : Prop)
    (h105516 : p4276)
    (h103484 : p2417 ∨ (¬ p3125) ∨ p2274 ∨ (¬ p4276))
    : (¬ p3125) ∨ p2417 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4276 := h105516;
    (Or.elim h103484 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125614 (p2417 p2437 p3434 p4750 : Prop)
    (h105433 : p4750)
    (h68672 : (¬ p2417) ∨ p3434 ∨ (¬ p4750) ∨ (¬ p2437))
    : p3434 ∨ (¬ p2417) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4750 := h105433;
    (Or.elim h68672 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step125615 (p2630 p2727 p3016 p3136 p3879 p4717 : Prop)
    (h105424 : p4717)
    (h103486 : p3136 ∨ (¬ p3016) ∨ (¬ p2630) ∨ (¬ p3879) ∨ (¬ p4717) ∨ (¬ p2727))
    : (¬ p2630) ∨ p3136 ∨ (¬ p3879) ∨ (¬ p3016) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3136) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4717 := h105424;
    (Or.elim h103486 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step125616 (p2241 p2563 p2573 p2750 p2881 p3379 p3541 p4558 : Prop)
    (h106345 : p2750)
    (h105400 : p4558)
    (h103489 : (¬ p2241) ∨ (¬ p3541) ∨ p3379 ∨ (¬ p2750) ∨ p2881 ∨ (¬ p4558) ∨ p2563 ∨ p2573)
    : p2573 ∨ (¬ p3541) ∨ p2563 ∨ (¬ p2241) ∨ p3379 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2750 := h106345;
    let u7 : p4558 := h105400;
    (Or.elim h103489 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step125618 (p2352 p2363 p3016 p3093 p3379 p4811 : Prop)
    (h105633 : p4811)
    (h103493 : p3093 ∨ (¬ p2352) ∨ (¬ p3016) ∨ (¬ p4811) ∨ (¬ p3379) ∨ (¬ p2363))
    : (¬ p3379) ∨ p3093 ∨ (¬ p2363) ∨ (¬ p2352) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3379 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4811 := h105633;
    (Or.elim h103493 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step125619 (p2122 p2553 p3016 p4750 : Prop)
    (h105433 : p4750)
    (h103494 : (¬ p2553) ∨ p2122 ∨ (¬ p4750) ∨ (¬ p3016))
    : p2122 ∨ (¬ p2553) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4750 := h105433;
    (Or.elim h103494 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step125623 (p2598 p2753 p2774 p2850 p4715 : Prop)
    (h105423 : p4715)
    (h103498 : (¬ p2598) ∨ p2774 ∨ (¬ p4715) ∨ (¬ p2850) ∨ (¬ p2753))
    : (¬ p2598) ∨ p2774 ∨ (¬ p2850) ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    (Or.elim h103498 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step125625 (p2528 p2850 p3609 p4608 : Prop)
    (h105540 : p4608)
    (h103500 : (¬ p2850) ∨ p3609 ∨ (¬ p2528) ∨ (¬ p4608))
    : (¬ p2850) ∨ p3609 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4608 := h105540;
    (Or.elim h103500 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125627 (p2187 p2249 p2274 p2307 p2641 p2946 p4153 : Prop)
    (h106513 : p2249)
    (h103502 : p2307 ∨ (¬ p2641) ∨ p2187 ∨ (¬ p2274) ∨ p2946 ∨ (¬ p4153) ∨ (¬ p2249))
    : (¬ p4153) ∨ p2946 ∨ (¬ p2274) ∨ p2307 ∨ p2187 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4153 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2249 := h106513;
    (Or.elim h103502 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step125642 (p2210 p2406 p3083 p3449 p4607 p4811 : Prop)
    (h105633 : p4811)
    (h103536 : p3449 ∨ (¬ p2210) ∨ p2406 ∨ (¬ p4607) ∨ (¬ p3083) ∨ (¬ p4811))
    : p3449 ∨ (¬ p4607) ∨ (¬ p3083) ∨ (¬ p2210) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4811 := h105633;
    (Or.elim h103536 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step125643 (p2210 p3201 p3379 p3399 p4210 p4644 p5217 : Prop)
    (h105411 : p4644)
    (h105493 : p5217)
    (h103537 : (¬ p3399) ∨ p3201 ∨ (¬ p2210) ∨ (¬ p5217) ∨ p3379 ∨ (¬ p4644) ∨ (¬ p4210))
    : (¬ p2210) ∨ p3201 ∨ (¬ p4210) ∨ (¬ p3399) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4644 := h105411;
    let u6 : p5217 := h105493;
    (Or.elim h103537 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step125651 (p2230 p2406 p2553 p3309 p4717 p5191 : Prop)
    (h105424 : p4717)
    (h103558 : (¬ p3309) ∨ p2553 ∨ (¬ p4717) ∨ p2406 ∨ p2230 ∨ (¬ p5191))
    : (¬ p5191) ∨ p2406 ∨ p2553 ∨ p2230 ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2406) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4717 := h105424;
    (Or.elim h103558 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step125655 (p2177 p2220 p2427 p2563 p2911 p3370 p4555 p4632 : Prop)
    (h105542 : p4555)
    (h106257 : p4632)
    (h103571 : (¬ p3370) ∨ (¬ p2220) ∨ (¬ p4632) ∨ p2427 ∨ (¬ p4555) ∨ (¬ p2177) ∨ p2911 ∨ (¬ p2563))
    : (¬ p2220) ∨ (¬ p3370) ∨ p2427 ∨ (¬ p2563) ∨ p2911 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4555 := h105542;
    let u7 : p4632 := h106257;
    (Or.elim h103571 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step125656 (p2406 p3379 p3399 p4646 : Prop)
    (h105534 : p4646)
    (h103572 : (¬ p3399) ∨ p3379 ∨ (¬ p4646) ∨ p2406)
    : p2406 ∨ p3379 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4646 := h105534;
    (Or.elim h103572 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step125659 (p2528 p2563 p3146 p4509 : Prop)
    (h105392 : p4509)
    (h103575 : (¬ p2528) ∨ p3146 ∨ (¬ p4509) ∨ p2563)
    : (¬ p2528) ∨ p2563 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4509 := h105392;
    (Or.elim h103575 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step125661 (p2132 p2156 p2528 p2563 p2651 p2655 p2659 p2685 p2696 p2737 p2901 p3051 p4558 p5190 : Prop)
    (h105400 : p4558)
    (h105487 : p5190)
    (h103577 : (¬ p3051) ∨ (¬ p4558) ∨ p2563 ∨ p2685 ∨ (¬ p2655) ∨ p2651 ∨ (¬ p2528) ∨ p2156 ∨ (¬ p2659) ∨ (¬ p2737) ∨ p2696 ∨ (¬ p2901) ∨ p2132 ∨ (¬ p5190))
    : (¬ p3051) ∨ p2685 ∨ p2563 ∨ p2132 ∨ p2696 ∨ p2651 ∨ (¬ p2528) ∨ (¬ p2901) ∨ (¬ p2659) ∨ p2156 ∨ (¬ p2655) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4558 := h105400;
    let u13 : p5190 := h105487;
    (Or.elim h103577 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u9 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u4 q10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u7))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (u3 q12))) (fun r12 => (False.elim (r12 u13)))))))))))))))))))))))))))))

theorem step125664 (p2190 p2363 p2528 p3146 p3323 p4384 p4564 : Prop)
    (h105401 : p4564)
    (h106167 : p4384)
    (h103582 : p3323 ∨ (¬ p2528) ∨ (¬ p3146) ∨ (¬ p4384) ∨ (¬ p2190) ∨ p2363 ∨ (¬ p4564))
    : (¬ p3146) ∨ (¬ p2528) ∨ (¬ p2190) ∨ p3323 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4564 := h105401;
    let u6 : p4384 := h106167;
    (Or.elim h103582 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step125666 (p2088 p2177 p2230 p2264 p2274 p2331 p2341 p2363 p2437 p2459 p2641 p2651 p2656 p2727 p2911 p2996 p3031 p3323 p3389 p3422 p3434 p4204 p4555 p4556 p4975 p4992 p5201 p5214 : Prop)
    (h105399 : p4556)
    (h105542 : p4555)
    (h105492 : p5214)
    (h105464 : p4975)
    (h103586 : (¬ p2088) ∨ (¬ p3434) ∨ (¬ p2656) ∨ (¬ p4556) ∨ (¬ p2177) ∨ (¬ p4555) ∨ (¬ p2363) ∨ (¬ p3422) ∨ (¬ p4204) ∨ p2274 ∨ (¬ p5214) ∨ (¬ p3389) ∨ (¬ p2459) ∨ (¬ p2641) ∨ (¬ p2230) ∨ p2727 ∨ p3323 ∨ (¬ p4992) ∨ (¬ p3031) ∨ (¬ p2264) ∨ (¬ p2341) ∨ (¬ p2996) ∨ (¬ p4975) ∨ (¬ p2437) ∨ (¬ p5201) ∨ p2651 ∨ (¬ p2911) ∨ (¬ p2331))
    : (¬ p3031) ∨ (¬ p2996) ∨ (¬ p4992) ∨ (¬ p2177) ∨ (¬ p2363) ∨ (¬ p2656) ∨ (¬ p3422) ∨ p2274 ∨ (¬ p4204) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p2088) ∨ (¬ p3434) ∨ p3323 ∨ (¬ p2641) ∨ (¬ p2230) ∨ (¬ p2341) ∨ (¬ p2264) ∨ (¬ p2437) ∨ (¬ p5201) ∨ p2651 ∨ p2727 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3031 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))))))))));
    let u24 : p4556 := h105399;
    let u25 : p4555 := h105542;
    let u26 : p5214 := h105492;
    let u27 : p4975 := h105464;
    (Or.elim h103586 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u24))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u25))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u7 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u26))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u9))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u15))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u16))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (u22 q15))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (u14 q16))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u2))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u0))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u18))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u17))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u1))) (fun r21 => (Or.elim r21 (fun q22 => (False.elim (q22 u27))) (fun r22 => (Or.elim r22 (fun q23 => (False.elim (q23 u19))) (fun r23 => (Or.elim r23 (fun q24 => (False.elim (q24 u20))) (fun r24 => (Or.elim r24 (fun q25 => (False.elim (u21 q25))) (fun r25 => (Or.elim r25 (fun q26 => (False.elim (q26 u10))) (fun r26 => (False.elim (r26 u23)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem step125671 (p2295 p2363 p3256 p4405 : Prop)
    (h105512 : p4405)
    (h103607 : (¬ p3256) ∨ p2363 ∨ (¬ p4405) ∨ p2295)
    : (¬ p3256) ∨ p2363 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4405 := h105512;
    (Or.elim h103607 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step125673 (p2352 p2363 p3146 p3958 : Prop)
    (h105378 : p3958)
    (h103615 : p2363 ∨ (¬ p3146) ∨ p2352 ∨ (¬ p3958))
    : (¬ p3146) ∨ p2352 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2352) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3958 := h105378;
    (Or.elim h103615 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125675 (p2241 p2608 p2630 p2651 p2750 : Prop)
    (h106345 : p2750)
    (h103629 : (¬ p2241) ∨ p2608 ∨ (¬ p2750) ∨ p2630 ∨ (¬ p2651))
    : p2630 ∨ (¬ p2651) ∨ (¬ p2241) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2750 := h106345;
    (Or.elim h103629 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step125676 (p2246 p2249 p2727 p2751 p2870 p2891 p3136 p3413 p4392 : Prop)
    (h106343 : p2751)
    (h106513 : p2249)
    (h103633 : (¬ p2246) ∨ p2870 ∨ (¬ p3413) ∨ (¬ p4392) ∨ p3136 ∨ (¬ p2891) ∨ (¬ p2727) ∨ (¬ p2249) ∨ (¬ p2751))
    : (¬ p4392) ∨ p2870 ∨ (¬ p2891) ∨ (¬ p2727) ∨ (¬ p2246) ∨ (¬ p3413) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4392 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2751 := h106343;
    let u8 : p2249 := h106513;
    (Or.elim h103633 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step125679 (p2132 p2166 p2696 p2737 p2753 p3156 p5052 : Prop)
    (h105473 : p5052)
    (h103642 : (¬ p2753) ∨ (¬ p2132) ∨ (¬ p5052) ∨ p3156 ∨ p2737 ∨ (¬ p2166) ∨ p2696)
    : (¬ p2166) ∨ (¬ p2132) ∨ p2737 ∨ p3156 ∨ (¬ p2753) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5052 := h105473;
    (Or.elim h103642 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (u5 r5)))))))))))))))

theorem step125680 (p2459 p2528 p3146 p3212 p4539 p4607 p4905 : Prop)
    (h105995 : p4905)
    (h105395 : p4539)
    (h103646 : (¬ p3212) ∨ (¬ p4905) ∨ (¬ p4539) ∨ (¬ p4607) ∨ p2528 ∨ (¬ p3146) ∨ p2459)
    : (¬ p3146) ∨ (¬ p4607) ∨ p2528 ∨ (¬ p3212) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4905 := h105995;
    let u6 : p4539 := h105395;
    (Or.elim h103646 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (u4 r5)))))))))))))))

theorem step125684 (p2331 p2641 p2727 p3379 p4975 : Prop)
    (h105464 : p4975)
    (h103665 : p2641 ∨ p3379 ∨ (¬ p2331) ∨ (¬ p4975) ∨ p2727)
    : p3379 ∨ p2727 ∨ p2641 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4975 := h105464;
    (Or.elim h103665 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step125685 (p2406 p2427 p2440 p2641 p2727 p2922 p4555 : Prop)
    (h105542 : p4555)
    (h103666 : (¬ p2641) ∨ (¬ p2406) ∨ p2427 ∨ p2440 ∨ p2727 ∨ (¬ p4555) ∨ p2922)
    : p2922 ∨ (¬ p2406) ∨ p2727 ∨ p2440 ∨ (¬ p2641) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4555 := h105542;
    (Or.elim h103666 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (u0 r5)))))))))))))))

theorem step125690 (p2255 p2341 p2807 p2996 p3527 p4104 : Prop)
    (h105367 : p2255)
    (h103686 : (¬ p2996) ∨ (¬ p2341) ∨ (¬ p4104) ∨ (¬ p2807) ∨ p3527 ∨ (¬ p2255))
    : p3527 ∨ (¬ p2996) ∨ (¬ p4104) ∨ (¬ p2341) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2255 := h105367;
    (Or.elim h103686 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step125695 (p2241 p2307 p2331 p2509 p2528 p2553 p2668 p2696 p2797 p2901 p3093 p4718 p4733 p4906 : Prop)
    (h105425 : p4718)
    (h105632 : p4906)
    (h105430 : p4733)
    (h103694 : p3093 ∨ (¬ p2509) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2528) ∨ (¬ p2901) ∨ p2241 ∨ (¬ p4718) ∨ p2331 ∨ (¬ p4906) ∨ (¬ p4733) ∨ p2307 ∨ (¬ p2553) ∨ p2797)
    : (¬ p2509) ∨ (¬ p2668) ∨ p2241 ∨ (¬ p2696) ∨ (¬ p2528) ∨ p2331 ∨ (¬ p2553) ∨ p3093 ∨ (¬ p2901) ∨ p2307 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4718 := h105425;
    let u12 : p4906 := h105632;
    let u13 : p4733 := h105430;
    (Or.elim h103694 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u13))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (u9 q11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u6))) (fun r12 => (False.elim (u10 r12)))))))))))))))))))))))))))))

theorem step125698 (p2255 p2406 p2440 p2651 : Prop)
    (h105367 : p2255)
    (h103701 : (¬ p2651) ∨ (¬ p2255) ∨ p2440 ∨ p2406)
    : p2440 ∨ (¬ p2651) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2255 := h105367;
    (Or.elim h103701 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step125702 (p2220 p2373 p2850 p4730 : Prop)
    (h106074 : p4730)
    (h103724 : (¬ p2220) ∨ p2373 ∨ (¬ p4730) ∨ p2850)
    : p2850 ∨ (¬ p2220) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4730 := h106074;
    (Or.elim h103724 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step125705 (p2264 p2341 p2528 p2911 p3246 p3363 p3367 p3389 p3461 p4140 p4327 p4712 p5197 : Prop)
    (h105422 : p4712)
    (h105381 : p4327)
    (h103729 : p3461 ∨ p2341 ∨ p2528 ∨ (¬ p3363) ∨ p2264 ∨ (¬ p4327) ∨ p3367 ∨ p3389 ∨ (¬ p5197) ∨ (¬ p4712) ∨ (¬ p2911) ∨ (¬ p4140) ∨ p3246)
    : (¬ p3363) ∨ (¬ p2911) ∨ p2528 ∨ p3367 ∨ (¬ p4140) ∨ p3389 ∨ (¬ p5197) ∨ p2341 ∨ p3461 ∨ p2264 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4712 := h105422;
    let u12 : p4327 := h105381;
    (Or.elim h103729 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u9 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u1))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u4))) (fun r11 => (False.elim (u10 r11)))))))))))))))))))))))))))

theorem step125715 (p2132 p2598 p2696 p2751 p2839 p2860 p3016 : Prop)
    (h106343 : p2751)
    (h103748 : (¬ p2839) ∨ p3016 ∨ (¬ p2132) ∨ p2860 ∨ (¬ p2696) ∨ p2598 ∨ (¬ p2751))
    : p2598 ∨ (¬ p2696) ∨ (¬ p2839) ∨ (¬ p2132) ∨ p2860 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2598) := (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2751 := h106343;
    (Or.elim h103748 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step125723 (p2241 p2573 p2750 p3016 p3379 p3541 : Prop)
    (h106345 : p2750)
    (h103765 : (¬ p2241) ∨ (¬ p3541) ∨ (¬ p3016) ∨ (¬ p2750) ∨ p2573 ∨ p3379)
    : p2573 ∨ p3379 ∨ (¬ p3016) ∨ (¬ p3541) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2750 := h106345;
    (Or.elim h103765 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (False.elim (u1 r4)))))))))))))

theorem step125728 (p2295 p2553 p2651 p2807 p4976 : Prop)
    (h105465 : p4976)
    (h103775 : (¬ p2295) ∨ p2553 ∨ (¬ p2807) ∨ p2651 ∨ (¬ p4976))
    : (¬ p2807) ∨ (¬ p2295) ∨ p2553 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4976 := h105465;
    (Or.elim h103775 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125730 (p2249 p2891 p2901 p2946 : Prop)
    (h106513 : p2249)
    (h103779 : p2901 ∨ p2946 ∨ (¬ p2249) ∨ (¬ p2891))
    : p2946 ∨ p2901 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2249 := h106513;
    (Or.elim h103779 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step125731 (p2352 p2383 p2493 p5194 : Prop)
    (h105489 : p5194)
    (h103781 : p2493 ∨ (¬ p2383) ∨ p2352 ∨ (¬ p5194))
    : p2493 ∨ (¬ p2383) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p5194 := h105489;
    (Or.elim h103781 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125732 (p2331 p2668 p2807 p4405 : Prop)
    (h105512 : p4405)
    (h103783 : (¬ p2331) ∨ (¬ p2668) ∨ (¬ p4405) ∨ p2807)
    : p2807 ∨ (¬ p2331) ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2807) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4405 := h105512;
    (Or.elim h103783 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step125733 (p2177 p2553 p2608 p3016 p3367 p4753 : Prop)
    (h105514 : p4753)
    (h103785 : p2608 ∨ p3367 ∨ p2553 ∨ p2177 ∨ p3016 ∨ (¬ p4753))
    : p3367 ∨ p2608 ∨ p2553 ∨ p2177 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3367) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4753 := h105514;
    (Or.elim h103785 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step125741 (p2230 p2241 p2363 p2440 p2459 p2532 p2563 p2651 p2950 p3063 p3073 p3093 p3319 p3461 p4198 p5046 p5118 p5119 : Prop)
    (h105482 : p5118)
    (h105472 : p5046)
    (h103816 : p3461 ∨ (¬ p5118) ∨ (¬ p2363) ∨ p2651 ∨ (¬ p2950) ∨ (¬ p5119) ∨ (¬ p2459) ∨ (¬ p3063) ∨ (¬ p2241) ∨ (¬ p3093) ∨ (¬ p3319) ∨ p2563 ∨ (¬ p5046) ∨ (¬ p4198) ∨ p2230 ∨ (¬ p2440) ∨ (¬ p2532) ∨ (¬ p3073))
    : (¬ p3063) ∨ (¬ p2440) ∨ p2563 ∨ p2230 ∨ (¬ p4198) ∨ (¬ p3073) ∨ (¬ p2459) ∨ (¬ p2950) ∨ (¬ p3093) ∨ p2651 ∨ (¬ p5119) ∨ (¬ p3319) ∨ (¬ p2241) ∨ (¬ p2363) ∨ p3461 ∨ (¬ p2532) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))));
    let u16 : p5118 := h105482;
    let u17 : p5046 := h105472;
    (Or.elim h103816 (fun q0 => (False.elim (u14 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u16))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u9 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (u2 q11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u17))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u4))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (u3 q14))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u1))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u15))) (fun r16 => (False.elim (r16 u5)))))))))))))))))))))))))))))))))))))

theorem step125747 (p2563 p2881 p2911 p4555 : Prop)
    (h105542 : p4555)
    (h69912 : p2911 ∨ (¬ p2881) ∨ (¬ p2563) ∨ (¬ p4555))
    : p2911 ∨ (¬ p2563) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4555 := h105542;
    (Or.elim h69912 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125749 (p2255 p2651 p2727 p2922 p2996 : Prop)
    (h105367 : p2255)
    (h103835 : p2727 ∨ (¬ p2255) ∨ (¬ p2651) ∨ p2922 ∨ p2996)
    : (¬ p2651) ∨ p2922 ∨ p2996 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2255 := h105367;
    (Or.elim h103835 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step125755 (p2295 p2427 p2553 p2901 p4702 : Prop)
    (h106079 : p4702)
    (h103849 : p2295 ∨ p2901 ∨ (¬ p4702) ∨ (¬ p2427) ∨ (¬ p2553))
    : p2901 ∨ (¬ p2553) ∨ p2295 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4702 := h106079;
    (Or.elim h103849 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step125757 (p2156 p2307 p2553 p2563 p3660 p4533 : Prop)
    (h105394 : p4533)
    (h103869 : p2307 ∨ p2156 ∨ (¬ p2553) ∨ (¬ p4533) ∨ (¬ p3660) ∨ (¬ p2563))
    : p2307 ∨ p2156 ∨ (¬ p2563) ∨ (¬ p2553) ∨ (¬ p3660) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4533 := h105394;
    (Or.elim h103869 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step125758 (p2363 p2373 p2563 p3146 p3696 p3697 p4533 : Prop)
    (h105394 : p4533)
    (h103870 : p2363 ∨ (¬ p3696) ∨ p2563 ∨ (¬ p4533) ∨ (¬ p2373) ∨ (¬ p3697) ∨ (¬ p3146))
    : (¬ p2373) ∨ (¬ p3697) ∨ p2363 ∨ (¬ p3146) ∨ p2563 ∨ (¬ p3696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4533 := h105394;
    (Or.elim h103870 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step125759 (p2210 p2241 p2253 p2651 p2741 p3412 p4377 : Prop)
    (h106170 : p4377)
    (h103874 : p2210 ∨ (¬ p3412) ∨ (¬ p4377) ∨ (¬ p2741) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2241))
    : (¬ p2741) ∨ p2210 ∨ (¬ p2241) ∨ (¬ p2253) ∨ (¬ p3412) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2741 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4377 := h106170;
    (Or.elim h103874 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step125760 (p2210 p2696 p2737 p4377 : Prop)
    (h106170 : p4377)
    (h103876 : p2737 ∨ p2210 ∨ (¬ p2696) ∨ (¬ p4377))
    : p2737 ∨ (¬ p2696) ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4377 := h106170;
    (Or.elim h103876 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125765 (p2192 p2745 p2860 p2992 p3136 : Prop)
    (h105523 : p2745)
    (h103883 : p2992 ∨ (¬ p2860) ∨ p2192 ∨ (¬ p3136) ∨ (¬ p2745))
    : (¬ p3136) ∨ p2992 ∨ (¬ p2860) ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    (Or.elim h103883 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125767 (p2230 p2274 p2437 p2440 p2553 p4718 : Prop)
    (h105425 : p4718)
    (h103889 : (¬ p2553) ∨ p2274 ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p4718) ∨ p2230)
    : (¬ p2437) ∨ (¬ p2553) ∨ (¬ p2440) ∨ p2230 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4718 := h105425;
    (Or.elim h103889 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step125770 (p2249 p2437 p2727 p2751 p3201 p4790 : Prop)
    (h106343 : p2751)
    (h106513 : p2249)
    (h106424 : p4790)
    (h69917 : (¬ p2437) ∨ (¬ p4790) ∨ (¬ p2751) ∨ (¬ p2727) ∨ (¬ p2249) ∨ p3201)
    : p3201 ∨ (¬ p2727) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2751 := h106343;
    let u4 : p2249 := h106513;
    let u5 : p4790 := h106424;
    (Or.elim h69917 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step125773 (p2177 p2249 p2437 p2470 p2727 p3083 p4276 : Prop)
    (h106513 : p2249)
    (h105516 : p4276)
    (h103899 : (¬ p2437) ∨ (¬ p2177) ∨ (¬ p2249) ∨ (¬ p2727) ∨ p3083 ∨ (¬ p4276) ∨ p2470)
    : p2470 ∨ p3083 ∨ (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2249 := h106513;
    let u6 : p4276 := h105516;
    (Or.elim h103899 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (u0 r5)))))))))))))))

theorem step125775 (p2437 p2608 p2630 p2745 p3389 : Prop)
    (h105523 : p2745)
    (h103903 : (¬ p2437) ∨ (¬ p2608) ∨ p3389 ∨ (¬ p2745) ∨ (¬ p2630))
    : (¬ p2630) ∨ p3389 ∨ (¬ p2437) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    (Or.elim h103903 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step125777 (p2396 p2417 p3063 p3093 p3631 p4405 : Prop)
    (h105512 : p4405)
    (h103914 : (¬ p3063) ∨ p3631 ∨ (¬ p3093) ∨ p2417 ∨ (¬ p2396) ∨ (¬ p4405))
    : (¬ p3063) ∨ p3631 ∨ p2417 ∨ (¬ p2396) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4405 := h105512;
    (Or.elim h103914 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step125786 (p2449 p2727 p3631 p4652 : Prop)
    (h105413 : p4652)
    (h103953 : (¬ p3631) ∨ p2449 ∨ p2727 ∨ (¬ p4652))
    : (¬ p3631) ∨ p2727 ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4652 := h105413;
    (Or.elim h103953 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125787 (p2437 p2440 p2449 p3246 p4644 : Prop)
    (h105411 : p4644)
    (h103955 : p2449 ∨ (¬ p3246) ∨ p2437 ∨ p2440 ∨ (¬ p4644))
    : p2437 ∨ (¬ p3246) ∨ p2449 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4644 := h105411;
    (Or.elim h103955 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125801 (p2331 p2901 p2946 p4555 : Prop)
    (h105542 : p4555)
    (h104004 : (¬ p2331) ∨ p2901 ∨ (¬ p4555) ∨ p2946)
    : p2946 ∨ p2901 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4555 := h105542;
    (Or.elim h104004 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step125802 (p2295 p2331 p3166 p4405 : Prop)
    (h105512 : p4405)
    (h104005 : p2331 ∨ (¬ p3166) ∨ (¬ p4405) ∨ p2295)
    : p2331 ∨ (¬ p3166) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4405 := h105512;
    (Or.elim h104005 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step125808 (p2797 p2946 p3105 p3136 p3986 p4790 p5043 : Prop)
    (h106424 : p4790)
    (h105471 : p5043)
    (h104020 : p3105 ∨ (¬ p5043) ∨ (¬ p3986) ∨ (¬ p4790) ∨ p3136 ∨ (¬ p2797) ∨ (¬ p2946))
    : p3136 ∨ (¬ p2797) ∨ p3105 ∨ (¬ p3986) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4790 := h106424;
    let u6 : p5043 := h105471;
    (Or.elim h104020 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step125816 (p2363 p2396 p2881 p3146 p4559 : Prop)
    (h105701 : p4559)
    (h104050 : p2363 ∨ (¬ p2881) ∨ (¬ p3146) ∨ p2396 ∨ (¬ p4559))
    : (¬ p3146) ∨ (¬ p2881) ∨ p2396 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4559 := h105701;
    (Or.elim h104050 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125819 (p2274 p2295 p2383 p2396 p2668 p4666 : Prop)
    (h105658 : p4666)
    (h104055 : p2295 ∨ (¬ p2668) ∨ p2396 ∨ p2274 ∨ (¬ p2383) ∨ (¬ p4666))
    : (¬ p2383) ∨ (¬ p2668) ∨ p2396 ∨ p2295 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4666 := h105658;
    (Or.elim h104055 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step125820 (p2241 p2396 p2440 p2563 p2651 p2881 p4555 p4666 : Prop)
    (h105542 : p4555)
    (h105658 : p4666)
    (h104056 : p2440 ∨ (¬ p2651) ∨ p2396 ∨ (¬ p4555) ∨ (¬ p4666) ∨ (¬ p2563) ∨ (¬ p2881) ∨ (¬ p2241))
    : (¬ p2651) ∨ p2440 ∨ p2396 ∨ (¬ p2563) ∨ (¬ p2881) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4555 := h105542;
    let u7 : p4666 := h105658;
    (Or.elim h104056 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step125825 (p2177 p2341 p2553 p2581 : Prop)
    (h105371 : p2581)
    (h104082 : p2341 ∨ (¬ p2553) ∨ (¬ p2581) ∨ (¬ p2177))
    : (¬ p2553) ∨ p2341 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2581 := h105371;
    (Or.elim h104082 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step125828 (p2274 p2553 p2881 p2911 p4718 p4973 : Prop)
    (h105425 : p4718)
    (h105835 : p4973)
    (h104091 : (¬ p2553) ∨ (¬ p2911) ∨ (¬ p4973) ∨ (¬ p4718) ∨ p2881 ∨ p2274)
    : (¬ p2553) ∨ p2881 ∨ p2274 ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4718 := h105425;
    let u5 : p4973 := h105835;
    (Or.elim h104091 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (u2 r4)))))))))))))

theorem step125829 (p2177 p2553 p2881 p4204 p4718 p4973 : Prop)
    (h105425 : p4718)
    (h105835 : p4973)
    (h104092 : (¬ p2553) ∨ (¬ p4204) ∨ (¬ p2177) ∨ p2881 ∨ (¬ p4973) ∨ (¬ p4718))
    : (¬ p2553) ∨ p2881 ∨ (¬ p2177) ∨ (¬ p4204) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4718 := h105425;
    let u5 : p4973 := h105835;
    (Or.elim h104092 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step125830 (p2363 p2459 p2881 p4556 : Prop)
    (h105399 : p4556)
    (h104093 : p2881 ∨ (¬ p4556) ∨ p2459 ∨ (¬ p2363))
    : p2881 ∨ p2459 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4556 := h105399;
    (Or.elim h104093 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step125831 (p2177 p2427 p2563 p2881 p4283 p4539 p4988 : Prop)
    (h105395 : p4539)
    (h104095 : (¬ p4988) ∨ (¬ p4283) ∨ (¬ p2177) ∨ p2427 ∨ (¬ p4539) ∨ p2881 ∨ (¬ p2563))
    : p2427 ∨ (¬ p2563) ∨ (¬ p4988) ∨ (¬ p2177) ∨ p2881 ∨ (¬ p4283) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4539 := h105395;
    (Or.elim h104095 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step125833 (p2563 p2881 p2911 p4558 : Prop)
    (h105400 : p4558)
    (h104100 : (¬ p2911) ∨ (¬ p4558) ∨ p2881 ∨ p2563)
    : (¬ p2911) ∨ p2563 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4558 := h105400;
    (Or.elim h104100 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step125834 (p2437 p2881 p2911 p3246 p3389 p4750 : Prop)
    (h105433 : p4750)
    (h104101 : (¬ p3246) ∨ (¬ p2911) ∨ (¬ p2437) ∨ p2881 ∨ (¬ p3389) ∨ (¬ p4750))
    : p2881 ∨ (¬ p3246) ∨ (¬ p3389) ∨ (¬ p2911) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4750 := h105433;
    (Or.elim h104101 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step125835 (p2427 p2717 p2881 p4533 p4882 : Prop)
    (h105453 : p4882)
    (h105394 : p4533)
    (h104103 : (¬ p2427) ∨ (¬ p2881) ∨ p2717 ∨ (¬ p4882) ∨ (¬ p4533))
    : p2717 ∨ (¬ p2427) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4882 := h105453;
    let u4 : p4533 := h105394;
    (Or.elim h104103 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125841 (p2177 p2807 p3166 p4361 : Prop)
    (h105382 : p4361)
    (h104113 : (¬ p3166) ∨ (¬ p4361) ∨ p2177 ∨ p2807)
    : (¬ p3166) ∨ p2807 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4361 := h105382;
    (Or.elim h104113 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step125842 (p2493 p2573 p2737 p3759 p4749 : Prop)
    (h105432 : p4749)
    (h70688 : p2493 ∨ (¬ p3759) ∨ (¬ p2573) ∨ (¬ p2737) ∨ (¬ p4749))
    : (¬ p2573) ∨ (¬ p2737) ∨ (¬ p3759) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4749 := h105432;
    (Or.elim h70688 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125862 (p2241 p2598 p2737 p3379 p4749 : Prop)
    (h105432 : p4749)
    (h104173 : (¬ p2737) ∨ (¬ p2241) ∨ p3379 ∨ p2598 ∨ (¬ p4749))
    : (¬ p2737) ∨ p2598 ∨ p3379 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4749 := h105432;
    (Or.elim h104173 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125877 (p2331 p2608 p2641 p2744 p2946 p4153 : Prop)
    (h106503 : p2744)
    (h104230 : (¬ p2641) ∨ p2331 ∨ p2946 ∨ (¬ p4153) ∨ (¬ p2744) ∨ (¬ p2608))
    : p2331 ∨ (¬ p4153) ∨ p2946 ∨ (¬ p2608) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2744 := h106503;
    (Or.elim h104230 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step125890 (p2341 p2608 p3527 p4793 : Prop)
    (h105438 : p4793)
    (h104279 : (¬ p3527) ∨ (¬ p2608) ∨ (¬ p4793) ∨ p2341)
    : p2341 ∨ (¬ p3527) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4793 := h105438;
    (Or.elim h104279 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u0 r2)))))))))

theorem step125894 (p2459 p2737 p2870 p2881 p2891 p5052 : Prop)
    (h105473 : p5052)
    (h104290 : p2870 ∨ p2737 ∨ (¬ p2891) ∨ p2459 ∨ (¬ p5052) ∨ p2881)
    : p2870 ∨ (¬ p2891) ∨ p2881 ∨ p2459 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5052 := h105473;
    (Or.elim h104290 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u2 r4)))))))))))))

theorem step125903 (p2241 p2331 p2528 p2641 p2911 p3389 p3399 p4116 p4778 p4975 p5214 : Prop)
    (h105464 : p4975)
    (h105492 : p5214)
    (h104355 : p3399 ∨ (¬ p2528) ∨ (¬ p2331) ∨ (¬ p5214) ∨ (¬ p4975) ∨ (¬ p4116) ∨ (¬ p4778) ∨ p2641 ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p2241))
    : p3399 ∨ (¬ p4116) ∨ (¬ p3389) ∨ (¬ p2528) ∨ (¬ p2911) ∨ (¬ p2241) ∨ p2641 ∨ (¬ p2331) ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4975 := h105464;
    let u10 : p5214 := h105492;
    (Or.elim h104355 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u5)))))))))))))))))))))))

theorem step125904 (p2241 p2331 p2741 p3379 p4116 p4975 : Prop)
    (h105464 : p4975)
    (h104356 : (¬ p2241) ∨ p3379 ∨ (¬ p4116) ∨ (¬ p2741) ∨ (¬ p2331) ∨ (¬ p4975))
    : (¬ p4116) ∨ p3379 ∨ (¬ p2741) ∨ (¬ p2331) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4975 := h105464;
    (Or.elim h104356 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step125906 (p2241 p2741 p2807 p3379 p4116 p4376 p4652 : Prop)
    (h105413 : p4652)
    (h106320 : p4376)
    (h104358 : (¬ p4116) ∨ (¬ p2741) ∨ p3379 ∨ (¬ p4652) ∨ (¬ p4376) ∨ (¬ p2807) ∨ (¬ p2241))
    : (¬ p4116) ∨ p3379 ∨ (¬ p2807) ∨ (¬ p2241) ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4652 := h105413;
    let u6 : p4376 := h106320;
    (Or.elim h104358 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step125911 (p2427 p2707 p2839 p3959 p4169 p4882 : Prop)
    (h105453 : p4882)
    (h104363 : p2707 ∨ (¬ p2839) ∨ (¬ p4882) ∨ (¬ p4169) ∨ (¬ p3959) ∨ (¬ p2427))
    : (¬ p3959) ∨ (¬ p2839) ∨ (¬ p2427) ∨ p2707 ∨ (¬ p4169) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3959 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4882 := h105453;
    (Or.elim h104363 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step125914 (p2284 p2563 p2630 p2641 p2696 p2881 p2891 p2911 p3136 p3361 p3579 p4117 p4241 p4555 : Prop)
    (h105542 : p4555)
    (h104373 : (¬ p2284) ∨ (¬ p2881) ∨ (¬ p4555) ∨ (¬ p3361) ∨ (¬ p4117) ∨ (¬ p2911) ∨ (¬ p2563) ∨ (¬ p2891) ∨ p2630 ∨ (¬ p4241) ∨ (¬ p2641) ∨ (¬ p3579) ∨ (¬ p3136) ∨ (¬ p2696))
    : (¬ p3136) ∨ (¬ p4117) ∨ (¬ p3579) ∨ (¬ p2881) ∨ (¬ p2563) ∨ (¬ p4241) ∨ p2630 ∨ (¬ p2696) ∨ (¬ p3361) ∨ (¬ p2911) ∨ (¬ p2641) ∨ (¬ p2284) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p4555 := h105542;
    (Or.elim h104373 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u6 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u2))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u0))) (fun r12 => (False.elim (r12 u7)))))))))))))))))))))))))))))

theorem step125923 (p2608 p2696 p3367 p3379 p4749 : Prop)
    (h105432 : p4749)
    (h104423 : p3379 ∨ (¬ p2608) ∨ p3367 ∨ (¬ p4749) ∨ (¬ p2696))
    : p3367 ∨ (¬ p2696) ∨ p3379 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3367) := (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4749 := h105432;
    (Or.elim h104423 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step125924 (p2132 p2241 p2608 p5052 : Prop)
    (h105473 : p5052)
    (h104424 : p2241 ∨ (¬ p2608) ∨ (¬ p2132) ∨ (¬ p5052))
    : (¬ p2132) ∨ p2241 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p5052 := h105473;
    (Or.elim h104424 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step125929 (p2187 p3093 p3449 p4518 : Prop)
    (h106113 : p4518)
    (h104446 : p3093 ∨ (¬ p3449) ∨ (¬ p4518) ∨ p2187)
    : p3093 ∨ (¬ p3449) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4518 := h106113;
    (Or.elim h104446 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step125935 (p2122 p2210 p2241 p2383 p2608 p2881 p2891 p2972 p3093 p3146 p4450 p4556 : Prop)
    (h105399 : p4556)
    (h104463 : p2241 ∨ p2383 ∨ p3146 ∨ (¬ p2608) ∨ (¬ p3093) ∨ (¬ p2210) ∨ (¬ p2972) ∨ p2881 ∨ (¬ p2891) ∨ (¬ p4556) ∨ p2122 ∨ (¬ p4450))
    : (¬ p2608) ∨ p2241 ∨ p3146 ∨ (¬ p2210) ∨ p2383 ∨ (¬ p2891) ∨ p2122 ∨ (¬ p2972) ∨ (¬ p3093) ∨ p2881 ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4556 := h105399;
    (Or.elim h104463 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u9 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u6 q10))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step125939 (p2284 p2331 p2563 p2651 p4705 : Prop)
    (h106238 : p4705)
    (h104485 : (¬ p2284) ∨ (¬ p2331) ∨ p2563 ∨ p2651 ∨ (¬ p4705))
    : p2651 ∨ (¬ p2284) ∨ (¬ p2331) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4705 := h106238;
    (Or.elim h104485 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125941 (p2751 p2870 p2901 p2996 p4333 p4906 : Prop)
    (h106343 : p2751)
    (h105632 : p4906)
    (h104489 : (¬ p2901) ∨ p2870 ∨ (¬ p4333) ∨ (¬ p4906) ∨ (¬ p2751) ∨ p2996)
    : p2870 ∨ (¬ p2901) ∨ (¬ p4333) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    let u5 : p4906 := h105632;
    (Or.elim h104489 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step125944 (p2177 p2437 p2481 p3083 p4276 p5203 : Prop)
    (h105516 : p4276)
    (h105490 : p5203)
    (h104494 : (¬ p2481) ∨ p3083 ∨ (¬ p2437) ∨ (¬ p5203) ∨ (¬ p2177) ∨ (¬ p4276))
    : (¬ p2481) ∨ p3083 ∨ (¬ p2177) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2481 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4276 := h105516;
    let u5 : p5203 := h105490;
    (Or.elim h104494 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step125946 (p2177 p2274 p3125 p4666 : Prop)
    (h105658 : p4666)
    (h104496 : (¬ p2274) ∨ p3125 ∨ (¬ p4666) ∨ (¬ p2177))
    : p3125 ∨ (¬ p2274) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4666 := h105658;
    (Or.elim h104496 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step125947 (p2177 p2470 p2518 p2651 p3083 p4276 : Prop)
    (h105516 : p4276)
    (h104497 : (¬ p2518) ∨ p2470 ∨ p2651 ∨ (¬ p2177) ∨ (¬ p4276) ∨ p3083)
    : p3083 ∨ (¬ p2518) ∨ p2651 ∨ (¬ p2177) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4276 := h105516;
    (Or.elim h104497 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step125948 (p2177 p2210 p2241 p2459 p2901 p2992 p4556 : Prop)
    (h105399 : p4556)
    (h70504 : (¬ p2901) ∨ (¬ p4556) ∨ (¬ p2177) ∨ (¬ p2459) ∨ (¬ p2210) ∨ (¬ p2992) ∨ (¬ p2241))
    : (¬ p2992) ∨ (¬ p2901) ∨ (¬ p2241) ∨ (¬ p2210) ∨ (¬ p2459) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4556 := h105399;
    (Or.elim h70504 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step125951 (p2177 p2274 p2440 p2459 p2553 p2581 p2598 p2608 p2651 p2781 p2982 p3063 p4236 p4514 p4736 p5059 : Prop)
    (h105431 : p4736)
    (h105371 : p2581)
    (h104500 : (¬ p4236) ∨ (¬ p4736) ∨ (¬ p2274) ∨ (¬ p2553) ∨ (¬ p5059) ∨ p2598 ∨ p3063 ∨ p2651 ∨ (¬ p2608) ∨ (¬ p2459) ∨ p2982 ∨ (¬ p2177) ∨ (¬ p2440) ∨ (¬ p4514) ∨ (¬ p2581) ∨ (¬ p2781))
    : (¬ p4236) ∨ p2651 ∨ p3063 ∨ p2598 ∨ (¬ p2553) ∨ (¬ p2274) ∨ (¬ p5059) ∨ (¬ p2459) ∨ (¬ p2440) ∨ (¬ p2177) ∨ (¬ p2608) ∨ p2982 ∨ (¬ p4514) ∨ (¬ p2781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3063) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : p4736 := h105431;
    let u15 : p2581 := h105371;
    (Or.elim h104500 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u11 q10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u9))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u8))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u12))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u15))) (fun r14 => (False.elim (r14 u13)))))))))))))))))))))))))))))))))

theorem step125952 (p2177 p2230 p2427 p2459 p2662 p2727 p3747 p4042 p4559 : Prop)
    (h105701 : p4559)
    (h104504 : (¬ p3747) ∨ p2727 ∨ p2459 ∨ (¬ p4042) ∨ p2427 ∨ (¬ p2662) ∨ p2230 ∨ (¬ p4559) ∨ p2177)
    : (¬ p2662) ∨ p2230 ∨ (¬ p4042) ∨ p2427 ∨ p2177 ∨ p2459 ∨ p2727 ∨ (¬ p3747) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2230) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4559 := h105701;
    (Or.elim h104504 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (u4 r7)))))))))))))))))))

theorem step125958 (p2230 p2295 p2373 p2696 p2797 p3146 p3917 p4419 p4604 : Prop)
    (h106293 : p4604)
    (h104525 : (¬ p3917) ∨ p2797 ∨ p2696 ∨ (¬ p4604) ∨ (¬ p4419) ∨ (¬ p3146) ∨ (¬ p2373) ∨ p2295 ∨ (¬ p2230))
    : p2797 ∨ (¬ p2230) ∨ (¬ p3917) ∨ p2696 ∨ (¬ p4419) ∨ p2295 ∨ (¬ p3146) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4604 := h106293;
    (Or.elim h104525 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step125960 (p2230 p2427 p2737 p2839 p2881 p3189 p3246 p3256 p3759 p3950 p4749 : Prop)
    (h105432 : p4749)
    (h104529 : (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3950) ∨ (¬ p3759) ∨ p3256 ∨ p2839 ∨ (¬ p2737) ∨ (¬ p4749) ∨ (¬ p3246) ∨ (¬ p2230) ∨ p3189)
    : (¬ p3246) ∨ (¬ p2427) ∨ (¬ p3759) ∨ (¬ p2737) ∨ p2839 ∨ p3189 ∨ p3256 ∨ (¬ p2230) ∨ (¬ p2881) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4749 := h105432;
    (Or.elim h104529 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (u5 r9)))))))))))))))))))))))

theorem step125961 (p2406 p2737 p2839 p2850 p4749 : Prop)
    (h105432 : p4749)
    (h104531 : (¬ p2737) ∨ p2839 ∨ p2406 ∨ (¬ p2850) ∨ (¬ p4749))
    : p2839 ∨ (¬ p2737) ∨ p2406 ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4749 := h105432;
    (Or.elim h104531 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step125967 (p2241 p2737 p3367 p3379 p4749 : Prop)
    (h105432 : p4749)
    (h104551 : (¬ p2737) ∨ p3379 ∨ (¬ p4749) ∨ (¬ p2241) ∨ p3367)
    : (¬ p2737) ∨ p3379 ∨ p3367 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4749 := h105432;
    (Or.elim h104551 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step125970 (p2230 p2241 p2406 p2608 p4749 : Prop)
    (h105432 : p4749)
    (h104556 : (¬ p2241) ∨ p2608 ∨ (¬ p4749) ∨ p2230 ∨ (¬ p2406))
    : (¬ p2406) ∨ (¬ p2241) ∨ p2608 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4749 := h105432;
    (Or.elim h104556 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step125971 (p2187 p2230 p2241 p2274 p2563 p2737 p2850 p4749 : Prop)
    (h105432 : p4749)
    (h70744 : (¬ p2850) ∨ (¬ p2737) ∨ (¬ p2230) ∨ (¬ p2241) ∨ (¬ p2563) ∨ (¬ p4749) ∨ (¬ p2187) ∨ (¬ p2274))
    : (¬ p2241) ∨ (¬ p2737) ∨ (¬ p2230) ∨ (¬ p2850) ∨ (¬ p2187) ∨ (¬ p2274) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4749 := h105432;
    (Or.elim h70744 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step125972 (p2241 p2252 p2608 p2750 p2774 p2819 p2946 p3146 p3156 p3906 p4318 p5580 : Prop)
    (h106345 : p2750)
    (h104557 : (¬ p4318) ∨ (¬ p2819) ∨ (¬ p3906) ∨ (¬ p2774) ∨ (¬ p2252) ∨ p2946 ∨ (¬ p2241) ∨ p3146 ∨ p2608 ∨ p5580 ∨ (¬ p2750) ∨ p3156)
    : (¬ p4318) ∨ p3156 ∨ p2946 ∨ p3146 ∨ (¬ p2774) ∨ (¬ p2241) ∨ (¬ p2819) ∨ p2608 ∨ (¬ p2252) ∨ (¬ p3906) ∨ p5580 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p5580) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2750 := h106345;
    (Or.elim h104557 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u10 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (False.elim (u1 r10)))))))))))))))))))))))))

theorem step125978 (p2156 p2187 p2210 p2241 p2363 p2563 p2608 p2744 p2946 p3641 p3990 p4697 p5160 : Prop)
    (h106503 : p2744)
    (h104566 : (¬ p5160) ∨ p2241 ∨ (¬ p2156) ∨ p2210 ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p2608) ∨ (¬ p2187) ∨ (¬ p3990) ∨ p3641 ∨ (¬ p2563) ∨ (¬ p2363) ∨ (¬ p4697))
    : (¬ p2608) ∨ (¬ p5160) ∨ (¬ p4697) ∨ (¬ p2156) ∨ p3641 ∨ (¬ p3990) ∨ (¬ p2187) ∨ (¬ p2946) ∨ p2241 ∨ p2210 ∨ (¬ p2363) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2744 := h106503;
    (Or.elim h104566 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u9 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u4 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u2)))))))))))))))))))))))))))

theorem step125979 (p2187 p2363 p2563 p3266 p4533 : Prop)
    (h105394 : p4533)
    (h70366 : (¬ p2563) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p4533) ∨ (¬ p3266))
    : (¬ p3266) ∨ (¬ p2363) ∨ (¬ p2187) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4533 := h105394;
    (Or.elim h70366 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step125981 (p2274 p2427 p2553 p2901 p4702 : Prop)
    (h106079 : p4702)
    (h104573 : (¬ p2553) ∨ p2274 ∨ p2901 ∨ (¬ p4702) ∨ (¬ p2427))
    : (¬ p2553) ∨ p2901 ∨ p2274 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4702 := h106079;
    (Or.elim h104573 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step125992 (p2248 p2331 p2608 p2737 p2829 : Prop)
    (h105365 : p2248)
    (h104613 : p2829 ∨ p2608 ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2737))
    : p2829 ∨ (¬ p2737) ∨ (¬ p2331) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2248 := h105365;
    (Or.elim h104613 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step125995 (p2406 p2493 p2573 p2891 p4203 p4555 : Prop)
    (h105542 : p4555)
    (h104620 : p2891 ∨ p2573 ∨ p2406 ∨ (¬ p2493) ∨ (¬ p4555) ∨ (¬ p4203))
    : p2891 ∨ (¬ p2493) ∨ p2406 ∨ p2573 ∨ (¬ p4203) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4555 := h105542;
    (Or.elim h104620 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step125996 (p2406 p2493 p2563 p2573 p2608 p3212 p5046 : Prop)
    (h105472 : p5046)
    (h104623 : (¬ p3212) ∨ (¬ p2406) ∨ p2573 ∨ (¬ p2608) ∨ p2493 ∨ (¬ p5046) ∨ p2563)
    : (¬ p3212) ∨ p2573 ∨ p2493 ∨ (¬ p2406) ∨ (¬ p2608) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5046 := h105472;
    (Or.elim h104623 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (u5 r5)))))))))))))))

theorem step125998 (p2255 p2807 p2891 p2901 p3368 p4957 : Prop)
    (h105367 : p2255)
    (h104630 : (¬ p2901) ∨ (¬ p4957) ∨ (¬ p2807) ∨ (¬ p2255) ∨ p2891 ∨ (¬ p3368))
    : p2891 ∨ (¬ p3368) ∨ (¬ p2807) ∨ (¬ p2901) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2255 := h105367;
    (Or.elim h104630 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step126021 (p2192 p2563 p2922 p4646 : Prop)
    (h105534 : p4646)
    (h104687 : (¬ p2922) ∨ p2192 ∨ (¬ p2563) ∨ (¬ p4646))
    : (¬ p2922) ∨ p2192 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4646 := h105534;
    (Or.elim h104687 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step126022 (p2210 p2274 p2563 p2911 p2922 p3379 p4646 : Prop)
    (h105534 : p4646)
    (h70346 : (¬ p3379) ∨ (¬ p4646) ∨ (¬ p2911) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p2210) ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (¬ p2911) ∨ (¬ p3379) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4646 := h105534;
    (Or.elim h70346 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step126047 (p2255 p2437 p2440 p2727 p3389 : Prop)
    (h105367 : p2255)
    (h104768 : (¬ p3389) ∨ p2437 ∨ p2727 ∨ (¬ p2440) ∨ (¬ p2255))
    : (¬ p3389) ∨ p2727 ∨ p2437 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2255 := h105367;
    (Or.elim h104768 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step126068 (p2284 p4322 p5043 p5284 : Prop)
    (h105471 : p5043)
    (h71160 : p4322 ∨ (¬ p5284) ∨ (¬ p5043) ∨ (¬ p2284))
    : p4322 ∨ (¬ p2284) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4322) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p5043 := h105471;
    (Or.elim h71160 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step126073 (p2156 p2284 p2982 p3506 p4322 p4705 : Prop)
    (h106238 : p4705)
    (h104840 : (¬ p2284) ∨ (¬ p4322) ∨ p2982 ∨ (¬ p3506) ∨ (¬ p4705) ∨ p2156)
    : (¬ p3506) ∨ p2982 ∨ (¬ p2284) ∨ p2156 ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    (Or.elim h104840 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step126079 (p2156 p2192 p2437 p2441 p2881 p2891 p2992 p3051 p3370 p4539 : Prop)
    (h105395 : p4539)
    (h104861 : (¬ p3051) ∨ p3370 ∨ (¬ p2992) ∨ (¬ p2437) ∨ (¬ p4539) ∨ (¬ p2156) ∨ p2192 ∨ p2891 ∨ (¬ p2441) ∨ (¬ p2881))
    : p3370 ∨ (¬ p3051) ∨ (¬ p2441) ∨ (¬ p2881) ∨ (¬ p2437) ∨ p2192 ∨ (¬ p2992) ∨ p2891 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3370) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4539 := h105395;
    (Or.elim h104861 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step126082 (p2230 p2252 p2295 p2331 p2363 p2396 p2598 p2668 p2750 p2753 p2982 p3362 p3422 p4322 p4332 p4395 p4450 p4789 : Prop)
    (h106345 : p2750)
    (h105646 : p4789)
    (h104873 : (¬ p4322) ∨ (¬ p4332) ∨ p2363 ∨ (¬ p3422) ∨ p2668 ∨ (¬ p2230) ∨ (¬ p2753) ∨ (¬ p2252) ∨ p2396 ∨ (¬ p2598) ∨ (¬ p4450) ∨ (¬ p4395) ∨ (¬ p3362) ∨ (¬ p2750) ∨ (¬ p2982) ∨ (¬ p4789) ∨ p2331 ∨ p2295)
    : p2331 ∨ (¬ p3422) ∨ (¬ p2753) ∨ (¬ p2230) ∨ p2363 ∨ (¬ p2598) ∨ p2295 ∨ p2668 ∨ (¬ p2982) ∨ p2396 ∨ (¬ p2252) ∨ (¬ p4322) ∨ (¬ p3362) ∨ (¬ p4450) ∨ (¬ p4395) ∨ (¬ p4332) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))));
    let u16 : p2750 := h106345;
    let u17 : p4789 := h105646;
    (Or.elim h104873 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u15))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u9 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u13))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u14))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u12))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u16))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u8))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u17))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (u0 q16))) (fun r16 => (False.elim (u6 r16)))))))))))))))))))))))))))))))))))))

theorem step126097 (p2563 p2982 p3564 p3660 p4192 p4555 : Prop)
    (h105542 : p4555)
    (h104920 : (¬ p3564) ∨ p2982 ∨ (¬ p4555) ∨ (¬ p4192) ∨ (¬ p2563) ∨ (¬ p3660))
    : (¬ p4192) ∨ (¬ p3564) ∨ (¬ p2563) ∨ (¬ p3660) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4555 := h105542;
    (Or.elim h104920 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step126098 (p2829 p3016 p3367 p4750 : Prop)
    (h105433 : p4750)
    (h72733 : p2829 ∨ (¬ p3367) ∨ (¬ p4750) ∨ (¬ p3016))
    : (¬ p3367) ∨ p2829 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4750 := h105433;
    (Or.elim h72733 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

end ElevenRUP
