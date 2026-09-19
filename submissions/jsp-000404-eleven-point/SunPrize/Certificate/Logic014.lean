import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step52832 (p2027 p2156 p2246 p2476 p2744 p2901 p2958 p3366 p3641 p3876 p3905 p3952 p4647 : Prop)
    (h40810 : (¬ p2027))
    (h26204 : p2027 ∨ (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2476) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2958) ∨ (¬ p3366) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p3952) ∨ (¬ p4647))
    : (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2476) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2958) ∨ (¬ p3366) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p3952) ∨ (¬ p4647) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h26204 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step52833 (p2027 p2246 p2744 p2901 p2946 p3055 p3246 p3366 p3644 p3876 p4668 : Prop)
    (h40810 : (¬ p2027))
    (h26205 : p2027 ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4668))
    : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26205 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52836 (p2027 p2156 p2246 p2744 p2958 p3156 p3201 p3366 p3540 p3874 p3905 p3952 p4434 : Prop)
    (h40810 : (¬ p2027))
    (h26208 : p2027 ∨ (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3156) ∨ (¬ p3201) ∨ (¬ p3366) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p3952) ∨ (¬ p4434))
    : (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3156) ∨ (¬ p3201) ∨ (¬ p3366) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p3952) ∨ (¬ p4434) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h26208 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step52837 (p2027 p2088 p3570 p4348 p4590 p4990 : Prop)
    (h40810 : (¬ p2027))
    (h26209 : p2027 ∨ (¬ p2088) ∨ (¬ p3570) ∨ (¬ p4348) ∨ (¬ p4590) ∨ (¬ p4990))
    : (¬ p2088) ∨ (¬ p3570) ∨ (¬ p4348) ∨ (¬ p4590) ∨ (¬ p4990) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26209 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step52838 (p2027 p2246 p2274 p2284 p2476 p2744 p2946 p3347 p3641 p3876 p4257 p4712 : Prop)
    (h40810 : (¬ p2027))
    (h26210 : p2027 ∨ (¬ p2246) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2476) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3347) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4257) ∨ (¬ p4712))
    : (¬ p2246) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2476) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3347) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4257) ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h26210 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step52841 (p2027 p2246 p2579 p2744 p3166 p3366 p3506 p3822 p3905 p4107 p4390 p4444 p4669 p5111 : Prop)
    (h40810 : (¬ p2027))
    (h26213 : p2027 ∨ (¬ p2246) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3366) ∨ (¬ p3506) ∨ (¬ p3822) ∨ (¬ p3905) ∨ (¬ p4107) ∨ (¬ p4390) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p5111))
    : (¬ p2246) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3366) ∨ (¬ p3506) ∨ (¬ p3822) ∨ (¬ p3905) ∨ (¬ p4107) ∨ (¬ p4390) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p5111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p5111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : (¬ p2027) := h40810;
    (Or.elim h26213 (fun q0 => (False.elim (u13 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u11))) (fun r12 => (False.elim (r12 u12)))))))))))))))))))))))))))))

theorem step52842 (p2027 p2247 p2307 p2497 p2744 p3549 p4257 p5020 : Prop)
    (h40810 : (¬ p2027))
    (h26214 : p2027 ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2497) ∨ (¬ p2744) ∨ (¬ p3549) ∨ (¬ p4257) ∨ (¬ p5020))
    : (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2497) ∨ (¬ p2744) ∨ (¬ p3549) ∨ (¬ p4257) ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h26214 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step52851 (p2027 p2264 p2476 p3389 p4383 p4653 : Prop)
    (h40810 : (¬ p2027))
    (h26223 : p2027 ∨ (¬ p2264) ∨ (¬ p2476) ∨ (¬ p3389) ∨ (¬ p4383) ∨ (¬ p4653))
    : (¬ p2264) ∨ (¬ p2476) ∨ (¬ p3389) ∨ (¬ p4383) ∨ (¬ p4653) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26223 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step52852 (p2027 p2139 p2156 p2177 p2274 p2630 p2657 p3877 p4041 p4236 : Prop)
    (h40810 : (¬ p2027))
    (h26224 : p2027 ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4236))
    : (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2139 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26224 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step52856 (p2027 p2685 p3276 p3355 p3366 p3414 p3519 p4035 p4236 p4376 p4444 p5113 : Prop)
    (h40810 : (¬ p2027))
    (h26229 : p2027 ∨ (¬ p2685) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p5113))
    : (¬ p2685) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p5113) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h26229 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step52857 (p1982 p2027 p2459 p2622 p2881 p2951 p3051 p3136 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h26230 : (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ p2622 ∨ (¬ p2881) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3136))
    : (¬ p2459) ∨ (¬ p2881) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h26230 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step52860 (p2027 p2481 p2509 p2717 p2922 p3960 p5087 : Prop)
    (h40810 : (¬ p2027))
    (h26233 : p2027 ∨ (¬ p2481) ∨ (¬ p2509) ∨ (¬ p2717) ∨ (¬ p2922) ∨ (¬ p3960) ∨ (¬ p5087))
    : (¬ p2481) ∨ (¬ p2509) ∨ (¬ p2717) ∨ (¬ p2922) ∨ (¬ p3960) ∨ (¬ p5087) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2481 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5087 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26233 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step52865 (p1994 p2027 p2190 p2202 p2563 p2727 p3497 p3662 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h26241 : (¬ p1994) ∨ p2027 ∨ (¬ p2190) ∨ p2202 ∨ (¬ p2563) ∨ (¬ p2727) ∨ (¬ p3497) ∨ (¬ p3662))
    : (¬ p2190) ∨ (¬ p2563) ∨ (¬ p2727) ∨ (¬ p3497) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h26241 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step52866 (p1994 p2027 p2148 p2220 p2727 p3497 p3662 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h26242 : (¬ p1994) ∨ p2027 ∨ p2148 ∨ (¬ p2220) ∨ (¬ p2727) ∨ (¬ p3497) ∨ (¬ p3662))
    : (¬ p2220) ∨ (¬ p2727) ∨ (¬ p3497) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2148) := h40865;
    (Or.elim h26242 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step52868 (p1994 p2027 p2202 p2373 p2727 p3497 p3662 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h26244 : (¬ p1994) ∨ p2027 ∨ p2202 ∨ (¬ p2373) ∨ (¬ p2727) ∨ (¬ p3497) ∨ (¬ p3662))
    : (¬ p2373) ∨ (¬ p2727) ∨ (¬ p3497) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h26244 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step52869 (p2027 p2246 p2528 p2608 p2651 p2744 p3083 p3817 p4366 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h26245 : p2027 ∨ (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669))
    : (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26245 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step52873 (p2027 p2122 p2246 p2313 p2528 p2651 p2744 p2778 p3083 p3366 p3917 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h26249 : p2027 ∨ (¬ p2122) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3917) ∨ (¬ p4604))
    : (¬ p2122) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3917) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h26249 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step52874 (p2027 p2246 p2528 p2651 p2744 p2780 p3083 p3366 p3822 p4107 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h26250 : p2027 ∨ (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4669))
    : (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26250 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52876 (p2027 p2177 p2311 p2386 p3551 p3564 p4624 : Prop)
    (h40810 : (¬ p2027))
    (h26252 : p2027 ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2386) ∨ (¬ p3551) ∨ (¬ p3564) ∨ (¬ p4624))
    : (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2386) ∨ (¬ p3551) ∨ (¬ p3564) ∨ (¬ p4624) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26252 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step52877 (p2027 p2246 p2264 p2459 p2744 p2807 p3379 p3860 p4257 p5118 p5693 : Prop)
    (h40810 : (¬ p2027))
    (h26253 : p2027 ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4257) ∨ (¬ p5118) ∨ (¬ p5693))
    : (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4257) ∨ (¬ p5118) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26253 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52878 (p1982 p2027 p2363 p2774 p2819 p2842 p3055 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h26255 : (¬ p1982) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ p2842 ∨ (¬ p3055))
    : (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3055) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2842) := h40885;
    (Or.elim h26255 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step52881 (p2027 p2295 p2774 p3425 p4471 p4843 : Prop)
    (h40810 : (¬ p2027))
    (h26258 : p2027 ∨ (¬ p2295) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p4471) ∨ (¬ p4843))
    : (¬ p2295) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p4471) ∨ (¬ p4843) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4843 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26258 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step52883 (p2027 p2870 p3516 p3691 p3694 p4132 p4668 : Prop)
    (h40810 : (¬ p2027))
    (h26262 : p2027 ∨ (¬ p2870) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p3694) ∨ (¬ p4132) ∨ (¬ p4668))
    : (¬ p2870) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p3694) ∨ (¬ p4132) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26262 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step52884 (p2027 p2246 p2651 p2744 p2780 p3276 p3343 p3366 p3822 p4260 p4831 : Prop)
    (h40810 : (¬ p2027))
    (h26263 : p2027 ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p4260) ∨ (¬ p4831))
    : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p4260) ∨ (¬ p4831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26263 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52889 (p2027 p2136 p2247 p2459 p2744 p3063 p3093 p3366 p3692 p4120 p4133 : Prop)
    (h40810 : (¬ p2027))
    (h26268 : p2027 ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4133))
    : (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26268 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52891 (p2027 p2136 p2246 p2331 p2363 p2668 p2744 p2870 p3366 p3556 p4385 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h26271 : p2027 ∨ (¬ p2136) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p2870) ∨ (¬ p3366) ∨ (¬ p3556) ∨ (¬ p4385) ∨ (¬ p5059))
    : (¬ p2136) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p2870) ∨ (¬ p3366) ∨ (¬ p3556) ∨ (¬ p4385) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h26271 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step52896 (p2027 p2138 p2246 p2331 p2668 p2744 p3366 p3979 p4322 p4385 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h26276 : p2027 ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3979) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p5119))
    : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3979) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26276 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52897 (p2027 p2246 p2608 p2744 p3166 p3256 p3266 p4366 p4442 p4831 : Prop)
    (h40810 : (¬ p2027))
    (h26277 : p2027 ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p4366) ∨ (¬ p4442) ∨ (¬ p4831))
    : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p4366) ∨ (¬ p4442) ∨ (¬ p4831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26277 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step52902 (p2027 p2138 p2246 p2470 p2663 p2744 p3343 p3366 p3690 p4244 p4256 p4638 : Prop)
    (h40810 : (¬ p2027))
    (h26282 : p2027 ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4256) ∨ (¬ p4638))
    : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4256) ∨ (¬ p4638) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h26282 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step52903 (p2027 p2138 p2246 p2744 p3166 p3256 p3266 p3366 p4244 p4831 p5660 : Prop)
    (h40810 : (¬ p2027))
    (h26283 : p2027 ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p4244) ∨ (¬ p4831) ∨ (¬ p5660))
    : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p4244) ∨ (¬ p4831) ∨ (¬ p5660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26283 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52906 (p2027 p2246 p2528 p2651 p2744 p3083 p3461 p3645 p4032 p4322 p4604 p4874 : Prop)
    (h40810 : (¬ p2027))
    (h26286 : p2027 ∨ (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3461) ∨ (¬ p3645) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4604) ∨ (¬ p4874))
    : (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3461) ∨ (¬ p3645) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4604) ∨ (¬ p4874) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h26286 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step52907 (p2027 p2138 p2247 p2744 p3083 p3366 p3379 p3487 p3570 p4244 p4420 : Prop)
    (h40810 : (¬ p2027))
    (h26288 : p2027 ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4420))
    : (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4420) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26288 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52908 (p2027 p2247 p2744 p3055 p3073 p3366 p3449 p3584 p4137 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h26289 : p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604))
    : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26289 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step52913 (p2027 p2608 p2761 p3346 p3537 p3609 p4425 p4669 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h26295 : p2027 ∨ (¬ p2608) ∨ (¬ p2761) ∨ (¬ p3346) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p4425) ∨ (¬ p4669) ∨ (¬ p5193))
    : (¬ p2608) ∨ (¬ p2761) ∨ (¬ p3346) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p4425) ∨ (¬ p4669) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26295 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step52915 (p2027 p2437 p2563 p3952 p4646 p4700 : Prop)
    (h40810 : (¬ p2027))
    (h26299 : p2027 ∨ (¬ p2437) ∨ (¬ p2563) ∨ (¬ p3952) ∨ (¬ p4646) ∨ (¬ p4700))
    : (¬ p2437) ∨ (¬ p2563) ∨ (¬ p3952) ∨ (¬ p4646) ∨ (¬ p4700) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26299 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step52916 (p2027 p2122 p2230 p2440 p3016 p3549 p3591 p5190 p5225 : Prop)
    (h40810 : (¬ p2027))
    (h26300 : p2027 ∨ (¬ p2122) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p5190) ∨ (¬ p5225))
    : (¬ p2122) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p5190) ∨ (¬ p5225) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26300 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step52919 (p2027 p2406 p2563 p2928 p4001 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h26307 : p2027 ∨ (¬ p2406) ∨ (¬ p2563) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4555))
    : (¬ p2406) ∨ (¬ p2563) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26307 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step52920 (p2027 p2246 p2579 p2749 p2807 p3347 p3572 p3755 p3956 p4347 p5109 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h26308 : p2027 ∨ (¬ p2246) ∨ (¬ p2579) ∨ (¬ p2749) ∨ (¬ p2807) ∨ (¬ p3347) ∨ (¬ p3572) ∨ (¬ p3755) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p5109) ∨ (¬ p5216))
    : (¬ p2246) ∨ (¬ p2579) ∨ (¬ p2749) ∨ (¬ p2807) ∨ (¬ p3347) ∨ (¬ p3572) ∨ (¬ p3755) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p5109) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h26308 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step52921 (p2027 p2387 p2577 p2662 p3063 p3662 p4701 p4759 : Prop)
    (h40810 : (¬ p2027))
    (h26309 : p2027 ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p3662) ∨ (¬ p4701) ∨ (¬ p4759))
    : (¬ p2387) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p3662) ∨ (¬ p4701) ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4701 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h26309 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step52922 (p2027 p2493 p3238 p3952 p4203 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h26311 : p2027 ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3952) ∨ (¬ p4203) ∨ (¬ p4702))
    : (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3952) ∨ (¬ p4203) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26311 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step52923 (p2027 p2498 p2588 p3591 p3830 p4624 p5152 : Prop)
    (h40810 : (¬ p2027))
    (h26312 : p2027 ∨ (¬ p2498) ∨ (¬ p2588) ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p4624) ∨ (¬ p5152))
    : (¬ p2498) ∨ (¬ p2588) ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p4624) ∨ (¬ p5152) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2498 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26312 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step52925 (p2027 p2246 p2449 p2579 p2744 p2761 p2807 p3347 p3956 p4257 p5123 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h26314 : p2027 ∨ (¬ p2246) ∨ (¬ p2449) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3347) ∨ (¬ p3956) ∨ (¬ p4257) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p2246) ∨ (¬ p2449) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3347) ∨ (¬ p3956) ∨ (¬ p4257) ∨ (¬ p5123) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h26314 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step52928 (p2027 p2246 p2744 p2901 p2946 p3055 p3246 p3366 p3584 p4137 p4625 : Prop)
    (h40810 : (¬ p2027))
    (h26317 : p2027 ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4625))
    : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4625) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26317 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52932 (p1998 p2027 p2210 p2247 p2688 p2881 p2891 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h26321 : (¬ p1998) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2247) ∨ p2688 ∨ (¬ p2881) ∨ (¬ p2891))
    : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2881) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h26321 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step52952 (p1994 p2027 p2578 p2667 p2727 p2764 p4137 p4154 p4191 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h26345 : (¬ p1994) ∨ p2027 ∨ (¬ p2578) ∨ (¬ p2667) ∨ (¬ p2727) ∨ p2764 ∨ (¬ p4137) ∨ (¬ p4154) ∨ (¬ p4191))
    : (¬ p2578) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p4137) ∨ (¬ p4154) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2578 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1994 := h2154;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2764) := h40882;
    (Or.elim h26345 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step52955 (p2027 p2972 p3486 p3570 p4135 p4668 : Prop)
    (h40810 : (¬ p2027))
    (h26348 : p2027 ∨ (¬ p2972) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4135) ∨ (¬ p4668))
    : (¬ p2972) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4135) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26348 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step52958 (p1982 p2027 p2363 p2622 p2774 p2819 p3365 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h26352 : (¬ p1982) ∨ p2027 ∨ (¬ p2363) ∨ p2622 ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3365))
    : (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3365) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h26352 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step52961 (p2027 p2136 p2246 p2363 p2663 p2744 p3083 p3366 p3389 p3646 p3692 p3742 p3988 p4596 : Prop)
    (h40810 : (¬ p2027))
    (h26355 : p2027 ∨ (¬ p2136) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3389) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p3742) ∨ (¬ p3988) ∨ (¬ p4596))
    : (¬ p2136) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3389) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p3742) ∨ (¬ p3988) ∨ (¬ p4596) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : (¬ p2027) := h40810;
    (Or.elim h26355 (fun q0 => (False.elim (u13 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u11))) (fun r12 => (False.elim (r12 u12)))))))))))))))))))))))))))))

theorem step52963 (p2027 p2138 p2247 p2744 p3366 p3399 p3527 p3690 p4244 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h26357 : p2027 ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4666))
    : (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26357 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step52964 (p2027 p2427 p3246 p3947 p4386 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h26358 : p2027 ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4702))
    : (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26358 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step52965 (p2027 p2427 p3516 p3691 p3947 p4386 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h26359 : p2027 ∨ (¬ p2427) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4702))
    : (¬ p2427) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26359 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step52966 (p2027 p2210 p2247 p2744 p2972 p3366 p3425 p3659 p4348 p4450 : Prop)
    (h40810 : (¬ p2027))
    (h26360 : p2027 ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2972) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4450))
    : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2972) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26360 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step52967 (p2027 p2579 p2588 p3449 p3707 p4107 p4351 p4444 p4669 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h26361 : p2027 ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3449) ∨ (¬ p3707) ∨ (¬ p4107) ∨ (¬ p4351) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p5193))
    : (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3449) ∨ (¬ p3707) ∨ (¬ p4107) ∨ (¬ p4351) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4351 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26361 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step52969 (p2027 p2246 p2449 p2608 p2744 p2761 p2807 p3860 p4353 p5123 p5612 : Prop)
    (h40810 : (¬ p2027))
    (h26363 : p2027 ∨ (¬ p2246) ∨ (¬ p2449) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3860) ∨ (¬ p4353) ∨ (¬ p5123) ∨ (¬ p5612))
    : (¬ p2246) ∨ (¬ p2449) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3860) ∨ (¬ p4353) ∨ (¬ p5123) ∨ (¬ p5612) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4353 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5612 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26363 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52970 (p2027 p2246 p2264 p2608 p2744 p2807 p3860 p3941 p4261 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h26364 : p2027 ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3860) ∨ (¬ p3941) ∨ (¬ p4261) ∨ (¬ p5122))
    : (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3860) ∨ (¬ p3941) ∨ (¬ p4261) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26364 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step52972 (p2027 p2246 p2542 p2651 p2744 p2982 p3366 p3425 p3659 p4348 p4450 : Prop)
    (h40810 : (¬ p2027))
    (h26366 : p2027 ∨ (¬ p2246) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2982) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4450))
    : (¬ p2246) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2982) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26366 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52974 (p2027 p2247 p2744 p3366 p3425 p3449 p3659 p3969 p4348 p4446 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h26368 : p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3449) ∨ (¬ p3659) ∨ (¬ p3969) ∨ (¬ p4348) ∨ (¬ p4446) ∨ (¬ p5122))
    : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3449) ∨ (¬ p3659) ∨ (¬ p3969) ∨ (¬ p4348) ∨ (¬ p4446) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4446 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26368 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52978 (p2027 p2246 p2608 p2744 p2881 p2901 p2946 p3817 p4366 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h26372 : p2027 ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4666))
    : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26372 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step52979 (p2027 p2247 p2744 p2780 p3366 p3399 p3527 p3822 p4107 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h26373 : p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4666))
    : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26373 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step52980 (p1995 p2027 p2764 p3238 p3556 p3690 p4031 p4381 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h26374 : (¬ p1995) ∨ p2027 ∨ p2764 ∨ (¬ p3238) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p4031) ∨ (¬ p4381))
    : (¬ p3238) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p4031) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3238 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h26374 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step52981 (p2027 p2307 p2630 p3567 p3822 p4841 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h26375 : p2027 ∨ (¬ p2307) ∨ (¬ p2630) ∨ (¬ p3567) ∨ (¬ p3822) ∨ (¬ p4841) ∨ (¬ p4972))
    : (¬ p2307) ∨ (¬ p2630) ∨ (¬ p3567) ∨ (¬ p3822) ∨ (¬ p4841) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26375 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step52982 (p2027 p2651 p2952 p2992 p4154 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h26377 : p2027 ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4154) ∨ (¬ p4972))
    : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4154) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26377 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step52983 (p2027 p2247 p2744 p3093 p3323 p3366 p3425 p3659 p3922 p4330 p4348 : Prop)
    (h40810 : (¬ p2027))
    (h26378 : p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3093) ∨ (¬ p3323) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3922) ∨ (¬ p4330) ∨ (¬ p4348))
    : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3093) ∨ (¬ p3323) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3922) ∨ (¬ p4330) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26378 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step52997 (p2027 p2246 p2363 p2383 p2744 p3055 p3366 p3684 p3880 p3987 p4348 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h26392 : p2027 ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p3987) ∨ (¬ p4348) ∨ (¬ p4905))
    : (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p3987) ∨ (¬ p4348) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h26392 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step52998 (p2027 p2247 p2476 p2534 p2744 p3063 p3093 p3146 p3366 p3905 p4134 : Prop)
    (h40810 : (¬ p2027))
    (h26393 : p2027 ∨ (¬ p2247) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p4134))
    : (¬ p2247) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p4134) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26393 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53001 (p2027 p2630 p2807 p3292 p3572 p5172 : Prop)
    (h40810 : (¬ p2027))
    (h26396 : p2027 ∨ (¬ p2630) ∨ (¬ p2807) ∨ (¬ p3292) ∨ (¬ p3572) ∨ (¬ p5172))
    : (¬ p2630) ∨ (¬ p2807) ∨ (¬ p3292) ∨ (¬ p3572) ∨ (¬ p5172) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26396 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53008 (p2027 p2247 p2744 p3471 p3588 p3589 : Prop)
    (h40810 : (¬ p2027))
    (h26406 : p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3471) ∨ (¬ p3588) ∨ (¬ p3589))
    : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3471) ∨ (¬ p3588) ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26406 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53009 (p2027 p2248 p2651 p3016 p3548 p3564 p4330 p4348 p4366 : Prop)
    (h40810 : (¬ p2027))
    (h26407 : p2027 ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3548) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4366))
    : (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3548) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26407 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53011 (p2027 p2475 p2499 p2518 p3324 p4113 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h26409 : p2027 ∨ (¬ p2475) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p3324) ∨ (¬ p4113) ∨ (¬ p4973))
    : (¬ p2475) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p3324) ∨ (¬ p4113) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2475 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26409 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53012 (p1998 p2027 p2177 p2295 p2622 p2743 p2829 p4328 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h26410 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2295) ∨ p2622 ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p4328))
    : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p4328) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h26410 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53013 (p1998 p2027 p2177 p2295 p2622 p2743 p2753 p2774 p4328 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h26411 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2295) ∨ p2622 ∨ (¬ p2743) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p4328))
    : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2743) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p4328) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1998 := h2158;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2622) := h40878;
    (Or.elim h26411 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53015 (p1981 p2027 p2122 p2611 p2668 p2774 p3568 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h26413 : (¬ p1981) ∨ p2027 ∨ (¬ p2122) ∨ p2611 ∨ (¬ p2668) ∨ (¬ p2774) ∨ (¬ p3568))
    : (¬ p2122) ∨ (¬ p2668) ∨ (¬ p2774) ∨ (¬ p3568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h26413 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53017 (p2027 p2192 p2241 p2750 p3369 p3371 p3646 : Prop)
    (h40810 : (¬ p2027))
    (h26416 : p2027 ∨ (¬ p2192) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3369) ∨ (¬ p3371) ∨ (¬ p3646))
    : (¬ p2192) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3369) ∨ (¬ p3371) ∨ (¬ p3646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26416 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53020 (p2027 p2437 p2911 p3359 p4636 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h26419 : p2027 ∨ (¬ p2437) ∨ (¬ p2911) ∨ (¬ p3359) ∨ (¬ p4636) ∨ (¬ p4666))
    : (¬ p2437) ∨ (¬ p2911) ∨ (¬ p3359) ∨ (¬ p4636) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53023 (p2005 p2027 p2766 p3266 p3422 p4425 p5160 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h26424 : (¬ p2005) ∨ p2027 ∨ p2766 ∨ (¬ p3266) ∨ (¬ p3422) ∨ (¬ p4425) ∨ (¬ p5160))
    : (¬ p3266) ∨ (¬ p3422) ∨ (¬ p4425) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h26424 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53026 (p2027 p2313 p3309 p3361 p3585 p3983 p4749 p4869 : Prop)
    (h40810 : (¬ p2027))
    (h26427 : p2027 ∨ (¬ p2313) ∨ (¬ p3309) ∨ (¬ p3361) ∨ (¬ p3585) ∨ (¬ p3983) ∨ (¬ p4749) ∨ (¬ p4869))
    : (¬ p2313) ∨ (¬ p3309) ∨ (¬ p3361) ∨ (¬ p3585) ∨ (¬ p3983) ∨ (¬ p4749) ∨ (¬ p4869) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h26427 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step53030 (p2027 p2737 p2807 p3588 p4777 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26431 : p2027 ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p3588) ∨ (¬ p4777) ∨ (¬ p4790))
    : (¬ p2737) ∨ (¬ p2807) ∨ (¬ p3588) ∨ (¬ p4777) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26431 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53032 (p2027 p2177 p2528 p4107 p4438 p4445 : Prop)
    (h40810 : (¬ p2027))
    (h26433 : p2027 ∨ (¬ p2177) ∨ (¬ p2528) ∨ (¬ p4107) ∨ (¬ p4438) ∨ (¬ p4445))
    : (¬ p2177) ∨ (¬ p2528) ∨ (¬ p4107) ∨ (¬ p4438) ∨ (¬ p4445) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26433 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53033 (p2027 p2341 p2963 p3553 p4104 p4572 : Prop)
    (h40810 : (¬ p2027))
    (h26434 : p2027 ∨ (¬ p2341) ∨ (¬ p2963) ∨ (¬ p3553) ∨ (¬ p4104) ∨ (¬ p4572))
    : (¬ p2341) ∨ (¬ p2963) ∨ (¬ p3553) ∨ (¬ p4104) ∨ (¬ p4572) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26434 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53034 (p2027 p2299 p2470 p3540 p4370 p4712 p5307 : Prop)
    (h40810 : (¬ p2027))
    (h26435 : p2027 ∨ (¬ p2299) ∨ (¬ p2470) ∨ (¬ p3540) ∨ (¬ p4370) ∨ (¬ p4712) ∨ (¬ p5307))
    : (¬ p2299) ∨ (¬ p2470) ∨ (¬ p3540) ∨ (¬ p4370) ∨ (¬ p4712) ∨ (¬ p5307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26435 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53035 (p2027 p2341 p3055 p3548 p3576 p3819 p5086 : Prop)
    (h40810 : (¬ p2027))
    (h26437 : p2027 ∨ (¬ p2341) ∨ (¬ p3055) ∨ (¬ p3548) ∨ (¬ p3576) ∨ (¬ p3819) ∨ (¬ p5086))
    : (¬ p2341) ∨ (¬ p3055) ∨ (¬ p3548) ∨ (¬ p3576) ∨ (¬ p3819) ∨ (¬ p5086) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5086 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26437 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53037 (p2027 p2946 p3115 p4385 p4392 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26441 : p2027 ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p4385) ∨ (¬ p4392) ∨ (¬ p4790))
    : (¬ p2946) ∨ (¬ p3115) ∨ (¬ p4385) ∨ (¬ p4392) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26441 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53038 (p1978 p3043 p4032 p4138 p4503 : Prop)
    (h2138 : p1978)
    (h40893 : (¬ p3043))
    (h26442 : (¬ p1978) ∨ p3043 ∨ (¬ p4032) ∨ (¬ p4138) ∨ p4503)
    : (¬ p4032) ∨ (¬ p4138) ∨ p4503 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4032 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4503) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p1978 := h2138;
    let u4 : (¬ p3043) := h40893;
    (Or.elim h26442 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step53040 (p2027 p2274 p2312 p2341 p3548 p4024 p4105 p4889 : Prop)
    (h40810 : (¬ p2027))
    (h26444 : p2027 ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3548) ∨ (¬ p4024) ∨ (¬ p4105) ∨ (¬ p4889))
    : (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3548) ∨ (¬ p4024) ∨ (¬ p4105) ∨ (¬ p4889) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h26444 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step53041 (p2027 p2319 p2387 p3516 p4107 p4501 : Prop)
    (h40810 : (¬ p2027))
    (h26445 : p2027 ∨ (¬ p2319) ∨ (¬ p2387) ∨ (¬ p3516) ∨ (¬ p4107) ∨ (¬ p4501))
    : (¬ p2319) ∨ (¬ p2387) ∨ (¬ p3516) ∨ (¬ p4107) ∨ (¬ p4501) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26445 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53042 (p2027 p2589 p2608 p2839 p3695 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h26446 : p2027 ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3695) ∨ (¬ p5193))
    : (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3695) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26446 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53045 (p2011 p2027 p2598 p2622 p2850 p2982 p3365 : Prop)
    (h2171 : p2011)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h26449 : (¬ p2011) ∨ p2027 ∨ (¬ p2598) ∨ p2622 ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3365))
    : (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3365) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2011 := h2171;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h26449 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53047 (p2027 p3178 p3767 p4035 p4461 p4790 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h26451 : p2027 ∨ (¬ p3178) ∨ (¬ p3767) ∨ (¬ p4035) ∨ (¬ p4461) ∨ (¬ p4790) ∨ (¬ p5284))
    : (¬ p3178) ∨ (¬ p3767) ∨ (¬ p4035) ∨ (¬ p4461) ∨ (¬ p4790) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3178 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26451 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53049 (p2027 p2104 p2132 p2860 p4312 p4507 p4963 : Prop)
    (h40810 : (¬ p2027))
    (h26454 : p2027 ∨ (¬ p2104) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p4312) ∨ (¬ p4507) ∨ (¬ p4963))
    : (¬ p2104) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p4312) ∨ (¬ p4507) ∨ (¬ p4963) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26454 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53053 (p2027 p2156 p2958 p3952 p4315 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26458 : p2027 ∨ (¬ p2156) ∨ (¬ p2958) ∨ (¬ p3952) ∨ (¬ p4315) ∨ (¬ p4790))
    : (¬ p2156) ∨ (¬ p2958) ∨ (¬ p3952) ∨ (¬ p4315) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26458 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53054 (p2027 p2331 p2737 p3688 p4337 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26459 : p2027 ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4337) ∨ (¬ p4790))
    : (¬ p2331) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4337) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26459 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53055 (p1975 p2027 p2114 p2137 p2156 p2299 p2839 p2881 p3872 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h26460 : (¬ p1975) ∨ p2027 ∨ p2114 ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2299) ∨ (¬ p2839) ∨ (¬ p2881) ∨ (¬ p3872))
    : (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2299) ∨ (¬ p2839) ∨ (¬ p2881) ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1975 := h2135;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2114) := h40864;
    (Or.elim h26460 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53056 (p2027 p2437 p2651 p2952 p3879 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h26461 : p2027 ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4646))
    : (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26461 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53060 (p2027 p2138 p2241 p3027 p3931 p4322 p4385 p4736 p4826 : Prop)
    (h40810 : (¬ p2027))
    (h26465 : p2027 ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4736) ∨ (¬ p4826))
    : (¬ p2138) ∨ (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4736) ∨ (¬ p4826) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26465 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53061 (p2027 p2241 p2264 p3027 p4416 p4592 : Prop)
    (h40810 : (¬ p2027))
    (h26466 : p2027 ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p4416) ∨ (¬ p4592))
    : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p4416) ∨ (¬ p4592) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4416 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4592 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26466 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53062 (p2027 p2807 p3032 p3527 p3659 p4357 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26467 : p2027 ∨ (¬ p2807) ∨ (¬ p3032) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p4357) ∨ (¬ p4790))
    : (¬ p2807) ∨ (¬ p3032) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p4357) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26467 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53070 (p2027 p2383 p2810 p3324 p3987 p4194 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26477 : p2027 ∨ (¬ p2383) ∨ (¬ p2810) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4194) ∨ (¬ p4790))
    : (¬ p2383) ∨ (¬ p2810) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4194) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26477 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53072 (p1975 p2027 p2230 p2233 p2274 p2440 p3016 p4203 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h26479 : (¬ p1975) ∨ p2027 ∨ (¬ p2230) ∨ p2233 ∨ (¬ p2274) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4203))
    : (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4203) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2233) := h40868;
    (Or.elim h26479 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53073 (p2027 p2383 p3324 p3987 p4195 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26480 : p2027 ∨ (¬ p2383) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4195) ∨ (¬ p4790))
    : (¬ p2383) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4195) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26480 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53078 (p2027 p2588 p3051 p3646 p3958 p4140 : Prop)
    (h40810 : (¬ p2027))
    (h26486 : p2027 ∨ (¬ p2588) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3958) ∨ (¬ p4140))
    : (¬ p2588) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3958) ∨ (¬ p4140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26486 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53088 (p2027 p2241 p2449 p2780 p3027 p3950 p4347 p4358 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h26500 : p2027 ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2780) ∨ (¬ p3027) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4736))
    : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2780) ∨ (¬ p3027) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26500 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53089 (p2027 p3323 p3568 p3690 p4556 p5299 p5379 : Prop)
    (h40810 : (¬ p2027))
    (h26502 : p2027 ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3690) ∨ (¬ p4556) ∨ (¬ p5299) ∨ (¬ p5379))
    : (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3690) ∨ (¬ p4556) ∨ (¬ p5299) ∨ (¬ p5379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26502 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53090 (p2027 p2737 p2946 p3583 p4316 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26505 : p2027 ∨ (¬ p2737) ∨ (¬ p2946) ∨ (¬ p3583) ∨ (¬ p4316) ∨ (¬ p4790))
    : (¬ p2737) ∨ (¬ p2946) ∨ (¬ p3583) ∨ (¬ p4316) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26505 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53091 (p1981 p2027 p2148 p2156 p2819 p3319 p3917 p3957 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h26506 : (¬ p1981) ∨ p2027 ∨ p2148 ∨ (¬ p2156) ∨ (¬ p2819) ∨ (¬ p3319) ∨ (¬ p3917) ∨ (¬ p3957))
    : (¬ p2156) ∨ (¬ p2819) ∨ (¬ p3319) ∨ (¬ p3917) ∨ (¬ p3957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1981 := h2141;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2148) := h40865;
    (Or.elim h26506 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53092 (p2027 p2417 p2891 p4363 p4382 p4647 : Prop)
    (h40810 : (¬ p2027))
    (h26507 : p2027 ∨ (¬ p2417) ∨ (¬ p2891) ∨ (¬ p4363) ∨ (¬ p4382) ∨ (¬ p4647))
    : (¬ p2417) ∨ (¬ p2891) ∨ (¬ p4363) ∨ (¬ p4382) ∨ (¬ p4647) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4382 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26507 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53093 (p2027 p2187 p2563 p3923 p4512 p4629 : Prop)
    (h40810 : (¬ p2027))
    (h26508 : p2027 ∨ (¬ p2187) ∨ (¬ p2563) ∨ (¬ p3923) ∨ (¬ p4512) ∨ (¬ p4629))
    : (¬ p2187) ∨ (¬ p2563) ∨ (¬ p3923) ∨ (¬ p4512) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26508 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53096 (p2027 p2573 p2663 p2810 p3574 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26511 : p2027 ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p3574) ∨ (¬ p4790))
    : (¬ p2573) ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p3574) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26511 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53105 (p2027 p2807 p2992 p2996 p4316 p4392 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26524 : p2027 ∨ (¬ p2807) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p4316) ∨ (¬ p4392) ∨ (¬ p4790))
    : (¬ p2807) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p4316) ∨ (¬ p4392) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26524 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53108 (p2027 p2177 p2553 p3659 p3689 p5222 : Prop)
    (h40810 : (¬ p2027))
    (h26528 : p2027 ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3659) ∨ (¬ p3689) ∨ (¬ p5222))
    : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3659) ∨ (¬ p3689) ∨ (¬ p5222) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3689 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26528 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53109 (p1978 p2027 p2462 p2860 p3646 p4107 p4244 p4275 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h26529 : (¬ p1978) ∨ p2027 ∨ p2462 ∨ (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4244) ∨ (¬ p4275))
    : (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4244) ∨ (¬ p4275) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1978 := h2138;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2462) := h40875;
    (Or.elim h26529 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53110 (p2027 p2651 p2992 p4111 p4315 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26530 : p2027 ∨ (¬ p2651) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4315) ∨ (¬ p4790))
    : (¬ p2651) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4315) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26530 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53114 (p2027 p2553 p3097 p3646 p3660 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h26534 : p2027 ∨ (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3660) ∨ (¬ p4533))
    : (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3660) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26534 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53116 (p1976 p2027 p2765 p3055 p3367 p3583 p3758 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h26536 : (¬ p1976) ∨ p2027 ∨ p2765 ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3758))
    : (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3758) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h26536 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53117 (p2000 p2027 p2542 p2589 p2633 p3644 p3742 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h26537 : (¬ p2000) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p2589) ∨ p2633 ∨ (¬ p3644) ∨ (¬ p3742))
    : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3644) ∨ (¬ p3742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2000 := h2160;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h26537 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53118 (p2027 p2088 p3178 p3877 p4118 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26539 : p2027 ∨ (¬ p2088) ∨ (¬ p3178) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4790))
    : (¬ p2088) ∨ (¬ p3178) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3178 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26539 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53119 (p2027 p2459 p2881 p3857 p3961 p4986 : Prop)
    (h40810 : (¬ p2027))
    (h26540 : p2027 ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4986))
    : (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4986) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26540 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53120 (p2027 p2192 p2946 p2963 p3745 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h26541 : p2027 ∨ (¬ p2192) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p4960))
    : (¬ p2192) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26541 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53121 (p1984 p2027 p2553 p3549 p3578 p3591 p3660 p3880 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h26543 : (¬ p1984) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3549) ∨ p3578 ∨ (¬ p3591) ∨ (¬ p3660) ∨ (¬ p3880))
    : (¬ p2553) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p3660) ∨ (¬ p3880) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3578) := h40900;
    (Or.elim h26543 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53131 (p1984 p2027 p2169 p3583 p3758 p3954 p3989 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h26560 : (¬ p1984) ∨ p2027 ∨ p2169 ∨ (¬ p3583) ∨ (¬ p3758) ∨ (¬ p3954) ∨ (¬ p3989))
    : (¬ p3583) ∨ (¬ p3758) ∨ (¬ p3954) ∨ (¬ p3989) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3583 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h26560 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53134 (p2027 p2241 p2295 p2589 p2641 p3989 p4110 p4501 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h26564 : p2027 ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2589) ∨ (¬ p2641) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4501) ∨ (¬ p5193))
    : (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2589) ∨ (¬ p2641) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4501) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26564 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53138 (p2027 p2295 p2331 p3822 p4790 p4841 : Prop)
    (h40810 : (¬ p2027))
    (h26569 : p2027 ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3822) ∨ (¬ p4790) ∨ (¬ p4841))
    : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3822) ∨ (¬ p4790) ∨ (¬ p4841) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26569 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53139 (p2027 p2598 p2753 p2850 p3688 p4342 p4715 : Prop)
    (h40810 : (¬ p2027))
    (h26570 : p2027 ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4715))
    : (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26570 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53144 (p2020 p2027 p2202 p2427 p3156 p3969 p4320 : Prop)
    (h2180 : p2020)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h26575 : (¬ p2020) ∨ p2027 ∨ p2202 ∨ (¬ p2427) ∨ (¬ p3156) ∨ (¬ p3969) ∨ (¬ p4320))
    : (¬ p2427) ∨ (¬ p3156) ∨ (¬ p3969) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2020 := h2180;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h26575 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53146 (p2027 p2363 p2668 p4037 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h26579 : p2027 ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p4037) ∨ (¬ p4604))
    : (¬ p2363) ∨ (¬ p2668) ∨ (¬ p4037) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2027) := h40810;
    (Or.elim h26579 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step53150 (p2027 p2341 p2922 p3193 p3575 p4636 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h26584 : p2027 ∨ (¬ p2341) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p3575) ∨ (¬ p4636) ∨ (¬ p4666))
    : (¬ p2341) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p3575) ∨ (¬ p4636) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26584 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53151 (p2027 p2406 p2427 p3556 p3904 p5191 : Prop)
    (h40810 : (¬ p2027))
    (h26586 : p2027 ∨ (¬ p2406) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p5191))
    : (¬ p2406) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p5191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26586 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53156 (p2027 p2187 p2387 p3051 p4198 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h26599 : p2027 ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p3051) ∨ (¬ p4198) ∨ (¬ p4558))
    : (¬ p2187) ∨ (¬ p2387) ∨ (¬ p3051) ∨ (¬ p4198) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26599 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53158 (p2027 p2252 p2750 p2963 p3399 p3954 p4037 p4075 p4191 p4826 : Prop)
    (h40810 : (¬ p2027))
    (h26602 : p2027 ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3399) ∨ (¬ p3954) ∨ (¬ p4037) ∨ (¬ p4075) ∨ (¬ p4191) ∨ (¬ p4826))
    : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3399) ∨ (¬ p3954) ∨ (¬ p4037) ∨ (¬ p4075) ∨ (¬ p4191) ∨ (¬ p4826) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26602 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53159 (p2027 p3093 p3954 p4242 p4243 p4512 p4741 : Prop)
    (h40810 : (¬ p2027))
    (h26603 : p2027 ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4243) ∨ (¬ p4512) ∨ (¬ p4741))
    : (¬ p3093) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4243) ∨ (¬ p4512) ∨ (¬ p4741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26603 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53161 (p2027 p2749 p2992 p3365 p4315 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h26605 : p2027 ∨ (¬ p2749) ∨ (¬ p2992) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p4734))
    : (¬ p2749) ∨ (¬ p2992) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2749 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26605 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53162 (p1977 p2027 p2241 p2553 p3008 p3549 p3591 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h26606 : (¬ p1977) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2553) ∨ p3008 ∨ (¬ p3549) ∨ (¬ p3591))
    : (¬ p2241) ∨ (¬ p2553) ∨ (¬ p3549) ∨ (¬ p3591) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3008) := h40891;
    (Or.elim h26606 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53163 (p1988 p2027 p2622 p2761 p2901 p3136 p3246 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h26607 : (¬ p1988) ∨ p2027 ∨ p2622 ∨ (¬ p2761) ∨ (¬ p2901) ∨ (¬ p3136) ∨ (¬ p3246))
    : (¬ p2761) ∨ (¬ p2901) ∨ (¬ p3136) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h26607 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53166 (p2027 p2577 p2659 p3016 p3564 p3946 : Prop)
    (h40810 : (¬ p2027))
    (h26610 : p2027 ∨ (¬ p2577) ∨ (¬ p2659) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3946))
    : (¬ p2577) ∨ (¬ p2659) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26610 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53169 (p1991 p2027 p2459 p2534 p2633 p2657 p3742 p4186 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h26615 : (¬ p1991) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2534) ∨ p2633 ∨ (¬ p2657) ∨ (¬ p3742) ∨ (¬ p4186))
    : (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3742) ∨ (¬ p4186) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1991 := h2151;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h26615 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53179 (p1990 p2027 p2202 p2352 p2493 p3097 p3238 p3955 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h26629 : (¬ p1990) ∨ p2027 ∨ p2202 ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3097) ∨ (¬ p3238) ∨ (¬ p3955))
    : (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3097) ∨ (¬ p3238) ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h26629 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53180 (p1976 p2027 p2387 p2764 p2778 p2819 p3917 p4191 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h26631 : (¬ p1976) ∨ p2027 ∨ (¬ p2387) ∨ p2764 ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p3917) ∨ (¬ p4191))
    : (¬ p2387) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p3917) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h26631 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53183 (p2027 p2396 p2761 p4321 p5142 p5357 : Prop)
    (h40810 : (¬ p2027))
    (h26634 : p2027 ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p4321) ∨ (¬ p5142) ∨ (¬ p5357))
    : (¬ p2396) ∨ (¬ p2761) ∨ (¬ p4321) ∨ (¬ p5142) ∨ (¬ p5357) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5142 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26634 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53186 (p2027 p3097 p3156 p3952 p4405 p4441 : Prop)
    (h40810 : (¬ p2027))
    (h26637 : p2027 ∨ (¬ p3097) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p4405) ∨ (¬ p4441))
    : (¬ p3097) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p4405) ∨ (¬ p4441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3097 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26637 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53188 (p1997 p2027 p2156 p2191 p2766 p3370 p3692 p4110 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h26639 : (¬ p1997) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p2191) ∨ p2766 ∨ (¬ p3370) ∨ (¬ p3692) ∨ (¬ p4110))
    : (¬ p2156) ∨ (¬ p2191) ∨ (¬ p3370) ∨ (¬ p3692) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h26639 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53191 (p1987 p2027 p2992 p2997 p3097 p3745 p4154 p4315 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h26642 : (¬ p1987) ∨ p2027 ∨ (¬ p2992) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3745) ∨ (¬ p4154) ∨ (¬ p4315))
    : (¬ p2992) ∨ (¬ p3097) ∨ (¬ p3745) ∨ (¬ p4154) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h26642 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53192 (p2027 p2911 p3146 p4278 p4660 p4905 p5107 : Prop)
    (h40810 : (¬ p2027))
    (h26643 : p2027 ∨ (¬ p2911) ∨ (¬ p3146) ∨ (¬ p4278) ∨ (¬ p4660) ∨ (¬ p4905) ∨ (¬ p5107))
    : (¬ p2911) ∨ (¬ p3146) ∨ (¬ p4278) ∨ (¬ p4660) ∨ (¬ p4905) ∨ (¬ p5107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26643 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53193 (p2027 p2245 p2352 p2598 p3146 p3172 p3422 p4118 p4134 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h26644 : p2027 ∨ (¬ p2245) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p3146) ∨ (¬ p3172) ∨ (¬ p3422) ∨ (¬ p4118) ∨ (¬ p4134) ∨ (¬ p4733))
    : (¬ p2245) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p3146) ∨ (¬ p3172) ∨ (¬ p3422) ∨ (¬ p4118) ∨ (¬ p4134) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26644 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53199 (p2001 p2027 p2220 p2766 p3646 p3989 p4347 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h26654 : (¬ p2001) ∨ p2027 ∨ (¬ p2220) ∨ p2766 ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4347))
    : (¬ p2220) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2001 := h2161;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h26654 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53201 (p1994 p2997 p3742 p4276 : Prop)
    (h2154 : p1994)
    (h40890 : (¬ p2997))
    (h26656 : (¬ p1994) ∨ p2997 ∨ (¬ p3742) ∨ p4276)
    : (¬ p3742) ∨ p4276 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3742 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4276) := (fun h => hn (Or.inr h));
    let u2 : p1994 := h2154;
    let u3 : (¬ p2997) := h40890;
    (Or.elim h26656 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step53202 (p2027 p2210 p2563 p3860 p3906 p4210 p4507 : Prop)
    (h40810 : (¬ p2027))
    (h26657 : p2027 ∨ (¬ p2210) ∨ (¬ p2563) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p4210) ∨ (¬ p4507))
    : (¬ p2210) ∨ (¬ p2563) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p4210) ∨ (¬ p4507) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26657 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53204 (p1998 p2027 p2247 p2688 p2881 p2922 p3379 p3569 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h26659 : (¬ p1998) ∨ p2027 ∨ (¬ p2247) ∨ p2688 ∨ (¬ p2881) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3569))
    : (¬ p2247) ∨ (¬ p2881) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3569) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h26659 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53206 (p2027 p2470 p2663 p2810 p4256 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26661 : p2027 ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p4256) ∨ (¬ p4790))
    : (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p4256) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26661 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53207 (p2027 p2248 p2946 p3146 p3156 p3548 p3591 p4105 p5118 p5558 : Prop)
    (h40810 : (¬ p2027))
    (h26662 : p2027 ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3548) ∨ (¬ p3591) ∨ (¬ p4105) ∨ (¬ p5118) ∨ (¬ p5558))
    : (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3548) ∨ (¬ p3591) ∨ (¬ p4105) ∨ (¬ p5118) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26662 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53208 (p2027 p3516 p3572 p3947 p4104 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26663 : p2027 ∨ (¬ p3516) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4104) ∨ (¬ p4790))
    : (¬ p3516) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4104) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26663 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53209 (p2027 p2284 p2553 p2696 p2742 p2992 p3585 p3822 p4718 p4737 p5220 : Prop)
    (h40810 : (¬ p2027))
    (h26665 : p2027 ∨ (¬ p2284) ∨ (¬ p2553) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2992) ∨ (¬ p3585) ∨ (¬ p3822) ∨ (¬ p4718) ∨ (¬ p4737) ∨ (¬ p5220))
    : (¬ p2284) ∨ (¬ p2553) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2992) ∨ (¬ p3585) ∨ (¬ p3822) ∨ (¬ p4718) ∨ (¬ p4737) ∨ (¬ p5220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26665 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53210 (p2010 p2027 p2437 p2459 p2481 p2633 p3857 p4256 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h26667 : (¬ p2010) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p2459) ∨ (¬ p2481) ∨ p2633 ∨ (¬ p3857) ∨ (¬ p4256))
    : (¬ p2437) ∨ (¬ p2459) ∨ (¬ p2481) ∨ (¬ p3857) ∨ (¬ p4256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2481 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2010 := h2170;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h26667 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53212 (p2027 p2284 p2590 p2819 p3956 p4428 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h26669 : p2027 ∨ (¬ p2284) ∨ (¬ p2590) ∨ (¬ p2819) ∨ (¬ p3956) ∨ (¬ p4428) ∨ (¬ p4705))
    : (¬ p2284) ∨ (¬ p2590) ∨ (¬ p2819) ∨ (¬ p3956) ∨ (¬ p4428) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26669 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53213 (p2000 p2027 p2274 p2542 p2589 p2765 p3742 p3921 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h26670 : (¬ p2000) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2542) ∨ (¬ p2589) ∨ p2765 ∨ (¬ p3742) ∨ (¬ p3921))
    : (¬ p2274) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3742) ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2000 := h2160;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h26670 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53217 (p2027 p2230 p2563 p3540 p4001 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h26675 : p2027 ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3540) ∨ (¬ p4001) ∨ (¬ p4555))
    : (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3540) ∨ (¬ p4001) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26675 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53220 (p1991 p2027 p2440 p2657 p2764 p4322 p4948 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h26679 : (¬ p1991) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2657) ∨ p2764 ∨ (¬ p4322) ∨ (¬ p4948))
    : (¬ p2440) ∨ (¬ p2657) ∨ (¬ p4322) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h26679 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53222 (p2027 p2177 p2295 p2331 p2957 p3146 p3697 p3857 p4315 p4790 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h26682 : p2027 ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2957) ∨ (¬ p3146) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4315) ∨ (¬ p4790) ∨ (¬ p4905))
    : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2957) ∨ (¬ p3146) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4315) ∨ (¬ p4790) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26682 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53223 (p2027 p2449 p2807 p4324 p4357 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26683 : p2027 ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p4324) ∨ (¬ p4357) ∨ (¬ p4790))
    : (¬ p2449) ∨ (¬ p2807) ∨ (¬ p4324) ∨ (¬ p4357) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26683 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53224 (p2027 p2493 p2579 p2655 p2946 p4116 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h26686 : p2027 ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2946) ∨ (¬ p4116) ∨ (¬ p4704))
    : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2946) ∨ (¬ p4116) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26686 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53227 (p2027 p2331 p2363 p2819 p2957 p4120 p4315 p4337 p4790 p5118 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h26689 : p2027 ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2819) ∨ (¬ p2957) ∨ (¬ p4120) ∨ (¬ p4315) ∨ (¬ p4337) ∨ (¬ p4790) ∨ (¬ p5118) ∨ (¬ p5568))
    : (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2819) ∨ (¬ p2957) ∨ (¬ p4120) ∨ (¬ p4315) ∨ (¬ p4337) ∨ (¬ p4790) ∨ (¬ p5118) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26689 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53229 (p2027 p2663 p2810 p3355 p3359 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26691 : p2027 ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p3355) ∨ (¬ p3359) ∨ (¬ p4790))
    : (¬ p2663) ∨ (¬ p2810) ∨ (¬ p3355) ∨ (¬ p3359) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2663 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26691 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53232 (p1982 p2027 p2331 p2363 p2633 p2668 p3246 p3570 p3947 p4315 p4386 p4790 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h26694 : (¬ p1982) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2363) ∨ p2633 ∨ (¬ p2668) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3947) ∨ (¬ p4315) ∨ (¬ p4386) ∨ (¬ p4790))
    : (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3947) ∨ (¬ p4315) ∨ (¬ p4386) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p1982 := h2142;
    let u10 : (¬ p2027) := h40810;
    let u11 : (¬ p2633) := h40879;
    (Or.elim h26694 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u11 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (False.elim (r10 u8)))))))))))))))))))))))))

theorem step53234 (p1998 p2027 p2264 p2842 p3201 p3516 p3575 p3947 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h26696 : (¬ p1998) ∨ p2027 ∨ (¬ p2264) ∨ p2842 ∨ (¬ p3201) ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p3947))
    : (¬ p2264) ∨ (¬ p3201) ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2842) := h40885;
    (Or.elim h26696 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53236 (p1998 p2027 p2323 p2449 p2651 p2911 p3580 p4278 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h26699 : (¬ p1998) ∨ p2027 ∨ p2323 ∨ (¬ p2449) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3580) ∨ (¬ p4278))
    : (¬ p2449) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3580) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h26699 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53238 (p1994 p2027 p2166 p2440 p2765 p3880 p4173 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h26701 : (¬ p1994) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2440) ∨ p2765 ∨ (¬ p3880) ∨ (¬ p4173))
    : (¬ p2166) ∨ (¬ p2440) ∨ (¬ p3880) ∨ (¬ p4173) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h26701 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53239 (p2027 p2220 p2579 p3880 p4399 p4715 : Prop)
    (h40810 : (¬ p2027))
    (h26702 : p2027 ∨ (¬ p2220) ∨ (¬ p2579) ∨ (¬ p3880) ∨ (¬ p4399) ∨ (¬ p4715))
    : (¬ p2220) ∨ (¬ p2579) ∨ (¬ p3880) ∨ (¬ p4399) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26702 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53244 (p2027 p2901 p2950 p3136 p3556 p4787 : Prop)
    (h40810 : (¬ p2027))
    (h26710 : p2027 ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3136) ∨ (¬ p3556) ∨ (¬ p4787))
    : (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3136) ∨ (¬ p3556) ∨ (¬ p4787) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26710 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53253 (p1987 p2027 p2202 p2437 p2440 p2696 p3540 p3905 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h26721 : (¬ p1987) ∨ p2027 ∨ p2202 ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2696) ∨ (¬ p3540) ∨ (¬ p3905))
    : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2696) ∨ (¬ p3540) ∨ (¬ p3905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h26721 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53259 (p1990 p2027 p2307 p2344 p2668 p3568 p3989 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40871 : (¬ p2344))
    (h26730 : (¬ p1990) ∨ p2027 ∨ (¬ p2307) ∨ p2344 ∨ (¬ p2668) ∨ (¬ p3568) ∨ (¬ p3989))
    : (¬ p2307) ∨ (¬ p2668) ∨ (¬ p3568) ∨ (¬ p3989) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2344) := h40871;
    (Or.elim h26730 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53263 (p2027 p2573 p2911 p3551 p3741 p4717 p5197 : Prop)
    (h40810 : (¬ p2027))
    (h26735 : p2027 ∨ (¬ p2573) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4717) ∨ (¬ p5197))
    : (¬ p2573) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4717) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26735 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53264 (p2007 p2027 p2202 p2437 p2440 p2518 p3347 p3540 : Prop)
    (h2167 : p2007)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h26736 : (¬ p2007) ∨ p2027 ∨ p2202 ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2518) ∨ (¬ p3347) ∨ (¬ p3540))
    : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2518) ∨ (¬ p3347) ∨ (¬ p3540) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2007 := h2167;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h26736 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53266 (p1975 p2027 p2202 p2299 p2437 p2440 p2911 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h26738 : (¬ p1975) ∨ p2027 ∨ p2202 ∨ (¬ p2299) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2911))
    : (¬ p2299) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h26738 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53267 (p1987 p2027 p2202 p2440 p2476 p2737 p3083 p3347 p4257 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h26741 : (¬ p1987) ∨ p2027 ∨ p2202 ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2737) ∨ (¬ p3083) ∨ (¬ p3347) ∨ (¬ p4257))
    : (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2737) ∨ (¬ p3083) ∨ (¬ p3347) ∨ (¬ p4257) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1987 := h2147;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2202) := h40867;
    (Or.elim h26741 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53272 (p2027 p2138 p2598 p3201 p3698 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h26748 : p2027 ∨ (¬ p2138) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3698) ∨ (¬ p4646))
    : (¬ p2138) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3698) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26748 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53275 (p2027 p2528 p2881 p3821 p4283 p4438 p4445 : Prop)
    (h40810 : (¬ p2027))
    (h26751 : p2027 ∨ (¬ p2528) ∨ (¬ p2881) ∨ (¬ p3821) ∨ (¬ p4283) ∨ (¬ p4438) ∨ (¬ p4445))
    : (¬ p2528) ∨ (¬ p2881) ∨ (¬ p3821) ∨ (¬ p4283) ∨ (¬ p4438) ∨ (¬ p4445) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26751 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53277 (p2027 p2230 p2440 p2663 p2810 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h26754 : p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p4790))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26754 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53278 (p2027 p2246 p2651 p2749 p2881 p3016 p3546 p3551 p3564 p3690 p4330 p4445 p4796 : Prop)
    (h40810 : (¬ p2027))
    (h26755 : p2027 ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p2881) ∨ (¬ p3016) ∨ (¬ p3546) ∨ (¬ p3551) ∨ (¬ p3564) ∨ (¬ p3690) ∨ (¬ p4330) ∨ (¬ p4445) ∨ (¬ p4796))
    : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p2881) ∨ (¬ p3016) ∨ (¬ p3546) ∨ (¬ p3551) ∨ (¬ p3564) ∨ (¬ p3690) ∨ (¬ p4330) ∨ (¬ p4445) ∨ (¬ p4796) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4796 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h26755 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step53279 (p2027 p3146 p3657 p3767 p4381 p4456 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h26756 : p2027 ∨ (¬ p3146) ∨ (¬ p3657) ∨ (¬ p3767) ∨ (¬ p4381) ∨ (¬ p4456) ∨ (¬ p4905))
    : (¬ p3146) ∨ (¬ p3657) ∨ (¬ p3767) ∨ (¬ p4381) ∨ (¬ p4456) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4456 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26756 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53282 (p1997 p2027 p2542 p3128 p3461 p3742 p4425 p4635 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40894 : (¬ p3128))
    (h26760 : (¬ p1997) ∨ p2027 ∨ (¬ p2542) ∨ p3128 ∨ (¬ p3461) ∨ (¬ p3742) ∨ (¬ p4425) ∨ (¬ p4635))
    : (¬ p2542) ∨ (¬ p3461) ∨ (¬ p3742) ∨ (¬ p4425) ∨ (¬ p4635) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3128) := h40894;
    (Or.elim h26760 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53286 (p2027 p2598 p2608 p2753 p2761 p3946 p4166 p4191 p4638 p5021 p5126 : Prop)
    (h40810 : (¬ p2027))
    (h26765 : p2027 ∨ (¬ p2598) ∨ (¬ p2608) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3946) ∨ (¬ p4166) ∨ (¬ p4191) ∨ (¬ p4638) ∨ (¬ p5021) ∨ (¬ p5126))
    : (¬ p2598) ∨ (¬ p2608) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3946) ∨ (¬ p4166) ∨ (¬ p4191) ∨ (¬ p4638) ∨ (¬ p5021) ∨ (¬ p5126) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5126 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26765 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53291 (p2027 p2797 p3115 p3413 p4385 p4392 p4975 : Prop)
    (h40810 : (¬ p2027))
    (h26773 : p2027 ∨ (¬ p2797) ∨ (¬ p3115) ∨ (¬ p3413) ∨ (¬ p4385) ∨ (¬ p4392) ∨ (¬ p4975))
    : (¬ p2797) ∨ (¬ p3115) ∨ (¬ p3413) ∨ (¬ p4385) ∨ (¬ p4392) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26773 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53293 (p2027 p2707 p2743 p2810 p4325 p4652 : Prop)
    (h40810 : (¬ p2027))
    (h26775 : p2027 ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p4325) ∨ (¬ p4652))
    : (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p4325) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26775 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53296 (p2027 p2748 p3276 p3355 p3365 p3367 p3759 p4312 p4360 p4734 p5123 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h26779 : p2027 ∨ (¬ p2748) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4312) ∨ (¬ p4360) ∨ (¬ p4734) ∨ (¬ p5123) ∨ (¬ p5568))
    : (¬ p2748) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4312) ∨ (¬ p4360) ∨ (¬ p4734) ∨ (¬ p5123) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2748 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h26779 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step53301 (p2027 p2122 p2177 p2245 p2774 p2952 p2992 p4041 p4360 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h26784 : p2027 ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4733))
    : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26784 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53304 (p2005 p2027 p2114 p2476 p2573 p3367 p3641 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h26789 : (¬ p2005) ∨ p2027 ∨ p2114 ∨ (¬ p2476) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3641))
    : (¬ p2476) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h26789 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53307 (p2027 p2911 p3201 p3551 p4727 p5197 : Prop)
    (h40810 : (¬ p2027))
    (h26792 : p2027 ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3551) ∨ (¬ p4727) ∨ (¬ p5197))
    : (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3551) ∨ (¬ p4727) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26792 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53310 (p1988 p2027 p2761 p2870 p3212 p3474 p3556 p4135 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h26795 : (¬ p1988) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p2870) ∨ (¬ p3212) ∨ p3474 ∨ (¬ p3556) ∨ (¬ p4135))
    : (¬ p2761) ∨ (¬ p2870) ∨ (¬ p3212) ∨ (¬ p3556) ∨ (¬ p4135) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3474) := h40898;
    (Or.elim h26795 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53311 (p1984 p2027 p2114 p2819 p2829 p3591 p3923 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h26796 : (¬ p1984) ∨ p2027 ∨ p2114 ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3591) ∨ (¬ p3923))
    : (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3591) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h26796 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53312 (p2027 p2312 p2563 p3309 p4235 p4283 p4518 : Prop)
    (h40810 : (¬ p2027))
    (h26797 : p2027 ∨ (¬ p2312) ∨ (¬ p2563) ∨ (¬ p3309) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4518))
    : (¬ p2312) ∨ (¬ p2563) ∨ (¬ p3309) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4518) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2312 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26797 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53314 (p1990 p2027 p2246 p2545 p2563 p2958 p3051 p4111 p4235 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h26799 : (¬ p1990) ∨ p2027 ∨ (¬ p2246) ∨ p2545 ∨ (¬ p2563) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4111) ∨ (¬ p4235))
    : (¬ p2246) ∨ (¬ p2563) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4111) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1990 := h2150;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2545) := h40876;
    (Or.elim h26799 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53317 (p2005 p2027 p2819 p2829 p2842 p3585 p3956 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h26805 : (¬ p2005) ∨ p2027 ∨ (¬ p2819) ∨ (¬ p2829) ∨ p2842 ∨ (¬ p3585) ∨ (¬ p3956))
    : (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p3956) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2842) := h40885;
    (Or.elim h26805 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53318 (p2005 p2027 p2122 p2588 p2829 p2842 p3585 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h26806 : (¬ p2005) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2588) ∨ (¬ p2829) ∨ p2842 ∨ (¬ p3585))
    : (¬ p2122) ∨ (¬ p2588) ∨ (¬ p2829) ∨ (¬ p3585) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2842) := h40885;
    (Or.elim h26806 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53320 (p2027 p2313 p2386 p3309 p3574 p3948 p4338 p4814 : Prop)
    (h40810 : (¬ p2027))
    (h26808 : p2027 ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p3948) ∨ (¬ p4338) ∨ (¬ p4814))
    : (¬ p2313) ∨ (¬ p2386) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p3948) ∨ (¬ p4338) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h26808 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step53321 (p1975 p2027 p2122 p2148 p2156 p3737 p4329 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h26809 : (¬ p1975) ∨ p2027 ∨ (¬ p2122) ∨ p2148 ∨ (¬ p2156) ∨ (¬ p3737) ∨ (¬ p4329))
    : (¬ p2122) ∨ (¬ p2156) ∨ (¬ p3737) ∨ (¬ p4329) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2148) := h40865;
    (Or.elim h26809 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53322 (p2027 p2331 p2589 p3323 p3461 p3880 p4117 p4729 p5123 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h26810 : p2027 ∨ (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3880) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p5123) ∨ (¬ p5568))
    : (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3880) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p5123) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26810 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53323 (p1978 p2027 p2274 p2373 p2588 p2590 p2765 p4120 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h26811 : (¬ p1978) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2373) ∨ (¬ p2588) ∨ (¬ p2590) ∨ p2765 ∨ (¬ p4120))
    : (¬ p2274) ∨ (¬ p2373) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p4120) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1978 := h2138;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h26811 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53325 (p2027 p2352 p2573 p3540 p3921 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h26813 : p2027 ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p4405))
    : (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26813 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53326 (p2027 p2528 p2598 p2743 p2963 p3361 p3641 p4037 p4604 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h26815 : p2027 ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p3641) ∨ (¬ p4037) ∨ (¬ p4604) ∨ (¬ p4737))
    : (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p3641) ∨ (¬ p4037) ∨ (¬ p4604) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26815 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53327 (p2027 p2737 p2928 p3201 p4257 p4749 : Prop)
    (h40810 : (¬ p2027))
    (h26816 : p2027 ∨ (¬ p2737) ∨ (¬ p2928) ∨ (¬ p3201) ∨ (¬ p4257) ∨ (¬ p4749))
    : (¬ p2737) ∨ (¬ p2928) ∨ (¬ p3201) ∨ (¬ p4257) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26816 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53328 (p2027 p2383 p2584 p2590 p2656 p3742 p3956 p4644 : Prop)
    (h40810 : (¬ p2027))
    (h26817 : p2027 ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2590) ∨ (¬ p2656) ∨ (¬ p3742) ∨ (¬ p3956) ∨ (¬ p4644))
    : (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2590) ∨ (¬ p2656) ∨ (¬ p3742) ∨ (¬ p3956) ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h26817 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step53329 (p1987 p2027 p2098 p2737 p2842 p3055 p4242 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h26818 : (¬ p1987) ∨ p2027 ∨ (¬ p2098) ∨ (¬ p2737) ∨ p2842 ∨ (¬ p3055) ∨ (¬ p4242))
    : (¬ p2098) ∨ (¬ p2737) ∨ (¬ p3055) ∨ (¬ p4242) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2842) := h40885;
    (Or.elim h26818 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53334 (p2027 p2166 p3051 p4120 p4235 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h26825 : p2027 ∨ (¬ p2166) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4235) ∨ (¬ p4632))
    : (¬ p2166) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4235) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53337 (p1990 p2027 p2299 p2470 p2542 p2563 p2633 p3549 p3591 p4256 p5190 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h26828 : (¬ p1990) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2563) ∨ p2633 ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4256) ∨ (¬ p5190))
    : (¬ p2299) ∨ (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4256) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p1990 := h2150;
    let u9 : (¬ p2027) := h40810;
    let u10 : (¬ p2633) := h40879;
    (Or.elim h26828 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u10 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step53338 (p1990 p2027 p2459 p2563 p2633 p3692 p4119 p4241 p4320 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h26829 : (¬ p1990) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2563) ∨ p2633 ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4241) ∨ (¬ p4320))
    : (¬ p2459) ∨ (¬ p2563) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4241) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1990 := h2150;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2633) := h40879;
    (Or.elim h26829 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53344 (p2027 p2651 p2761 p3422 p3564 p3572 p3773 p4155 p4343 p4621 p4790 p5294 : Prop)
    (h40810 : (¬ p2027))
    (h26835 : p2027 ∨ (¬ p2651) ∨ (¬ p2761) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p3572) ∨ (¬ p3773) ∨ (¬ p4155) ∨ (¬ p4343) ∨ (¬ p4621) ∨ (¬ p4790) ∨ (¬ p5294))
    : (¬ p2651) ∨ (¬ p2761) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p3572) ∨ (¬ p3773) ∨ (¬ p4155) ∨ (¬ p4343) ∨ (¬ p4621) ∨ (¬ p4790) ∨ (¬ p5294) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5294 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h26835 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step53354 (p1988 p2027 p2462 p2651 p3276 p3343 p3572 p3791 p4107 p4391 p4790 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h26847 : (¬ p1988) ∨ p2027 ∨ p2462 ∨ (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3572) ∨ (¬ p3791) ∨ (¬ p4107) ∨ (¬ p4391) ∨ (¬ p4790))
    : (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3572) ∨ (¬ p3791) ∨ (¬ p4107) ∨ (¬ p4391) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p1988 := h2148;
    let u9 : (¬ p2027) := h40810;
    let u10 : (¬ p2462) := h40875;
    (Or.elim h26847 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u10 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step53355 (p2027 p2396 p2553 p2573 p3365 p3366 p3519 p3553 p3572 p4376 p4668 : Prop)
    (h40810 : (¬ p2027))
    (h26850 : p2027 ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4376) ∨ (¬ p4668))
    : (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4376) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26850 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53361 (p1992 p2027 p2437 p2545 p2696 p2743 p3540 p3905 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h26860 : (¬ p1992) ∨ p2027 ∨ (¬ p2437) ∨ p2545 ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3540) ∨ (¬ p3905))
    : (¬ p2437) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3540) ∨ (¬ p3905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h26860 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53362 (p2027 p2210 p2252 p2440 p2657 p2750 p2972 p3954 p4110 p5046 : Prop)
    (h40810 : (¬ p2027))
    (h26861 : p2027 ∨ (¬ p2210) ∨ (¬ p2252) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2972) ∨ (¬ p3954) ∨ (¬ p4110) ∨ (¬ p5046))
    : (¬ p2210) ∨ (¬ p2252) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2972) ∨ (¬ p3954) ∨ (¬ p4110) ∨ (¬ p5046) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26861 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53363 (p1998 p2027 p2528 p3008 p3083 p3574 p4348 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h26862 : (¬ p1998) ∨ p2027 ∨ (¬ p2528) ∨ p3008 ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p4348))
    : (¬ p2528) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3008) := h40891;
    (Or.elim h26862 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53366 (p2027 p2307 p2786 p2952 p3483 p3497 p3692 p3822 p4330 p4789 : Prop)
    (h40810 : (¬ p2027))
    (h26865 : p2027 ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p2952) ∨ (¬ p3483) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3822) ∨ (¬ p4330) ∨ (¬ p4789))
    : (¬ p2307) ∨ (¬ p2786) ∨ (¬ p2952) ∨ (¬ p3483) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3822) ∨ (¬ p4330) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26865 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53367 (p2027 p2307 p2534 p2657 p2786 p3483 p3822 p4256 p4330 p4789 : Prop)
    (h40810 : (¬ p2027))
    (h26866 : p2027 ∨ (¬ p2307) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2786) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4256) ∨ (¬ p4330) ∨ (¬ p4789))
    : (¬ p2307) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2786) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4256) ∨ (¬ p4330) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26866 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53369 (p2027 p2952 p3055 p3276 p3361 p3497 p3619 p4749 p5123 p5164 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h26869 : p2027 ∨ (¬ p2952) ∨ (¬ p3055) ∨ (¬ p3276) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3619) ∨ (¬ p4749) ∨ (¬ p5123) ∨ (¬ p5164) ∨ (¬ p5568))
    : (¬ p2952) ∨ (¬ p3055) ∨ (¬ p3276) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3619) ∨ (¬ p4749) ∨ (¬ p5123) ∨ (¬ p5164) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5164 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26869 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53370 (p2027 p3055 p3276 p3361 p3414 p3553 p3619 p4749 p5123 p5164 p5558 : Prop)
    (h40810 : (¬ p2027))
    (h26870 : p2027 ∨ (¬ p3055) ∨ (¬ p3276) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3619) ∨ (¬ p4749) ∨ (¬ p5123) ∨ (¬ p5164) ∨ (¬ p5558))
    : (¬ p3055) ∨ (¬ p3276) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3619) ∨ (¬ p4749) ∨ (¬ p5123) ∨ (¬ p5164) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5164 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26870 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53372 (p2027 p2132 p2437 p2619 p3146 p3359 p3540 p4697 p4729 : Prop)
    (h40810 : (¬ p2027))
    (h26872 : p2027 ∨ (¬ p2132) ∨ (¬ p2437) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3359) ∨ (¬ p3540) ∨ (¬ p4697) ∨ (¬ p4729))
    : (¬ p2132) ∨ (¬ p2437) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3359) ∨ (¬ p3540) ∨ (¬ p4697) ∨ (¬ p4729) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26872 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53373 (p2027 p2144 p2220 p2579 p2655 p3105 p3461 p3579 p3581 p3694 p4397 p4429 p4789 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h26873 : p2027 ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p3105) ∨ (¬ p3461) ∨ (¬ p3579) ∨ (¬ p3581) ∨ (¬ p3694) ∨ (¬ p4397) ∨ (¬ p4429) ∨ (¬ p4789) ∨ (¬ p5284))
    : (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p3105) ∨ (¬ p3461) ∨ (¬ p3579) ∨ (¬ p3581) ∨ (¬ p3694) ∨ (¬ p4397) ∨ (¬ p4429) ∨ (¬ p4789) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4397 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4429 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : (¬ p2027) := h40810;
    (Or.elim h26873 (fun q0 => (False.elim (u13 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u11))) (fun r12 => (False.elim (r12 u12)))))))))))))))))))))))))))))

theorem step53374 (p2027 p2088 p2122 p4078 p4170 p4340 p4501 : Prop)
    (h40810 : (¬ p2027))
    (h26874 : p2027 ∨ (¬ p2088) ∨ (¬ p2122) ∨ (¬ p4078) ∨ (¬ p4170) ∨ (¬ p4340) ∨ (¬ p4501))
    : (¬ p2088) ∨ (¬ p2122) ∨ (¬ p4078) ∨ (¬ p4170) ∨ (¬ p4340) ∨ (¬ p4501) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26874 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53375 (p2027 p2589 p2598 p3237 p3333 p3589 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h26875 : p2027 ∨ (¬ p2589) ∨ (¬ p2598) ∨ (¬ p3237) ∨ (¬ p3333) ∨ (¬ p3589) ∨ (¬ p5193))
    : (¬ p2589) ∨ (¬ p2598) ∨ (¬ p3237) ∨ (¬ p3333) ∨ (¬ p3589) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26875 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53376 (p2027 p2088 p2187 p4078 p4170 p4340 p4889 : Prop)
    (h40810 : (¬ p2027))
    (h26876 : p2027 ∨ (¬ p2088) ∨ (¬ p2187) ∨ (¬ p4078) ∨ (¬ p4170) ∨ (¬ p4340) ∨ (¬ p4889))
    : (¬ p2088) ∨ (¬ p2187) ∨ (¬ p4078) ∨ (¬ p4170) ∨ (¬ p4340) ∨ (¬ p4889) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26876 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53379 (p2027 p2656 p3389 p3868 p4256 p4383 p5564 : Prop)
    (h40810 : (¬ p2027))
    (h26879 : p2027 ∨ (¬ p2656) ∨ (¬ p3389) ∨ (¬ p3868) ∨ (¬ p4256) ∨ (¬ p4383) ∨ (¬ p5564))
    : (¬ p2656) ∨ (¬ p3389) ∨ (¬ p3868) ∨ (¬ p4256) ∨ (¬ p4383) ∨ (¬ p5564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2656 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26879 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53380 (p2002 p2027 p2187 p2307 p2387 p2765 p3822 : Prop)
    (h2162 : p2002)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h26881 : (¬ p2002) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2387) ∨ p2765 ∨ (¬ p3822))
    : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3822) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2002 := h2162;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h26881 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53381 (p1985 p2027 p2230 p2427 p2545 p2579 p3016 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h26883 : (¬ p1985) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2427) ∨ p2545 ∨ (¬ p2579) ∨ (¬ p3016))
    : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2579) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h26883 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53382 (p2027 p2104 p2373 p2406 p2459 p3379 p4340 p4736 p4902 : Prop)
    (h40810 : (¬ p2027))
    (h26884 : p2027 ∨ (¬ p2104) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p4340) ∨ (¬ p4736) ∨ (¬ p4902))
    : (¬ p2104) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p4340) ∨ (¬ p4736) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26884 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53383 (p2027 p2191 p2563 p2619 p4210 p4244 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h26885 : p2027 ∨ (¬ p2191) ∨ (¬ p2563) ∨ (¬ p2619) ∨ (¬ p4210) ∨ (¬ p4244) ∨ (¬ p4555))
    : (¬ p2191) ∨ (¬ p2563) ∨ (¬ p2619) ∨ (¬ p4210) ∨ (¬ p4244) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26885 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53387 (p2027 p2132 p2619 p3146 p3414 p3553 p4789 p5118 p5558 : Prop)
    (h40810 : (¬ p2027))
    (h26889 : p2027 ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4789) ∨ (¬ p5118) ∨ (¬ p5558))
    : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4789) ∨ (¬ p5118) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26889 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53388 (p2027 p2264 p2696 p2742 p3027 p3363 p3540 p3585 p4278 p4666 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h26893 : p2027 ∨ (¬ p2264) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4737))
    : (¬ p2264) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26893 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53390 (p1990 p2027 p2611 p2839 p2860 p3471 p3588 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h26895 : (¬ p1990) ∨ p2027 ∨ p2611 ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p3471) ∨ (¬ p3588))
    : (¬ p2839) ∨ (¬ p2860) ∨ (¬ p3471) ∨ (¬ p3588) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h26895 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53391 (p1975 p2027 p2765 p3051 p3246 p3370 p4107 p4173 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h26896 : (¬ p1975) ∨ p2027 ∨ p2765 ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3370) ∨ (¬ p4107) ∨ (¬ p4173))
    : (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3370) ∨ (¬ p4107) ∨ (¬ p4173) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h26896 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53393 (p2027 p2307 p2534 p2589 p2668 p3146 p3347 p3568 p4134 p4257 p4607 p4866 p5016 : Prop)
    (h40810 : (¬ p2027))
    (h26898 : p2027 ∨ (¬ p2307) ∨ (¬ p2534) ∨ (¬ p2589) ∨ (¬ p2668) ∨ (¬ p3146) ∨ (¬ p3347) ∨ (¬ p3568) ∨ (¬ p4134) ∨ (¬ p4257) ∨ (¬ p4607) ∨ (¬ p4866) ∨ (¬ p5016))
    : (¬ p2307) ∨ (¬ p2534) ∨ (¬ p2589) ∨ (¬ p2668) ∨ (¬ p3146) ∨ (¬ p3347) ∨ (¬ p3568) ∨ (¬ p4134) ∨ (¬ p4257) ∨ (¬ p4607) ∨ (¬ p4866) ∨ (¬ p5016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h26898 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step53395 (p2027 p2247 p2744 p3055 p3093 p3309 p3366 p3584 p3956 p4501 : Prop)
    (h40810 : (¬ p2027))
    (h26900 : p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4501))
    : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4501) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26900 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53396 (p2027 p2440 p3016 p4031 p4120 p4203 p4507 : Prop)
    (h40810 : (¬ p2027))
    (h26901 : p2027 ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4031) ∨ (¬ p4120) ∨ (¬ p4203) ∨ (¬ p4507))
    : (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4031) ∨ (¬ p4120) ∨ (¬ p4203) ∨ (¬ p4507) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26901 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53397 (p2027 p2363 p2534 p2819 p3573 p5225 : Prop)
    (h40810 : (¬ p2027))
    (h26903 : p2027 ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2819) ∨ (¬ p3573) ∨ (¬ p5225))
    : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2819) ∨ (¬ p3573) ∨ (¬ p5225) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26903 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53400 (p2027 p2230 p2246 p2440 p2608 p2663 p2744 p3083 p3591 p3923 p4596 : Prop)
    (h40810 : (¬ p2027))
    (h26907 : p2027 ∨ (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2440) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4596))
    : (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2440) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4596) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h26907 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53401 (p2027 p2088 p3591 p4238 p4261 p4371 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h26909 : p2027 ∨ (¬ p2088) ∨ (¬ p3591) ∨ (¬ p4238) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4521))
    : (¬ p2088) ∨ (¬ p3591) ∨ (¬ p4238) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26909 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53402 (p2027 p2248 p3166 p3256 p3588 p3659 p3692 p3954 p4902 : Prop)
    (h40810 : (¬ p2027))
    (h26911 : p2027 ∨ (¬ p2248) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3692) ∨ (¬ p3954) ∨ (¬ p4902))
    : (¬ p2248) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3692) ∨ (¬ p3954) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26911 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53404 (p1990 p2027 p2563 p2622 p2630 p2657 p2946 p4241 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h26913 : (¬ p1990) ∨ p2027 ∨ (¬ p2563) ∨ p2622 ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p4241))
    : (¬ p2563) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h26913 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53409 (p1982 p2027 p2148 p2156 p2373 p3146 p4110 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h26921 : (¬ p1982) ∨ p2027 ∨ p2148 ∨ (¬ p2156) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4110))
    : (¬ p2156) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2148) := h40865;
    (Or.elim h26921 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53410 (p2027 p2104 p2230 p2459 p2563 p3125 p3322 p4133 p4340 p4419 : Prop)
    (h40810 : (¬ p2027))
    (h26922 : p2027 ∨ (¬ p2104) ∨ (¬ p2230) ∨ (¬ p2459) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3322) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p4419))
    : (¬ p2104) ∨ (¬ p2230) ∨ (¬ p2459) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3322) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26922 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53411 (p2027 p2685 p3093 p3309 p3366 p3414 p3452 p3877 p4236 p4376 p4501 p4769 : Prop)
    (h40810 : (¬ p2027))
    (h26923 : p2027 ∨ (¬ p2685) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3452) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4501) ∨ (¬ p4769))
    : (¬ p2685) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3452) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4501) ∨ (¬ p4769) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h26923 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step53420 (p2027 p2499 p2922 p3956 p4501 p4710 : Prop)
    (h40810 : (¬ p2027))
    (h26936 : p2027 ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3956) ∨ (¬ p4501) ∨ (¬ p4710))
    : (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3956) ∨ (¬ p4501) ∨ (¬ p4710) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26936 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53421 (p1982 p2027 p2166 p2202 p2363 p2563 p4173 p4441 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h26937 : (¬ p1982) ∨ p2027 ∨ (¬ p2166) ∨ p2202 ∨ (¬ p2363) ∨ (¬ p2563) ∨ (¬ p4173) ∨ (¬ p4441))
    : (¬ p2166) ∨ (¬ p2363) ∨ (¬ p2563) ∨ (¬ p4173) ∨ (¬ p4441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h26937 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53427 (p2027 p2363 p3055 p3063 p3093 p3876 p4278 p4669 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h26943 : p2027 ∨ (¬ p2363) ∨ (¬ p3055) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4736))
    : (¬ p2363) ∨ (¬ p3055) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26943 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53434 (p2027 p2459 p2717 p3692 p4119 p4898 : Prop)
    (h40810 : (¬ p2027))
    (h26952 : p2027 ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4898))
    : (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4898) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4898 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26952 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53435 (p2027 p3055 p3366 p3631 p3687 p3821 p3959 p4357 p4749 : Prop)
    (h40810 : (¬ p2027))
    (h26955 : p2027 ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3821) ∨ (¬ p3959) ∨ (¬ p4357) ∨ (¬ p4749))
    : (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3821) ∨ (¬ p3959) ∨ (¬ p4357) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26955 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53438 (p2027 p2246 p2264 p2459 p2608 p2663 p2744 p3389 p3740 p3834 p4351 p5118 p5693 : Prop)
    (h40810 : (¬ p2027))
    (h26960 : p2027 ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3389) ∨ (¬ p3740) ∨ (¬ p3834) ∨ (¬ p4351) ∨ (¬ p5118) ∨ (¬ p5693))
    : (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3389) ∨ (¬ p3740) ∨ (¬ p3834) ∨ (¬ p4351) ∨ (¬ p5118) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4351 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h26960 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step53441 (p1982 p2027 p2765 p3105 p3680 p3758 p4444 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h26963 : (¬ p1982) ∨ p2027 ∨ p2765 ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p3758) ∨ (¬ p4444))
    : (¬ p3105) ∨ (¬ p3680) ∨ (¬ p3758) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h26963 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53442 (p2027 p3426 p3434 p4107 p4358 p4501 : Prop)
    (h40810 : (¬ p2027))
    (h26964 : p2027 ∨ (¬ p3426) ∨ (¬ p3434) ∨ (¬ p4107) ∨ (¬ p4358) ∨ (¬ p4501))
    : (¬ p3426) ∨ (¬ p3434) ∨ (¬ p4107) ∨ (¬ p4358) ∨ (¬ p4501) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3426 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26964 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53443 (p1997 p2027 p2459 p2534 p2542 p2633 p4256 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h26965 : (¬ p1997) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2542) ∨ p2633 ∨ (¬ p4256))
    : (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2542) ∨ (¬ p4256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h26965 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53444 (p2027 p2122 p2246 p2313 p2744 p3286 p3506 p3645 p3917 p4198 p4444 p4604 p4874 : Prop)
    (h40810 : (¬ p2027))
    (h26966 : p2027 ∨ (¬ p2122) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2744) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3645) ∨ (¬ p3917) ∨ (¬ p4198) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p4874))
    : (¬ p2122) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2744) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3645) ∨ (¬ p3917) ∨ (¬ p4198) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p4874) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h26966 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step53445 (p1983 p2027 p2417 p3578 p3644 p3969 p5558 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h26967 : (¬ p1983) ∨ p2027 ∨ (¬ p2417) ∨ p3578 ∨ (¬ p3644) ∨ (¬ p3969) ∨ (¬ p5558))
    : (¬ p2417) ∨ (¬ p3644) ∨ (¬ p3969) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3578) := h40900;
    (Or.elim h26967 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53446 (p1994 p2027 p2406 p2440 p2633 p3347 p3540 p3644 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h26968 : (¬ p1994) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2440) ∨ p2633 ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3644))
    : (¬ p2406) ∨ (¬ p2440) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h26968 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53448 (p2027 p2797 p3567 p4173 p4315 p4356 p4957 : Prop)
    (h40810 : (¬ p2027))
    (h26970 : p2027 ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p4173) ∨ (¬ p4315) ∨ (¬ p4356) ∨ (¬ p4957))
    : (¬ p2797) ∨ (¬ p3567) ∨ (¬ p4173) ∨ (¬ p4315) ∨ (¬ p4356) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26970 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53450 (p2027 p2156 p2891 p3556 p3952 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h26972 : p2027 ∨ (¬ p2156) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3952) ∨ (¬ p4960))
    : (¬ p2156) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3952) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26972 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53456 (p2027 p2140 p2829 p3583 p3646 p4185 : Prop)
    (h40810 : (¬ p2027))
    (h26978 : p2027 ∨ (¬ p2140) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p4185))
    : (¬ p2140) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p4185) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2140 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26978 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53458 (p1982 p2027 p2169 p3461 p3483 p4358 p4444 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h26980 : (¬ p1982) ∨ p2027 ∨ p2169 ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p4358) ∨ (¬ p4444))
    : (¬ p3461) ∨ (¬ p3483) ∨ (¬ p4358) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h26980 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53459 (p2027 p2459 p3438 p3449 p3834 p4832 : Prop)
    (h40810 : (¬ p2027))
    (h26981 : p2027 ∨ (¬ p2459) ∨ (¬ p3438) ∨ (¬ p3449) ∨ (¬ p3834) ∨ (¬ p4832))
    : (¬ p2459) ∨ (¬ p3438) ∨ (¬ p3449) ∨ (¬ p3834) ∨ (¬ p4832) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4832 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26981 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53460 (p2027 p2132 p2192 p2780 p4428 p4878 : Prop)
    (h40810 : (¬ p2027))
    (h26982 : p2027 ∨ (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2780) ∨ (¬ p4428) ∨ (¬ p4878))
    : (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2780) ∨ (¬ p4428) ∨ (¬ p4878) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h26982 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53461 (p2027 p2122 p2248 p2542 p2563 p2651 p3549 p3591 p4401 : Prop)
    (h40810 : (¬ p2027))
    (h26983 : p2027 ∨ (¬ p2122) ∨ (¬ p2248) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2651) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4401))
    : (¬ p2122) ∨ (¬ p2248) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2651) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4401) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26983 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53462 (p2027 p2248 p3286 p3506 p3555 p3744 p4173 p4381 p4625 : Prop)
    (h40810 : (¬ p2027))
    (h26984 : p2027 ∨ (¬ p2248) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4381) ∨ (¬ p4625))
    : (¬ p2248) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4381) ∨ (¬ p4625) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26984 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53465 (p2027 p2156 p2406 p3952 p4109 p4700 p4814 : Prop)
    (h40810 : (¬ p2027))
    (h26987 : p2027 ∨ (¬ p2156) ∨ (¬ p2406) ∨ (¬ p3952) ∨ (¬ p4109) ∨ (¬ p4700) ∨ (¬ p4814))
    : (¬ p2156) ∨ (¬ p2406) ∨ (¬ p3952) ∨ (¬ p4109) ∨ (¬ p4700) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h26987 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53466 (p1994 p2027 p2622 p2743 p3367 p3422 p3574 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h26988 : (¬ p1994) ∨ p2027 ∨ p2622 ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3422) ∨ (¬ p3574))
    : (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3422) ∨ (¬ p3574) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h26988 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53467 (p1994 p2027 p2573 p2764 p3346 p3574 p4425 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h26989 : (¬ p1994) ∨ p2027 ∨ (¬ p2573) ∨ p2764 ∨ (¬ p3346) ∨ (¬ p3574) ∨ (¬ p4425))
    : (¬ p2573) ∨ (¬ p3346) ∨ (¬ p3574) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h26989 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53469 (p2027 p2132 p2753 p2870 p3246 p3379 p3860 p3950 p4261 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h26993 : p2027 ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p5216))
    : (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h26993 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53470 (p1988 p2027 p2323 p2807 p3506 p3572 p3755 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h26994 : (¬ p1988) ∨ p2027 ∨ p2323 ∨ (¬ p2807) ∨ (¬ p3506) ∨ (¬ p3572) ∨ (¬ p3755))
    : (¬ p2807) ∨ (¬ p3506) ∨ (¬ p3572) ∨ (¬ p3755) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h26994 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53471 (p2027 p2579 p2696 p3115 p3136 p3956 p4347 p4450 p4729 : Prop)
    (h40810 : (¬ p2027))
    (h26997 : p2027 ∨ (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p4729))
    : (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p4729) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h26997 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53473 (p2027 p3178 p3877 p3998 p4790 p5600 : Prop)
    (h40810 : (¬ p2027))
    (h27000 : p2027 ∨ (¬ p3178) ∨ (¬ p3877) ∨ (¬ p3998) ∨ (¬ p4790) ∨ (¬ p5600))
    : (¬ p3178) ∨ (¬ p3877) ∨ (¬ p3998) ∨ (¬ p4790) ∨ (¬ p5600) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3178 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27000 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53475 (p2027 p2437 p2651 p3364 p3876 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h27004 : p2027 ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3364) ∨ (¬ p3876) ∨ (¬ p4790))
    : (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3364) ∨ (¬ p3876) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27004 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53476 (p2027 p2579 p2744 p3212 p3347 p3370 p3422 p3680 p4257 p4365 p4381 p4641 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h27005 : p2027 ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3212) ∨ (¬ p3347) ∨ (¬ p3370) ∨ (¬ p3422) ∨ (¬ p3680) ∨ (¬ p4257) ∨ (¬ p4365) ∨ (¬ p4381) ∨ (¬ p4641) ∨ (¬ p5160))
    : (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3212) ∨ (¬ p3347) ∨ (¬ p3370) ∨ (¬ p3422) ∨ (¬ p3680) ∨ (¬ p4257) ∨ (¬ p4365) ∨ (¬ p4381) ∨ (¬ p4641) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h27005 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step53481 (p1977 p2027 p2299 p2396 p2633 p2996 p3577 p4155 p4324 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h27012 : (¬ p1977) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2396) ∨ p2633 ∨ (¬ p2996) ∨ (¬ p3577) ∨ (¬ p4155) ∨ (¬ p4324))
    : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2996) ∨ (¬ p3577) ∨ (¬ p4155) ∨ (¬ p4324) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1977 := h2137;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2633) := h40879;
    (Or.elim h27012 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53487 (p2027 p2313 p2505 p2608 p3309 p4376 p5015 : Prop)
    (h40810 : (¬ p2027))
    (h27019 : p2027 ∨ (¬ p2313) ∨ (¬ p2505) ∨ (¬ p2608) ∨ (¬ p3309) ∨ (¬ p4376) ∨ (¬ p5015))
    : (¬ p2313) ∨ (¬ p2505) ∨ (¬ p2608) ∨ (¬ p3309) ∨ (¬ p4376) ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27019 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53488 (p1987 p2027 p2662 p2810 p2881 p2938 p3540 p3644 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h27020 : (¬ p1987) ∨ p2027 ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p2881) ∨ p2938 ∨ (¬ p3540) ∨ (¬ p3644))
    : (¬ p2662) ∨ (¬ p2810) ∨ (¬ p2881) ∨ (¬ p3540) ∨ (¬ p3644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2938) := h40888;
    (Or.elim h27020 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53490 (p2027 p2331 p2727 p2810 p4154 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h27022 : p2027 ∨ (¬ p2331) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p4154) ∨ (¬ p4790))
    : (¬ p2331) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p4154) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27022 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53493 (p2027 p2741 p2839 p2870 p3848 p4040 p4204 p5043 : Prop)
    (h40810 : (¬ p2027))
    (h27026 : p2027 ∨ (¬ p2741) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3848) ∨ (¬ p4040) ∨ (¬ p4204) ∨ (¬ p5043))
    : (¬ p2741) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3848) ∨ (¬ p4040) ∨ (¬ p4204) ∨ (¬ p5043) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2741 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h27026 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step53494 (p1996 p2027 p2499 p2922 p3008 p3516 p3575 p3947 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h27027 : (¬ p1996) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p2922) ∨ p3008 ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p3947))
    : (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1996 := h2156;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3008) := h40891;
    (Or.elim h27027 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53495 (p2027 p3146 p3166 p3292 p3438 p3853 p5063 : Prop)
    (h40810 : (¬ p2027))
    (h27028 : p2027 ∨ (¬ p3146) ∨ (¬ p3166) ∨ (¬ p3292) ∨ (¬ p3438) ∨ (¬ p3853) ∨ (¬ p5063))
    : (¬ p3146) ∨ (¬ p3166) ∨ (¬ p3292) ∨ (¬ p3438) ∨ (¬ p3853) ∨ (¬ p5063) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27028 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53496 (p1994 p2027 p2630 p2766 p3551 p3572 p4155 p4348 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h27029 : (¬ p1994) ∨ p2027 ∨ (¬ p2630) ∨ p2766 ∨ (¬ p3551) ∨ (¬ p3572) ∨ (¬ p4155) ∨ (¬ p4348))
    : (¬ p2630) ∨ (¬ p3551) ∨ (¬ p3572) ∨ (¬ p4155) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h27029 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53497 (p2027 p2132 p2860 p3737 p3817 p4366 p4381 p4733 p5250 : Prop)
    (h40810 : (¬ p2027))
    (h27030 : p2027 ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3737) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4381) ∨ (¬ p4733) ∨ (¬ p5250))
    : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3737) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4381) ∨ (¬ p4733) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27030 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53499 (p2027 p2248 p2331 p2928 p3005 p3452 p3644 p4195 p4550 : Prop)
    (h40810 : (¬ p2027))
    (h27032 : p2027 ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2928) ∨ (¬ p3005) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p4195) ∨ (¬ p4550))
    : (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2928) ∨ (¬ p3005) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p4195) ∨ (¬ p4550) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27032 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53501 (p2027 p2476 p2901 p2946 p3905 p4129 p4340 p4444 p4786 p4826 p5373 : Prop)
    (h40810 : (¬ p2027))
    (h27034 : p2027 ∨ (¬ p2476) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3905) ∨ (¬ p4129) ∨ (¬ p4340) ∨ (¬ p4444) ∨ (¬ p4786) ∨ (¬ p4826) ∨ (¬ p5373))
    : (¬ p2476) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3905) ∨ (¬ p4129) ∨ (¬ p4340) ∨ (¬ p4444) ∨ (¬ p4786) ∨ (¬ p4826) ∨ (¬ p5373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27034 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53504 (p2027 p2245 p2363 p2657 p2774 p2819 p2928 p3487 p4278 p4669 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h27038 : p2027 ∨ (¬ p2245) ∨ (¬ p2363) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2928) ∨ (¬ p3487) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4733))
    : (¬ p2245) ∨ (¬ p2363) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2928) ∨ (¬ p3487) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27038 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53505 (p1991 p2938 p3414 p4280 : Prop)
    (h2151 : p1991)
    (h40888 : (¬ p2938))
    (h27039 : (¬ p1991) ∨ p2938 ∨ (¬ p3414) ∨ p4280)
    : (¬ p3414) ∨ p4280 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3414 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4280) := (fun h => hn (Or.inr h));
    let u2 : p1991 := h2151;
    let u3 : (¬ p2938) := h40888;
    (Or.elim h27039 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step53506 (p2027 p2299 p2319 p2341 p2748 p2779 p2829 p3365 p3662 p4320 p4559 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h27040 : p2027 ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2748) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p3662) ∨ (¬ p4320) ∨ (¬ p4559) ∨ (¬ p4734))
    : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2748) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p3662) ∨ (¬ p4320) ∨ (¬ p4559) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h27040 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step53509 (p2027 p2245 p2299 p2657 p2727 p2881 p2996 p3051 p4361 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h27044 : p2027 ∨ (¬ p2245) ∨ (¬ p2299) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2881) ∨ (¬ p2996) ∨ (¬ p3051) ∨ (¬ p4361) ∨ (¬ p4521))
    : (¬ p2245) ∨ (¬ p2299) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2881) ∨ (¬ p2996) ∨ (¬ p3051) ∨ (¬ p4361) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27044 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53510 (p2027 p2901 p3946 p3952 p4140 p4356 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h27045 : p2027 ∨ (¬ p2901) ∨ (¬ p3946) ∨ (¬ p3952) ∨ (¬ p4140) ∨ (¬ p4356) ∨ (¬ p4620))
    : (¬ p2901) ∨ (¬ p3946) ∨ (¬ p3952) ∨ (¬ p4140) ∨ (¬ p4356) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27045 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53511 (p2027 p2534 p2657 p3366 p3399 p3555 p3631 p3950 p4236 p4256 p4377 : Prop)
    (h40810 : (¬ p2027))
    (h27048 : p2027 ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4256) ∨ (¬ p4377))
    : (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4256) ∨ (¬ p4377) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27048 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53512 (p2027 p2307 p3717 p3743 p3822 p4193 p5449 : Prop)
    (h40810 : (¬ p2027))
    (h27049 : p2027 ∨ (¬ p2307) ∨ (¬ p3717) ∨ (¬ p3743) ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p5449))
    : (¬ p2307) ∨ (¬ p3717) ∨ (¬ p3743) ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p5449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27049 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53514 (p2027 p2406 p2589 p2928 p3201 p4727 : Prop)
    (h40810 : (¬ p2027))
    (h27051 : p2027 ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2928) ∨ (¬ p3201) ∨ (¬ p4727))
    : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2928) ∨ (¬ p3201) ∨ (¬ p4727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27051 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53516 (p2027 p2177 p2254 p2657 p3093 p3309 p3683 p3876 p4278 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h27053 : p2027 ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3683) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4666))
    : (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3683) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27053 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53518 (p2001 p2027 p2156 p2252 p2462 p2619 p2657 p2750 p3125 p3370 p3371 p3742 p3917 p4193 p4278 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h27056 : (¬ p2001) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p2252) ∨ p2462 ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3125) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3742) ∨ (¬ p3917) ∨ (¬ p4193) ∨ (¬ p4278))
    : (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3125) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3742) ∨ (¬ p3917) ∨ (¬ p4193) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2001 := h2161;
    let u13 : (¬ p2027) := h40810;
    let u14 : (¬ p2462) := h40875;
    (Or.elim h27056 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u13 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u14 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u8))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u9))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u10))) (fun r13 => (False.elim (r13 u11)))))))))))))))))))))))))))))))

theorem step53524 (p2027 p2230 p2427 p2608 p3519 p3834 p4029 p4129 p4376 p4826 p5387 : Prop)
    (h40810 : (¬ p2027))
    (h27064 : p2027 ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3834) ∨ (¬ p4029) ∨ (¬ p4129) ∨ (¬ p4376) ∨ (¬ p4826) ∨ (¬ p5387))
    : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3834) ∨ (¬ p4029) ∨ (¬ p4129) ∨ (¬ p4376) ∨ (¬ p4826) ∨ (¬ p5387) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4029 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27064 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53525 (p2027 p2963 p3324 p3366 p3399 p3452 p3631 p3950 p4236 p4347 p4376 : Prop)
    (h40810 : (¬ p2027))
    (h27065 : p2027 ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4347) ∨ (¬ p4376))
    : (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4347) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27065 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53526 (p1991 p2027 p2313 p2766 p3941 p3955 p3983 p4348 p5580 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h27066 : (¬ p1991) ∨ p2027 ∨ (¬ p2313) ∨ p2766 ∨ (¬ p3941) ∨ (¬ p3955) ∨ (¬ p3983) ∨ (¬ p4348) ∨ (¬ p5580))
    : (¬ p2313) ∨ (¬ p3941) ∨ (¬ p3955) ∨ (¬ p3983) ∨ (¬ p4348) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1991 := h2151;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2766) := h40884;
    (Or.elim h27066 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53529 (p2027 p2230 p2427 p2753 p3365 p3519 p3877 p4129 p4376 p5560 p5600 : Prop)
    (h40810 : (¬ p2027))
    (h27069 : p2027 ∨ (¬ p2230) ∨ (¬ p2427) ∨ p2753 ∨ (¬ p3365) ∨ (¬ p3519) ∨ (¬ p3877) ∨ (¬ p4129) ∨ (¬ p4376) ∨ (¬ p5560) ∨ (¬ p5600))
    : (¬ p2230) ∨ (¬ p2427) ∨ p2753 ∨ (¬ p3365) ∨ (¬ p3519) ∨ (¬ p3877) ∨ (¬ p4129) ∨ (¬ p4376) ∨ (¬ p5560) ∨ (¬ p5600) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2753) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5560 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27069 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53530 (p2027 p2307 p2387 p2668 p3097 p4560 : Prop)
    (h40810 : (¬ p2027))
    (h27071 : p2027 ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p3097) ∨ (¬ p4560))
    : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p3097) ∨ (¬ p4560) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4560 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27071 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53532 (p2027 p2143 p2751 p2901 p2992 p3556 p4392 : Prop)
    (h40810 : (¬ p2027))
    (h27073 : p2027 ∨ (¬ p2143) ∨ (¬ p2751) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3556) ∨ (¬ p4392))
    : (¬ p2143) ∨ (¬ p2751) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3556) ∨ (¬ p4392) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27073 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53533 (p2027 p2751 p2901 p2992 p4244 p4392 : Prop)
    (h40810 : (¬ p2027))
    (h27074 : p2027 ∨ (¬ p2751) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4244) ∨ (¬ p4392))
    : (¬ p2751) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4244) ∨ (¬ p4392) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27074 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53537 (p2027 p2146 p2341 p3570 p4244 p4988 : Prop)
    (h40810 : (¬ p2027))
    (h27080 : p2027 ∨ (¬ p2146) ∨ (¬ p2341) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4988))
    : (¬ p2146) ∨ (¬ p2341) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27080 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53540 (p1986 p2027 p2611 p2696 p2741 p3136 p3367 p3662 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h27085 : (¬ p1986) ∨ p2027 ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2741) ∨ (¬ p3136) ∨ (¬ p3367) ∨ (¬ p3662))
    : (¬ p2696) ∨ (¬ p2741) ∨ (¬ p3136) ∨ (¬ p3367) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1986 := h2146;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h27085 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53543 (p2027 p2341 p3570 p3575 p3741 p4320 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h27089 : p2027 ∨ (¬ p2341) ∨ (¬ p3570) ∨ (¬ p3575) ∨ (¬ p3741) ∨ (¬ p4320) ∨ (¬ p4702))
    : (¬ p2341) ∨ (¬ p3570) ∨ (¬ p3575) ∨ (¬ p3741) ∨ (¬ p4320) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27089 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53546 (p1977 p2027 p2331 p2938 p2952 p4154 p4320 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h27092 : (¬ p1977) ∨ p2027 ∨ (¬ p2331) ∨ p2938 ∨ (¬ p2952) ∨ (¬ p4154) ∨ (¬ p4320))
    : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p4154) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h27092 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53547 (p1987 p2598 p2699 p3589 p4749 : Prop)
    (h2147 : p1987)
    (h40881 : (¬ p2699))
    (h27093 : (¬ p1987) ∨ (¬ p2598) ∨ p2699 ∨ (¬ p3589) ∨ p4749)
    : (¬ p2598) ∨ (¬ p3589) ∨ p4749 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4749) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p1987 := h2147;
    let u4 : (¬ p2699) := h40881;
    (Or.elim h27093 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step53551 (p2027 p2177 p2254 p2598 p2707 p3414 p3553 p3585 p3589 p4473 : Prop)
    (h40810 : (¬ p2027))
    (h27097 : p2027 ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4473))
    : (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4473) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27097 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53552 (p2005 p2027 p2611 p2727 p2946 p3016 p3662 p4117 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h27100 : (¬ p2005) ∨ p2027 ∨ p2611 ∨ (¬ p2727) ∨ (¬ p2946) ∨ (¬ p3016) ∨ (¬ p3662) ∨ (¬ p4117))
    : (¬ p2727) ∨ (¬ p2946) ∨ (¬ p3016) ∨ (¬ p3662) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2005 := h2165;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h27100 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53553 (p1975 p2027 p2230 p2493 p2553 p2766 p3238 p3365 p3877 p4079 p4118 p4736 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h27101 : (¬ p1975) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2493) ∨ (¬ p2553) ∨ p2766 ∨ (¬ p3238) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4079) ∨ (¬ p4118) ∨ (¬ p4736))
    : (¬ p2230) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p3238) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4079) ∨ (¬ p4118) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p1975 := h2135;
    let u10 : (¬ p2027) := h40810;
    let u11 : (¬ p2766) := h40884;
    (Or.elim h27101 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u11 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (False.elim (r10 u8)))))))))))))))))))))))))

theorem step53555 (p2005 p2027 p2493 p3193 p3767 p3783 p4425 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40904 : (¬ p3783))
    (h27103 : (¬ p2005) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p3193) ∨ (¬ p3767) ∨ p3783 ∨ (¬ p4425))
    : (¬ p2493) ∨ (¬ p3193) ∨ (¬ p3767) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3783) := h40904;
    (Or.elim h27103 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53566 (p2005 p2027 p2114 p2588 p3093 p3309 p3954 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h27115 : (¬ p2005) ∨ p2027 ∨ p2114 ∨ (¬ p2588) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3954))
    : (¬ p2588) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h27115 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53571 (p2027 p2383 p2584 p3584 p3956 p4730 : Prop)
    (h40810 : (¬ p2027))
    (h27121 : p2027 ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4730))
    : (¬ p2383) ∨ (¬ p2584) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27121 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53576 (p2005 p2284 p2388 p3958 : Prop)
    (h2165 : p2005)
    (h40873 : (¬ p2388))
    (h27129 : (¬ p2005) ∨ (¬ p2284) ∨ p2388 ∨ p3958)
    : (¬ p2284) ∨ p3958 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3958) := (fun h => hn (Or.inr h));
    let u2 : p2005 := h2165;
    let u3 : (¬ p2388) := h40873;
    (Or.elim h27129 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step53577 (p2027 p2138 p2241 p2641 p2668 p3097 p3758 p4405 p4736 : Prop)
    (h40810 : (¬ p2027))
    (h27131 : p2027 ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3097) ∨ (¬ p3758) ∨ (¬ p4405) ∨ (¬ p4736))
    : (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3097) ∨ (¬ p3758) ∨ (¬ p4405) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27131 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53580 (p1987 p2027 p2114 p2241 p2992 p3954 p4315 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h27135 : (¬ p1987) ∨ p2027 ∨ p2114 ∨ (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3954) ∨ (¬ p4315))
    : (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3954) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h27135 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53584 (p2027 p3238 p3434 p3452 p3471 p4107 p4235 p4559 p4733 : Prop)
    (h40810 : (¬ p2027))
    (h27139 : p2027 ∨ (¬ p3238) ∨ (¬ p3434) ∨ (¬ p3452) ∨ (¬ p3471) ∨ (¬ p4107) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4733))
    : (¬ p3238) ∨ (¬ p3434) ∨ (¬ p3452) ∨ (¬ p3471) ∨ (¬ p4107) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3238 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27139 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53588 (p1988 p2027 p2156 p2699 p2972 p3461 p4172 p4173 p5045 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h27149 : (¬ p1988) ∨ p2027 ∨ (¬ p2156) ∨ p2699 ∨ (¬ p2972) ∨ (¬ p3461) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p5045))
    : (¬ p2156) ∨ (¬ p2972) ∨ (¬ p3461) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p5045) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1988 := h2148;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2699) := h40881;
    (Or.elim h27149 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53590 (p2027 p2651 p3016 p3364 p3584 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h27151 : p2027 ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3364) ∨ (¬ p3584) ∨ (¬ p4790))
    : (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3364) ∨ (¬ p3584) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27151 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53596 (p1976 p2027 p2765 p2911 p3425 p3659 p3741 p4110 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h27157 : (¬ p1976) ∨ p2027 ∨ p2765 ∨ (¬ p2911) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3741) ∨ (¬ p4110))
    : (¬ p2911) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3741) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h27157 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53597 (p2027 p2255 p2352 p2459 p2493 p2651 p2996 p3857 p3961 p4116 p4133 p4155 : Prop)
    (h40810 : (¬ p2027))
    (h27158 : p2027 ∨ (¬ p2255) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2493) ∨ (¬ p2651) ∨ (¬ p2996) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4116) ∨ (¬ p4133) ∨ (¬ p4155))
    : (¬ p2255) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2493) ∨ (¬ p2651) ∨ (¬ p2996) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4116) ∨ (¬ p4133) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h27158 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step53598 (p2027 p2493 p2553 p4116 p4256 p4432 p4501 : Prop)
    (h40810 : (¬ p2027))
    (h27160 : p2027 ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p4116) ∨ (¬ p4256) ∨ (¬ p4432) ∨ (¬ p4501))
    : (¬ p2493) ∨ (¬ p2553) ∨ (¬ p4116) ∨ (¬ p4256) ∨ (¬ p4432) ∨ (¬ p4501) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27160 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53604 (p2027 p2166 p2255 p2667 p2946 p3412 p3946 p3969 p4154 p4191 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h27167 : p2027 ∨ (¬ p2166) ∨ (¬ p2255) ∨ (¬ p2667) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3946) ∨ (¬ p3969) ∨ (¬ p4154) ∨ (¬ p4191) ∨ (¬ p5119))
    : (¬ p2166) ∨ (¬ p2255) ∨ (¬ p2667) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3946) ∨ (¬ p3969) ∨ (¬ p4154) ∨ (¬ p4191) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27167 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53607 (p2027 p2870 p2992 p2996 p3691 p4155 p5053 : Prop)
    (h40810 : (¬ p2027))
    (h27170 : p2027 ∨ (¬ p2870) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3691) ∨ (¬ p4155) ∨ (¬ p5053))
    : (¬ p2870) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3691) ∨ (¬ p4155) ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27170 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53610 (p2027 p2459 p3189 p3848 p4550 p5107 : Prop)
    (h40810 : (¬ p2027))
    (h27173 : p2027 ∨ (¬ p2459) ∨ (¬ p3189) ∨ (¬ p3848) ∨ (¬ p4550) ∨ (¬ p5107))
    : (¬ p2459) ∨ (¬ p3189) ∨ (¬ p3848) ∨ (¬ p4550) ∨ (¬ p5107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27173 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53612 (p1980 p2331 p2622 p4787 : Prop)
    (h2140 : p1980)
    (h40878 : (¬ p2622))
    (h27175 : (¬ p1980) ∨ (¬ p2331) ∨ p2622 ∨ p4787)
    : (¬ p2331) ∨ p4787 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4787) := (fun h => hn (Or.inr h));
    let u2 : p1980 := h2140;
    let u3 : (¬ p2622) := h40878;
    (Or.elim h27175 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step53613 (p1988 p2027 p2230 p2622 p2630 p2982 p3519 p3680 p4116 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h27176 : (¬ p1988) ∨ p2027 ∨ (¬ p2230) ∨ p2622 ∨ (¬ p2630) ∨ (¬ p2982) ∨ (¬ p3519) ∨ (¬ p3680) ∨ (¬ p4116))
    : (¬ p2230) ∨ (¬ p2630) ∨ (¬ p2982) ∨ (¬ p3519) ∨ (¬ p3680) ∨ (¬ p4116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1988 := h2148;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2622) := h40878;
    (Or.elim h27176 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53615 (p2000 p2027 p2589 p2633 p2850 p3644 p3876 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h27178 : (¬ p2000) ∨ p2027 ∨ (¬ p2589) ∨ p2633 ∨ (¬ p2850) ∨ (¬ p3644) ∨ (¬ p3876))
    : (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3644) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2000 := h2160;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h27178 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53616 (p2027 p2553 p2774 p3425 p4471 p5222 : Prop)
    (h40810 : (¬ p2027))
    (h27179 : p2027 ∨ (¬ p2553) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p4471) ∨ (¬ p5222))
    : (¬ p2553) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p4471) ∨ (¬ p5222) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27179 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53619 (p2027 p2187 p2363 p3857 p4197 p4486 : Prop)
    (h40810 : (¬ p2027))
    (h27182 : p2027 ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4486))
    : (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4486) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27182 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53620 (p1991 p2027 p2202 p2657 p3422 p3574 p3684 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h27184 : (¬ p1991) ∨ p2027 ∨ p2202 ∨ (¬ p2657) ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p3684))
    : (¬ p2657) ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p3684) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h27184 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53623 (p1982 p2027 p2274 p2363 p2668 p2765 p3568 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h27187 : (¬ p1982) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2363) ∨ (¬ p2668) ∨ p2765 ∨ (¬ p3568))
    : (¬ p2274) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h27187 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53624 (p2027 p2264 p2751 p3027 p3364 p3659 p3686 : Prop)
    (h40810 : (¬ p2027))
    (h27188 : p2027 ∨ (¬ p2264) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3364) ∨ (¬ p3659) ∨ (¬ p3686))
    : (¬ p2264) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3364) ∨ (¬ p3659) ∨ (¬ p3686) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3686 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27188 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53634 (p1990 p2027 p2138 p2284 p2696 p3136 p3474 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h27203 : (¬ p1990) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2284) ∨ (¬ p2696) ∨ (¬ p3136) ∨ p3474)
    : (¬ p2138) ∨ (¬ p2284) ∨ (¬ p2696) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3474) := h40898;
    (Or.elim h27203 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step53641 (p1996 p2027 p2622 p3365 p3434 p3471 p3947 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h27211 : (¬ p1996) ∨ p2027 ∨ p2622 ∨ (¬ p3365) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3947))
    : (¬ p3365) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1996 := h2156;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h27211 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53642 (p2027 p2396 p2553 p3956 p4138 p4668 : Prop)
    (h40810 : (¬ p2027))
    (h27212 : p2027 ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4668))
    : (¬ p2396) ∨ (¬ p2553) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27212 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53648 (p2027 p2542 p2589 p2655 p2807 p4652 : Prop)
    (h40810 : (¬ p2027))
    (h27220 : p2027 ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p4652))
    : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27220 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53652 (p2027 p2252 p2476 p2534 p2655 p2750 p3063 p3093 p3146 p3954 p4134 : Prop)
    (h40810 : (¬ p2027))
    (h27224 : p2027 ∨ (¬ p2252) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3954) ∨ (¬ p4134))
    : (¬ p2252) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3954) ∨ (¬ p4134) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27224 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53653 (p1981 p2027 p2114 p2187 p2192 p2210 p3954 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h27225 : (¬ p1981) ∨ p2027 ∨ p2114 ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3954))
    : (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h27225 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53655 (p1986 p2027 p2589 p2765 p3389 p3876 p4110 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h27228 : (¬ p1986) ∨ p2027 ∨ (¬ p2589) ∨ p2765 ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4110))
    : (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1986 := h2146;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h27228 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53661 (p2027 p2352 p3399 p3631 p3923 p3954 p4137 p4625 p4870 : Prop)
    (h40810 : (¬ p2027))
    (h27235 : p2027 ∨ (¬ p2352) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3923) ∨ (¬ p3954) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4870))
    : (¬ p2352) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3923) ∨ (¬ p3954) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27235 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53664 (p2027 p2518 p2743 p3541 p3874 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h27239 : p2027 ∨ (¬ p2518) ∨ (¬ p2743) ∨ (¬ p3541) ∨ (¬ p3874) ∨ (¬ p4752))
    : (¬ p2518) ∨ (¬ p2743) ∨ (¬ p3541) ∨ (¬ p3874) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27239 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53665 (p2027 p2248 p2881 p2901 p2928 p2946 p3452 p4278 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h27240 : p2027 ∨ (¬ p2248) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2928) ∨ (¬ p2946) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4666))
    : (¬ p2248) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2928) ∨ (¬ p2946) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27240 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53668 (p2027 p3083 p3570 p3742 p4404 p4647 : Prop)
    (h40810 : (¬ p2027))
    (h27243 : p2027 ∨ (¬ p3083) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4404) ∨ (¬ p4647))
    : (¬ p3083) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4404) ∨ (¬ p4647) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27243 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53669 (p2027 p2573 p3222 p3238 p3346 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h27244 : p2027 ∨ (¬ p2573) ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3346) ∨ (¬ p4717))
    : (¬ p2573) ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3346) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27244 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53670 (p2027 p2563 p3343 p3952 p4700 p4953 : Prop)
    (h40810 : (¬ p2027))
    (h27245 : p2027 ∨ (¬ p2563) ∨ (¬ p3343) ∨ (¬ p3952) ∨ (¬ p4700) ∨ (¬ p4953))
    : (¬ p2563) ∨ (¬ p3343) ∨ (¬ p3952) ∨ (¬ p4700) ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27245 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53671 (p2027 p2563 p3222 p4173 p4202 p4953 : Prop)
    (h40810 : (¬ p2027))
    (h27246 : p2027 ∨ (¬ p2563) ∨ (¬ p3222) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4953))
    : (¬ p2563) ∨ (¬ p3222) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27246 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53672 (p1990 p2027 p2860 p2964 p3276 p4322 p4385 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40889 : (¬ p2964))
    (h27247 : (¬ p1990) ∨ p2027 ∨ (¬ p2860) ∨ p2964 ∨ (¬ p3276) ∨ (¬ p4322) ∨ (¬ p4385))
    : (¬ p2860) ∨ (¬ p3276) ∨ (¬ p4322) ∨ (¬ p4385) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2964) := h40889;
    (Or.elim h27247 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53674 (p1983 p2027 p2202 p2563 p3051 p3246 p3646 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h27252 : (¬ p1983) ∨ p2027 ∨ p2202 ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3646))
    : (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h27252 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53675 (p1983 p2027 p2202 p2396 p2440 p3055 p3471 p4343 p4475 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h27253 : (¬ p1983) ∨ p2027 ∨ p2202 ∨ (¬ p2396) ∨ (¬ p2440) ∨ (¬ p3055) ∨ (¬ p3471) ∨ (¬ p4343) ∨ (¬ p4475))
    : (¬ p2396) ∨ (¬ p2440) ∨ (¬ p3055) ∨ (¬ p3471) ∨ (¬ p4343) ∨ (¬ p4475) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1983 := h2143;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2202) := h40867;
    (Or.elim h27253 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53676 (p1982 p2027 p2202 p2459 p2911 p2922 p3238 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h27255 : (¬ p1982) ∨ p2027 ∨ p2202 ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3238))
    : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3238) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h27255 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53677 (p1984 p2027 p2177 p2247 p2996 p2997 p3553 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h27256 : (¬ p1984) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2996) ∨ p2997 ∨ (¬ p3553))
    : (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p3553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h27256 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53679 (p1983 p2027 p2274 p2396 p2542 p2545 p2563 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h27258 : (¬ p1983) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2542) ∨ p2545 ∨ (¬ p2563))
    : (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2542) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h27258 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53685 (p2027 p2220 p2249 p2656 p2727 p2963 p3922 p3923 p3969 p4347 p4399 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h27265 : p2027 ∨ (¬ p2220) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p3969) ∨ (¬ p4347) ∨ (¬ p4399) ∨ (¬ p5122))
    : (¬ p2220) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p3969) ∨ (¬ p4347) ∨ (¬ p4399) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h27265 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step53686 (p1978 p2027 p2192 p2633 p3486 p3570 p3646 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h27266 : (¬ p1978) ∨ p2027 ∨ (¬ p2192) ∨ p2633 ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p3646))
    : (¬ p2192) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p3646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1978 := h2138;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h27266 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53687 (p2027 p2138 p2417 p3367 p3389 p3692 p3694 p3759 p3950 p4734 : Prop)
    (h40810 : (¬ p2027))
    (h27268 : p2027 ∨ (¬ p2138) ∨ (¬ p2417) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3759) ∨ (¬ p3950) ∨ (¬ p4734))
    : (¬ p2138) ∨ (¬ p2417) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3759) ∨ (¬ p3950) ∨ (¬ p4734) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4734 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27268 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53690 (p1998 p2027 p2114 p2717 p3055 p3367 p3471 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h27271 : (¬ p1998) ∨ p2027 ∨ p2114 ∨ (¬ p2717) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3471))
    : (¬ p2717) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3471) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h27271 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53694 (p2027 p2946 p2972 p3292 p4040 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h27276 : p2027 ∨ (¬ p2946) ∨ (¬ p2972) ∨ (¬ p3292) ∨ (¬ p4040) ∨ (¬ p4960))
    : (¬ p2946) ∨ (¬ p2972) ∨ (¬ p3292) ∨ (¬ p4040) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27276 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53698 (p2027 p2177 p3051 p4120 p4132 p4556 : Prop)
    (h40810 : (¬ p2027))
    (h27281 : p2027 ∨ (¬ p2177) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4132) ∨ (¬ p4556))
    : (¬ p2177) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4132) ∨ (¬ p4556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27281 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53700 (p2027 p2934 p3093 p3631 p3821 p4281 p4760 p5206 : Prop)
    (h40810 : (¬ p2027))
    (h27283 : p2027 ∨ (¬ p2934) ∨ (¬ p3093) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4281) ∨ (¬ p4760) ∨ (¬ p5206))
    : (¬ p2934) ∨ (¬ p3093) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4281) ∨ (¬ p4760) ∨ (¬ p5206) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2934 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4760 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h27283 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step53702 (p1979 p2027 p2210 p2247 p2688 p2891 p4320 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h27285 : (¬ p1979) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2247) ∨ p2688 ∨ (¬ p2891) ∨ (¬ p4320))
    : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2891) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1979 := h2139;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h27285 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53707 (p1980 p2027 p2633 p2797 p3177 p3877 p3941 p5590 : Prop)
    (h2140 : p1980)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h27290 : (¬ p1980) ∨ p2027 ∨ p2633 ∨ (¬ p2797) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p3941) ∨ (¬ p5590))
    : (¬ p2797) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p3941) ∨ (¬ p5590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1980 := h2140;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h27290 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53709 (p2027 p2982 p3054 p3422 p4385 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h27292 : p2027 ∨ (¬ p2982) ∨ (¬ p3054) ∨ (¬ p3422) ∨ (¬ p4385) ∨ (¬ p4717))
    : (¬ p2982) ∨ (¬ p3054) ∨ (¬ p3422) ∨ (¬ p4385) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27292 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53710 (p2027 p2230 p2440 p2663 p3414 p4650 : Prop)
    (h40810 : (¬ p2027))
    (h27293 : p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p3414) ∨ (¬ p4650))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p3414) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27293 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53714 (p2027 p2579 p2588 p2696 p2742 p2901 p2992 p3363 p3585 p4556 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h27297 : p2027 ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4556) ∨ (¬ p4737))
    : (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4556) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27297 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53716 (p1996 p2027 p2622 p3365 p3471 p3527 p3553 p4424 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h27299 : (¬ p1996) ∨ p2027 ∨ p2622 ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4424))
    : (¬ p3365) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4424) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1996 := h2156;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h27299 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53718 (p2000 p2388 p2589 p4705 : Prop)
    (h2160 : p2000)
    (h40873 : (¬ p2388))
    (h27301 : (¬ p2000) ∨ p2388 ∨ (¬ p2589) ∨ p4705)
    : (¬ p2589) ∨ p4705 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4705) := (fun h => hn (Or.inr h));
    let u2 : p2000 := h2160;
    let u3 : (¬ p2388) := h40873;
    (Or.elim h27301 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step53719 (p2003 p2027 p2299 p2633 p3323 p3568 p3946 : Prop)
    (h2163 : p2003)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h27302 : (¬ p2003) ∨ p2027 ∨ (¬ p2299) ∨ p2633 ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3946))
    : (¬ p2299) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2003 := h2163;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h27302 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53720 (p1976 p2027 p2633 p3365 p3570 p4315 p4320 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h27303 : (¬ p1976) ∨ p2027 ∨ p2633 ∨ (¬ p3365) ∨ (¬ p3570) ∨ (¬ p4315) ∨ (¬ p4320))
    : (¬ p3365) ∨ (¬ p3570) ∨ (¬ p4315) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h27303 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53722 (p2027 p2241 p2589 p2641 p2668 p3097 p4110 p4405 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h27309 : p2027 ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4405) ∨ (¬ p5193))
    : (¬ p2241) ∨ (¬ p2589) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4405) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27309 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53726 (p1994 p2027 p2230 p2440 p2938 p3246 p3821 p5197 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h27313 : (¬ p1994) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ p2938 ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p5197))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2938) := h40888;
    (Or.elim h27313 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53728 (p2027 p2136 p2247 p2619 p2744 p2922 p3366 p3379 p4120 p4244 p4277 : Prop)
    (h40810 : (¬ p2027))
    (h27315 : p2027 ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2619) ∨ (¬ p2744) ∨ (¬ p2922) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p4120) ∨ (¬ p4244) ∨ (¬ p4277))
    : (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2619) ∨ (¬ p2744) ∨ (¬ p2922) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p4120) ∨ (¬ p4244) ∨ (¬ p4277) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27315 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53734 (p2007 p2027 p2145 p2264 p2651 p2766 p3580 p3646 p3941 p3989 p4117 p4286 p4347 : Prop)
    (h2167 : p2007)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h27323 : (¬ p2007) ∨ p2027 ∨ (¬ p2145) ∨ (¬ p2264) ∨ (¬ p2651) ∨ p2766 ∨ (¬ p3580) ∨ (¬ p3646) ∨ (¬ p3941) ∨ (¬ p3989) ∨ (¬ p4117) ∨ (¬ p4286) ∨ (¬ p4347))
    : (¬ p2145) ∨ (¬ p2264) ∨ (¬ p2651) ∨ (¬ p3580) ∨ (¬ p3646) ∨ (¬ p3941) ∨ (¬ p3989) ∨ (¬ p4117) ∨ (¬ p4286) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2007 := h2167;
    let u11 : (¬ p2027) := h40810;
    let u12 : (¬ p2766) := h40884;
    (Or.elim h27323 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u12 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u8))) (fun r11 => (False.elim (r11 u9)))))))))))))))))))))))))))

theorem step53737 (p2027 p2727 p2952 p3166 p4360 p4701 : Prop)
    (h40810 : (¬ p2027))
    (h27326 : p2027 ∨ (¬ p2727) ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p4360) ∨ (¬ p4701))
    : (¬ p2727) ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p4360) ∨ (¬ p4701) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4701 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27326 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53738 (p2027 p3055 p3366 p3399 p3527 p3591 p3684 p3880 p4866 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h27327 : p2027 ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3591) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p4866) ∨ (¬ p4905))
    : (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3591) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p4866) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27327 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53739 (p1976 p2027 p2169 p2363 p3365 p3877 p4118 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h27328 : (¬ p1976) ∨ p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4118))
    : (¬ p2363) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4118) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h27328 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53740 (p1982 p2027 p2192 p2363 p2873 p3156 p3952 p4441 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40886 : (¬ p2873))
    (h27329 : (¬ p1982) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p2363) ∨ p2873 ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p4441))
    : (¬ p2192) ∨ (¬ p2363) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p4441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2873) := h40886;
    (Or.elim h27329 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53742 (p2027 p2248 p2264 p2299 p2331 p3055 p3367 p3588 p3873 p4156 p4477 : Prop)
    (h40810 : (¬ p2027))
    (h27331 : p2027 ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4156) ∨ (¬ p4477))
    : (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4156) ∨ (¬ p4477) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27331 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53743 (p1994 p2027 p2598 p2622 p3365 p3422 p3574 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h27332 : (¬ p1994) ∨ p2027 ∨ (¬ p2598) ∨ p2622 ∨ (¬ p3365) ∨ (¬ p3422) ∨ (¬ p3574))
    : (¬ p2598) ∨ (¬ p3365) ∨ (¬ p3422) ∨ (¬ p3574) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h27332 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53748 (p2027 p2579 p3399 p3422 p3527 p3570 p3876 p4647 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h27337 : p2027 ∨ (¬ p2579) ∨ (¬ p3399) ∨ (¬ p3422) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3876) ∨ (¬ p4647) ∨ (¬ p5193))
    : (¬ p2579) ∨ (¬ p3399) ∨ (¬ p3422) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3876) ∨ (¬ p4647) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27337 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53754 (p1990 p2027 p2553 p2766 p3097 p3956 p4347 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h27343 : (¬ p1990) ∨ p2027 ∨ (¬ p2553) ∨ p2766 ∨ (¬ p3097) ∨ (¬ p3956) ∨ (¬ p4347))
    : (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3956) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h27343 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53755 (p1991 p2027 p2202 p2440 p3172 p3189 p4111 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h27345 : (¬ p1991) ∨ p2027 ∨ p2202 ∨ (¬ p2440) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p4111))
    : (¬ p2440) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h27345 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53757 (p2027 p2254 p2588 p2657 p3399 p3527 p3570 p3574 p4556 : Prop)
    (h40810 : (¬ p2027))
    (h27347 : p2027 ∨ (¬ p2254) ∨ (¬ p2588) ∨ (¬ p2657) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3574) ∨ (¬ p4556))
    : (¬ p2254) ∨ (¬ p2588) ∨ (¬ p2657) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3574) ∨ (¬ p4556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27347 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53759 (p2006 p2027 p2132 p2409 p2493 p3055 p3584 : Prop)
    (h2166 : p2006)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h27350 : (¬ p2006) ∨ p2027 ∨ (¬ p2132) ∨ p2409 ∨ (¬ p2493) ∨ (¬ p3055) ∨ (¬ p3584))
    : (¬ p2132) ∨ (¬ p2493) ∨ (¬ p3055) ∨ (¬ p3584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2006 := h2166;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2409) := h40874;
    (Or.elim h27350 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53760 (p2027 p2252 p2284 p2750 p2922 p2950 p3379 p3646 p3954 p4277 p4320 : Prop)
    (h40810 : (¬ p2027))
    (h27352 : p2027 ∨ (¬ p2252) ∨ (¬ p2284) ∨ (¬ p2750) ∨ (¬ p2922) ∨ (¬ p2950) ∨ (¬ p3379) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4277) ∨ (¬ p4320))
    : (¬ p2252) ∨ (¬ p2284) ∨ (¬ p2750) ∨ (¬ p2922) ∨ (¬ p2950) ∨ (¬ p3379) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4277) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27352 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53765 (p1987 p2027 p2388 p2727 p2810 p2901 p3368 p3486 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h27357 : (¬ p1987) ∨ p2027 ∨ p2388 ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p2901) ∨ (¬ p3368) ∨ (¬ p3486))
    : (¬ p2727) ∨ (¬ p2810) ∨ (¬ p2901) ∨ (¬ p3368) ∨ (¬ p3486) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2388) := h40873;
    (Or.elim h27357 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53766 (p2027 p3093 p3319 p3347 p3556 p3570 p3904 p3954 p4330 p4348 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h27361 : p2027 ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3347) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3904) ∨ (¬ p3954) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5216))
    : (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3347) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3904) ∨ (¬ p3954) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27361 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53772 (p2027 p2144 p2156 p3365 p4030 p4173 p4202 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h27367 : p2027 ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p3365) ∨ (¬ p4030) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4752))
    : (¬ p2144) ∨ (¬ p2156) ∨ (¬ p3365) ∨ (¬ p4030) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h27367 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step53779 (p2027 p2589 p2696 p2797 p3323 p3692 p3880 p4330 p4729 : Prop)
    (h40810 : (¬ p2027))
    (h27374 : p2027 ∨ (¬ p2589) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4330) ∨ (¬ p4729))
    : (¬ p2589) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4330) ∨ (¬ p4729) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27374 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53780 (p2027 p2493 p3238 p3758 p4203 p4882 : Prop)
    (h40810 : (¬ p2027))
    (h27375 : p2027 ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3758) ∨ (¬ p4203) ∨ (¬ p4882))
    : (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3758) ∨ (¬ p4203) ∨ (¬ p4882) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27375 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53781 (p2027 p2247 p2819 p3654 p3917 p4111 p4256 p4384 p5017 : Prop)
    (h40810 : (¬ p2027))
    (h27376 : p2027 ∨ (¬ p2247) ∨ (¬ p2819) ∨ (¬ p3654) ∨ (¬ p3917) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p5017))
    : (¬ p2247) ∨ (¬ p2819) ∨ (¬ p3654) ∨ (¬ p3917) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p5017) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27376 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53784 (p2027 p2363 p2386 p2553 p3857 p4197 p4501 : Prop)
    (h40810 : (¬ p2027))
    (h27380 : p2027 ∨ (¬ p2363) ∨ (¬ p2386) ∨ (¬ p2553) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4501))
    : (¬ p2363) ∨ (¬ p2386) ∨ (¬ p2553) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4501) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27380 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53787 (p1984 p2027 p2313 p2766 p3309 p3923 p4347 p5015 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h27383 : (¬ p1984) ∨ p2027 ∨ (¬ p2313) ∨ p2766 ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p5015))
    : (¬ p2313) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h27383 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53788 (p1988 p2027 p2114 p2230 p2982 p3367 p3680 p3759 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h27384 : (¬ p1988) ∨ p2027 ∨ p2114 ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3367) ∨ (¬ p3680) ∨ (¬ p3759))
    : (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3367) ∨ (¬ p3680) ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h27384 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53790 (p1982 p2027 p2202 p2440 p3276 p3343 p4444 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h27387 : (¬ p1982) ∨ p2027 ∨ p2202 ∨ (¬ p2440) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4444))
    : (¬ p2440) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h27387 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53791 (p1981 p2027 p2187 p2284 p2545 p2992 p4111 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h27389 : (¬ p1981) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2284) ∨ p2545 ∨ (¬ p2992) ∨ (¬ p4111))
    : (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2992) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h27389 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53794 (p2027 p2707 p3097 p3688 p4401 p4475 : Prop)
    (h40810 : (¬ p2027))
    (h27392 : p2027 ∨ (¬ p2707) ∨ (¬ p3097) ∨ (¬ p3688) ∨ (¬ p4401) ∨ (¬ p4475))
    : (¬ p2707) ∨ (¬ p3097) ∨ (¬ p3688) ∨ (¬ p4401) ∨ (¬ p4475) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27392 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53795 (p1975 p2027 p2137 p2156 p2274 p2839 p2842 p3585 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h27393 : (¬ p1975) ∨ p2027 ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2839) ∨ p2842 ∨ (¬ p3585))
    : (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2839) ∨ (¬ p3585) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2842) := h40885;
    (Or.elim h27393 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53800 (p2027 p2373 p2850 p3876 p3988 p4001 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h27400 : p2027 ∨ (¬ p2373) ∨ (¬ p2850) ∨ (¬ p3876) ∨ (¬ p3988) ∨ (¬ p4001) ∨ (¬ p4555))
    : (¬ p2373) ∨ (¬ p2850) ∨ (¬ p3876) ∨ (¬ p3988) ∨ (¬ p4001) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27400 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53801 (p2027 p2220 p2247 p3146 p4111 p4256 p4348 p4438 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h27401 : p2027 ∨ (¬ p2220) ∨ (¬ p2247) ∨ (¬ p3146) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4521))
    : (¬ p2220) ∨ (¬ p2247) ∨ (¬ p3146) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27401 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53802 (p2027 p2470 p2542 p2589 p3874 p4750 : Prop)
    (h40810 : (¬ p2027))
    (h27402 : p2027 ∨ (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3874) ∨ (¬ p4750))
    : (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3874) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27402 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53804 (p2027 p2132 p2619 p2780 p3745 p4337 p4509 : Prop)
    (h40810 : (¬ p2027))
    (h27406 : p2027 ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2780) ∨ (¬ p3745) ∨ (¬ p4337) ∨ (¬ p4509))
    : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2780) ∨ (¬ p3745) ∨ (¬ p4337) ∨ (¬ p4509) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27406 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53805 (p2027 p2177 p2598 p2850 p2982 p3551 p4107 p4395 p5260 : Prop)
    (h40810 : (¬ p2027))
    (h27407 : p2027 ∨ (¬ p2177) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5260))
    : (¬ p2177) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5260) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27407 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53806 (p1990 p2027 p2563 p2611 p2651 p2810 p3136 p4117 p4241 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h27408 : (¬ p1990) ∨ p2027 ∨ (¬ p2563) ∨ p2611 ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4117) ∨ (¬ p4241))
    : (¬ p2563) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4117) ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1990 := h2150;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2611) := h40877;
    (Or.elim h27408 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53808 (p2027 p2696 p2753 p2797 p3266 p3323 p3645 p4032 p4322 p4330 p4877 : Prop)
    (h40810 : (¬ p2027))
    (h27410 : p2027 ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3266) ∨ (¬ p3323) ∨ (¬ p3645) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4330) ∨ (¬ p4877))
    : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3266) ∨ (¬ p3323) ∨ (¬ p3645) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4330) ∨ (¬ p4877) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27410 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53810 (p2027 p2579 p2588 p3073 p3347 p3449 p3954 p4107 p4669 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h27413 : p2027 ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3073) ∨ (¬ p3347) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p5216))
    : (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3073) ∨ (¬ p3347) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27413 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53812 (p2027 p2630 p2696 p2753 p2761 p3204 p3343 p3946 p4191 p4512 p4638 p4877 : Prop)
    (h40810 : (¬ p2027))
    (h27416 : p2027 ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3204) ∨ (¬ p3343) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4512) ∨ (¬ p4638) ∨ (¬ p4877))
    : (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3204) ∨ (¬ p3343) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4512) ∨ (¬ p4638) ∨ (¬ p4877) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h27416 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step53814 (p2027 p2187 p3016 p3958 p4256 p4432 : Prop)
    (h40810 : (¬ p2027))
    (h27418 : p2027 ∨ (¬ p2187) ∨ (¬ p3016) ∨ (¬ p3958) ∨ (¬ p4256) ∨ (¬ p4432))
    : (¬ p2187) ∨ (¬ p3016) ∨ (¬ p3958) ∨ (¬ p4256) ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27418 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53815 (p2027 p2589 p2685 p3166 p3690 p3877 p3931 p4117 p4235 p4729 p4830 : Prop)
    (h40810 : (¬ p2027))
    (h27419 : p2027 ∨ (¬ p2589) ∨ (¬ p2685) ∨ (¬ p3166) ∨ (¬ p3690) ∨ (¬ p3877) ∨ (¬ p3931) ∨ (¬ p4117) ∨ (¬ p4235) ∨ (¬ p4729) ∨ (¬ p4830))
    : (¬ p2589) ∨ (¬ p2685) ∨ (¬ p3166) ∨ (¬ p3690) ∨ (¬ p3877) ∨ (¬ p3931) ∨ (¬ p4117) ∨ (¬ p4235) ∨ (¬ p4729) ∨ (¬ p4830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27419 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53816 (p2027 p2246 p2651 p2749 p2810 p3097 p3645 p3646 p3755 p4107 p4638 p4877 p5175 : Prop)
    (h40810 : (¬ p2027))
    (h27420 : p2027 ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p3097) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p4107) ∨ (¬ p4638) ∨ (¬ p4877) ∨ (¬ p5175))
    : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p3097) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p4107) ∨ (¬ p4638) ∨ (¬ p4877) ∨ (¬ p5175) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h27420 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step53817 (p2027 p2145 p2459 p2651 p2810 p3005 p3692 p4117 p4120 p4550 : Prop)
    (h40810 : (¬ p2027))
    (h27421 : p2027 ∨ (¬ p2145) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3692) ∨ (¬ p4117) ∨ (¬ p4120) ∨ (¬ p4550))
    : (¬ p2145) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3692) ∨ (¬ p4117) ∨ (¬ p4120) ∨ (¬ p4550) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27421 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53832 (p2010 p2027 p2493 p2699 p3201 p3379 p3584 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h27437 : (¬ p2010) ∨ p2027 ∨ (¬ p2493) ∨ p2699 ∨ (¬ p3201) ∨ (¬ p3379) ∨ (¬ p3584))
    : (¬ p2493) ∨ (¬ p3201) ∨ (¬ p3379) ∨ (¬ p3584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2010 := h2170;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h27437 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53834 (p2027 p2156 p2657 p2958 p4173 p4282 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h27439 : p2027 ∨ (¬ p2156) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p4173) ∨ (¬ p4282) ∨ (¬ p4704))
    : (¬ p2156) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p4173) ∨ (¬ p4282) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27439 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53835 (p2027 p2630 p3170 p3256 p3857 p4121 p4787 : Prop)
    (h40810 : (¬ p2027))
    (h27440 : p2027 ∨ (¬ p2630) ∨ (¬ p3170) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p4121) ∨ (¬ p4787))
    : (¬ p2630) ∨ (¬ p3170) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p4121) ∨ (¬ p4787) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4121 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27440 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53837 (p2027 p2505 p2509 p2588 p3309 p4595 : Prop)
    (h40810 : (¬ p2027))
    (h27442 : p2027 ∨ (¬ p2505) ∨ (¬ p2509) ∨ (¬ p2588) ∨ (¬ p3309) ∨ (¬ p4595))
    : (¬ p2505) ∨ (¬ p2509) ∨ (¬ p2588) ∨ (¬ p3309) ∨ (¬ p4595) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2505 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4595 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27442 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53840 (p1982 p2027 p2098 p2138 p2363 p2765 p3758 p4326 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h27445 : (¬ p1982) ∨ p2027 ∨ (¬ p2098) ∨ (¬ p2138) ∨ (¬ p2363) ∨ p2765 ∨ (¬ p3758) ∨ (¬ p4326))
    : (¬ p2098) ∨ (¬ p2138) ∨ (¬ p2363) ∨ (¬ p3758) ∨ (¬ p4326) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4326 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h27445 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53841 (p2027 p2247 p3767 p3854 p4321 p4439 : Prop)
    (h40810 : (¬ p2027))
    (h27446 : p2027 ∨ (¬ p2247) ∨ (¬ p3767) ∨ (¬ p3854) ∨ (¬ p4321) ∨ (¬ p4439))
    : (¬ p2247) ∨ (¬ p3767) ∨ (¬ p3854) ∨ (¬ p4321) ∨ (¬ p4439) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3854 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4439 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27446 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53843 (p2027 p2657 p2807 p2928 p3658 p4777 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h27448 : p2027 ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2928) ∨ (¬ p3658) ∨ (¬ p4777) ∨ (¬ p4811))
    : (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2928) ∨ (¬ p3658) ∨ (¬ p4777) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27448 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53845 (p1982 p2027 p2148 p2459 p3051 p3875 p4001 p4149 p5558 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h27451 : (¬ p1982) ∨ p2027 ∨ p2148 ∨ (¬ p2459) ∨ (¬ p3051) ∨ (¬ p3875) ∨ (¬ p4001) ∨ (¬ p4149) ∨ (¬ p5558))
    : (¬ p2459) ∨ (¬ p3051) ∨ (¬ p3875) ∨ (¬ p4001) ∨ (¬ p4149) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1982 := h2142;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2148) := h40865;
    (Or.elim h27451 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53846 (p2027 p2963 p3324 p3366 p3449 p3452 p4181 p4236 p4347 p4376 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h27454 : p2027 ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4181) ∨ (¬ p4236) ∨ (¬ p4347) ∨ (¬ p4376) ∨ (¬ p5122))
    : (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4181) ∨ (¬ p4236) ∨ (¬ p4347) ∨ (¬ p4376) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27454 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53847 (p2027 p2761 p2963 p3051 p3246 p3324 p3366 p3519 p4236 p4376 p4399 p5123 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h27455 : p2027 ∨ (¬ p2761) ∨ (¬ p2963) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p2761) ∨ (¬ p2963) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p5123) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h27455 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step53848 (p1976 p2027 p2299 p2633 p3425 p3791 p4423 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h27457 : (¬ p1976) ∨ p2027 ∨ (¬ p2299) ∨ p2633 ∨ (¬ p3425) ∨ (¬ p3791) ∨ (¬ p4423))
    : (¬ p2299) ∨ (¬ p3425) ∨ (¬ p3791) ∨ (¬ p4423) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4423 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h27457 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53852 (p2027 p2122 p2252 p2396 p2534 p2657 p2750 p2829 p3950 p4256 : Prop)
    (h40810 : (¬ p2027))
    (h27463 : p2027 ∨ (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p3950) ∨ (¬ p4256))
    : (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p3950) ∨ (¬ p4256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27463 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53859 (p2027 p2187 p2870 p4193 p4358 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h27472 : p2027 ∨ (¬ p2187) ∨ (¬ p2870) ∨ (¬ p4193) ∨ (¬ p4358) ∨ (¬ p4558))
    : (¬ p2187) ∨ (¬ p2870) ∨ (¬ p4193) ∨ (¬ p4358) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27472 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53863 (p1975 p2027 p2122 p2699 p3093 p3319 p3917 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h27476 : (¬ p1975) ∨ p2027 ∨ (¬ p2122) ∨ p2699 ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3917))
    : (¬ p2122) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h27476 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53865 (p2027 p3584 p3683 p4009 p4121 p4286 p4607 p4715 : Prop)
    (h40810 : (¬ p2027))
    (h27480 : p2027 ∨ (¬ p3584) ∨ (¬ p3683) ∨ (¬ p4009) ∨ (¬ p4121) ∨ (¬ p4286) ∨ (¬ p4607) ∨ (¬ p4715))
    : (¬ p3584) ∨ (¬ p3683) ∨ (¬ p4009) ∨ (¬ p4121) ∨ (¬ p4286) ∨ (¬ p4607) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3584 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4121 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h27480 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step53868 (p1992 p2027 p2622 p2630 p2657 p2774 p3688 p4236 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h27483 : (¬ p1992) ∨ p2027 ∨ p2622 ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p3688) ∨ (¬ p4236))
    : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p3688) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h27483 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53869 (p2027 p3055 p3767 p4749 p5352 p5387 p5453 : Prop)
    (h40810 : (¬ p2027))
    (h27484 : p2027 ∨ (¬ p3055) ∨ (¬ p3767) ∨ (¬ p4749) ∨ (¬ p5352) ∨ (¬ p5387) ∨ (¬ p5453))
    : (¬ p3055) ∨ (¬ p3767) ∨ (¬ p4749) ∨ (¬ p5352) ∨ (¬ p5387) ∨ (¬ p5453) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27484 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53870 (p2027 p2254 p2518 p3379 p3414 p3947 p4149 p4381 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h27485 : p2027 ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4149) ∨ (¬ p4381) ∨ (¬ p5119))
    : (¬ p2254) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4149) ∨ (¬ p4381) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27485 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53871 (p2027 p2136 p2619 p2696 p4120 p5049 : Prop)
    (h40810 : (¬ p2027))
    (h27486 : p2027 ∨ (¬ p2136) ∨ (¬ p2619) ∨ (¬ p2696) ∨ (¬ p4120) ∨ (¬ p5049))
    : (¬ p2136) ∨ (¬ p2619) ∨ (¬ p2696) ∨ (¬ p4120) ∨ (¬ p5049) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27486 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53877 (p2027 p2780 p2946 p3115 p3680 p3822 p4260 p4786 p4831 : Prop)
    (h40810 : (¬ p2027))
    (h27494 : p2027 ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p3822) ∨ (¬ p4260) ∨ (¬ p4786) ∨ (¬ p4831))
    : (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p3822) ∨ (¬ p4260) ∨ (¬ p4786) ∨ (¬ p4831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2780 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27494 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53878 (p2027 p2383 p3055 p3323 p3324 p3876 p3987 p4278 p4621 p4786 : Prop)
    (h40810 : (¬ p2027))
    (h27495 : p2027 ∨ (¬ p2383) ∨ (¬ p3055) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3876) ∨ (¬ p3987) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4786))
    : (¬ p2383) ∨ (¬ p3055) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3876) ∨ (¬ p3987) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27495 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53880 (p2027 p2247 p2588 p2744 p3055 p3093 p3319 p3366 p3584 p4624 : Prop)
    (h40810 : (¬ p2027))
    (h27498 : p2027 ∨ (¬ p2247) ∨ (¬ p2588) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3366) ∨ (¬ p3584) ∨ (¬ p4624))
    : (¬ p2247) ∨ (¬ p2588) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3366) ∨ (¬ p3584) ∨ (¬ p4624) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27498 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53882 (p2027 p3422 p3564 p3874 p4432 p4603 : Prop)
    (h40810 : (¬ p2027))
    (h27500 : p2027 ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p3874) ∨ (¬ p4432) ∨ (¬ p4603))
    : (¬ p3422) ∨ (¬ p3564) ∨ (¬ p3874) ∨ (¬ p4432) ∨ (¬ p4603) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4603 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27500 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53884 (p2027 p2542 p2651 p2780 p2982 p3822 p4107 p4395 p4786 : Prop)
    (h40810 : (¬ p2027))
    (h27504 : p2027 ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p2982) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4786))
    : (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p2982) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27504 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53887 (p2027 p2248 p2780 p2946 p3146 p3156 p3822 p3873 p4107 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h27508 : p2027 ∨ (¬ p2248) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3822) ∨ (¬ p3873) ∨ (¬ p4107) ∨ (¬ p4669))
    : (¬ p2248) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3822) ∨ (¬ p3873) ∨ (¬ p4107) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27508 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53892 (p1985 p2027 p2202 p2911 p3201 p3570 p3684 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h27513 : (¬ p1985) ∨ p2027 ∨ p2202 ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3570) ∨ (¬ p3684))
    : (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3570) ∨ (¬ p3684) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h27513 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53893 (p1985 p2027 p2246 p2545 p2807 p2911 p3570 p3579 p4111 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h27514 : (¬ p1985) ∨ p2027 ∨ (¬ p2246) ∨ p2545 ∨ (¬ p2807) ∨ (¬ p2911) ∨ (¬ p3570) ∨ (¬ p3579) ∨ (¬ p4111))
    : (¬ p2246) ∨ (¬ p2807) ∨ (¬ p2911) ∨ (¬ p3570) ∨ (¬ p3579) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1985 := h2145;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2545) := h40876;
    (Or.elim h27514 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53894 (p1990 p2027 p2331 p2545 p2657 p2668 p3989 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h27515 : (¬ p1990) ∨ p2027 ∨ (¬ p2331) ∨ p2545 ∨ (¬ p2657) ∨ (¬ p2668) ∨ (¬ p3989))
    : (¬ p2331) ∨ (¬ p2657) ∨ (¬ p2668) ∨ (¬ p3989) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h27515 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53898 (p2027 p2220 p2579 p3115 p3366 p3370 p3497 p3822 p3905 p4107 p4377 p4390 p4395 : Prop)
    (h40810 : (¬ p2027))
    (h27523 : p2027 ∨ (¬ p2220) ∨ (¬ p2579) ∨ (¬ p3115) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3497) ∨ (¬ p3822) ∨ (¬ p3905) ∨ (¬ p4107) ∨ (¬ p4377) ∨ (¬ p4390) ∨ (¬ p4395))
    : (¬ p2220) ∨ (¬ p2579) ∨ (¬ p3115) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3497) ∨ (¬ p3822) ∨ (¬ p3905) ∨ (¬ p4107) ∨ (¬ p4377) ∨ (¬ p4390) ∨ (¬ p4395) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h27523 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step53899 (p2012 p2027 p2202 p2579 p3355 p3422 p3684 : Prop)
    (h2172 : p2012)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h27524 : (¬ p2012) ∨ p2027 ∨ p2202 ∨ (¬ p2579) ∨ (¬ p3355) ∨ (¬ p3422) ∨ (¬ p3684))
    : (¬ p2579) ∨ (¬ p3355) ∨ (¬ p3422) ∨ (¬ p3684) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2012 := h2172;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h27524 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53903 (p2027 p2630 p2657 p3471 p4236 p4782 : Prop)
    (h40810 : (¬ p2027))
    (h27528 : p2027 ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3471) ∨ (¬ p4236) ∨ (¬ p4782))
    : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3471) ∨ (¬ p4236) ∨ (¬ p4782) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27528 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53904 (p2027 p2630 p2657 p2774 p4236 p4845 : Prop)
    (h40810 : (¬ p2027))
    (h27529 : p2027 ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p4236) ∨ (¬ p4845))
    : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p4236) ∨ (¬ p4845) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27529 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53909 (p1982 p2027 p2220 p2860 p3146 p3474 p3646 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h27535 : (¬ p1982) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p2860) ∨ (¬ p3146) ∨ p3474 ∨ (¬ p3646))
    : (¬ p2220) ∨ (¬ p2860) ∨ (¬ p3146) ∨ (¬ p3646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3474) := h40898;
    (Or.elim h27535 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53910 (p2027 p2156 p2187 p2363 p3055 p3366 p3370 p3876 p4278 p4377 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h27536 : p2027 ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4377) ∨ (¬ p4669))
    : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4377) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27536 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53912 (p2027 p2341 p3246 p3365 p3570 p4037 p4195 p4625 p5257 : Prop)
    (h40810 : (¬ p2027))
    (h27538 : p2027 ∨ (¬ p2341) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3570) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4625) ∨ (¬ p5257))
    : (¬ p2341) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3570) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4625) ∨ (¬ p5257) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27538 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53915 (p1976 p2027 p2437 p3008 p3055 p3574 p3876 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h27544 : (¬ p1976) ∨ p2027 ∨ (¬ p2437) ∨ p3008 ∨ (¬ p3055) ∨ (¬ p3574) ∨ (¬ p3876))
    : (¬ p2437) ∨ (¬ p3055) ∨ (¬ p3574) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3008) := h40891;
    (Or.elim h27544 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53919 (p1982 p2027 p2406 p2409 p2427 p2459 p2881 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h27550 : (¬ p1982) ∨ p2027 ∨ (¬ p2406) ∨ p2409 ∨ (¬ p2427) ∨ (¬ p2459) ∨ (¬ p2881))
    : (¬ p2406) ∨ (¬ p2427) ∨ (¬ p2459) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2409) := h40874;
    (Or.elim h27550 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53920 (p2027 p2187 p2192 p2210 p2459 p2476 p4133 p4340 p5193 p5373 : Prop)
    (h40810 : (¬ p2027))
    (h27551 : p2027 ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p5193) ∨ (¬ p5373))
    : (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p5193) ∨ (¬ p5373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27551 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53921 (p2027 p2088 p2110 p3365 p3685 p4340 p4782 : Prop)
    (h40810 : (¬ p2027))
    (h27552 : p2027 ∨ (¬ p2088) ∨ (¬ p2110) ∨ (¬ p3365) ∨ (¬ p3685) ∨ (¬ p4340) ∨ (¬ p4782))
    : (¬ p2088) ∨ (¬ p2110) ∨ (¬ p3365) ∨ (¬ p3685) ∨ (¬ p4340) ∨ (¬ p4782) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27552 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53922 (p1975 p2027 p2307 p2387 p2459 p2633 p3692 p4441 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h27553 : (¬ p1975) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2459) ∨ p2633 ∨ (¬ p3692) ∨ (¬ p4441))
    : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h27553 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53923 (p1992 p2027 p2462 p2761 p2785 p3688 p3946 p4191 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h27555 : (¬ p1992) ∨ p2027 ∨ p2462 ∨ (¬ p2761) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p3946) ∨ (¬ p4191))
    : (¬ p2761) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p3946) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2462) := h40875;
    (Or.elim h27555 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53924 (p1985 p2202 p2427 p5119 p5121 : Prop)
    (h2145 : p1985)
    (h40867 : (¬ p2202))
    (h27556 : (¬ p1985) ∨ p2202 ∨ (¬ p2427) ∨ p5119 ∨ (¬ p5121))
    : (¬ p2427) ∨ p5119 ∨ (¬ p5121) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5119) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5121 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p1985 := h2145;
    let u4 : (¬ p2202) := h40867;
    (Or.elim h27556 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step53925 (p1975 p2027 p2148 p2220 p2274 p2563 p3880 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h27557 : (¬ p1975) ∨ p2027 ∨ p2148 ∨ (¬ p2220) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3880))
    : (¬ p2220) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3880) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2148) := h40865;
    (Or.elim h27557 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53926 (p2027 p2247 p2911 p3389 p3568 p3570 p4154 p4556 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h27558 : p2027 ∨ (¬ p2247) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p3570) ∨ (¬ p4154) ∨ (¬ p4556) ∨ (¬ p5190))
    : (¬ p2247) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p3570) ∨ (¬ p4154) ∨ (¬ p4556) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27558 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53931 (p1997 p2027 p2542 p3441 p4181 p4256 p4286 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40897 : (¬ p3441))
    (h27563 : (¬ p1997) ∨ p2027 ∨ (¬ p2542) ∨ p3441 ∨ (¬ p4181) ∨ (¬ p4256) ∨ (¬ p4286))
    : (¬ p2542) ∨ (¬ p4181) ∨ (¬ p4256) ∨ (¬ p4286) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3441) := h40897;
    (Or.elim h27563 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53933 (p2027 p2136 p2247 p2299 p2744 p3083 p3097 p3366 p3379 p3487 p3646 p4420 : Prop)
    (h40810 : (¬ p2027))
    (h27572 : p2027 ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p3646) ∨ (¬ p4420))
    : (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p3646) ∨ (¬ p4420) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h27572 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step53935 (p1982 p2027 p2363 p2553 p3008 p3063 p3549 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h27574 : (¬ p1982) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2553) ∨ p3008 ∨ (¬ p3063) ∨ (¬ p3549))
    : (¬ p2363) ∨ (¬ p2553) ∨ (¬ p3063) ∨ (¬ p3549) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3008) := h40891;
    (Or.elim h27574 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53937 (p2027 p3591 p3830 p4037 p4761 p5152 : Prop)
    (h40810 : (¬ p2027))
    (h27576 : p2027 ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p4037) ∨ (¬ p4761) ∨ (¬ p5152))
    : (¬ p3591) ∨ (¬ p3830) ∨ (¬ p4037) ∨ (¬ p4761) ∨ (¬ p5152) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3591 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27576 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53938 (p2027 p2247 p2363 p2383 p3266 p3662 p5017 p5405 p5740 : Prop)
    (h40810 : (¬ p2027))
    (h27577 : p2027 ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p3266) ∨ (¬ p3662) ∨ (¬ p5017) ∨ (¬ p5405) ∨ (¬ p5740))
    : (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p3266) ∨ (¬ p3662) ∨ (¬ p5017) ∨ (¬ p5405) ∨ (¬ p5740) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27577 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53940 (p1992 p2027 p2764 p3363 p3540 p3585 p4278 p4381 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h27580 : (¬ p1992) ∨ p2027 ∨ p2764 ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p4278) ∨ (¬ p4381))
    : (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p4278) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h27580 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53941 (p1984 p2027 p2545 p2707 p2743 p2810 p3425 p3873 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h27582 : (¬ p1984) ∨ p2027 ∨ p2545 ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3425) ∨ (¬ p3873))
    : (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3425) ∨ (¬ p3873) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h27582 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53942 (p2027 p2187 p2248 p2284 p2707 p2946 p3425 p3873 p4242 p4863 : Prop)
    (h40810 : (¬ p2027))
    (h27585 : p2027 ∨ (¬ p2187) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2707) ∨ (¬ p2946) ∨ (¬ p3425) ∨ (¬ p3873) ∨ (¬ p4242) ∨ (¬ p4863))
    : (¬ p2187) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2707) ∨ (¬ p2946) ∨ (¬ p3425) ∨ (¬ p3873) ∨ (¬ p4242) ∨ (¬ p4863) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4863 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27585 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53944 (p2027 p2313 p2598 p2753 p2850 p3204 p3727 p4107 p4381 p4870 p5400 : Prop)
    (h40810 : (¬ p2027))
    (h27588 : p2027 ∨ (¬ p2313) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3204) ∨ (¬ p3727) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p4870) ∨ (¬ p5400))
    : (¬ p2313) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3204) ∨ (¬ p3727) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p4870) ∨ (¬ p5400) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27588 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53945 (p1998 p2027 p2363 p2819 p2997 p3822 p4348 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h27590 : (¬ p1998) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2819) ∨ p2997 ∨ (¬ p3822) ∨ (¬ p4348))
    : (¬ p2363) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h27590 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53947 (p2027 p2145 p2685 p2696 p3692 p3931 p4120 p4444 p4826 : Prop)
    (h40810 : (¬ p2027))
    (h27592 : p2027 ∨ (¬ p2145) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3692) ∨ (¬ p3931) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4826))
    : (¬ p2145) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3692) ∨ (¬ p3931) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4826) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27592 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53948 (p2027 p2579 p2588 p3619 p3670 p4107 p4322 p4395 p4729 : Prop)
    (h40810 : (¬ p2027))
    (h27593 : p2027 ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3619) ∨ (¬ p3670) ∨ (¬ p4107) ∨ (¬ p4322) ∨ (¬ p4395) ∨ (¬ p4729))
    : (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3619) ∨ (¬ p3670) ∨ (¬ p4107) ∨ (¬ p4322) ∨ (¬ p4395) ∨ (¬ p4729) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27593 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53952 (p2011 p2027 p2563 p2938 p3212 p3646 p4235 : Prop)
    (h2171 : p2011)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h27597 : (¬ p2011) ∨ p2027 ∨ (¬ p2563) ∨ p2938 ∨ (¬ p3212) ∨ (¬ p3646) ∨ (¬ p4235))
    : (¬ p2563) ∨ (¬ p3212) ∨ (¬ p3646) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2011 := h2171;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h27597 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53953 (p2027 p2264 p2459 p2589 p2807 p3744 p4110 p4117 p4604 p4729 : Prop)
    (h40810 : (¬ p2027))
    (h27598 : p2027 ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2589) ∨ (¬ p2807) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4117) ∨ (¬ p4604) ∨ (¬ p4729))
    : (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2589) ∨ (¬ p2807) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4117) ∨ (¬ p4604) ∨ (¬ p4729) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27598 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53954 (p1983 p2027 p2417 p2437 p2622 p2662 p2743 p3367 p3759 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h27599 : (¬ p1983) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p2437) ∨ p2622 ∨ (¬ p2662) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3759))
    : (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2662) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1983 := h2143;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2622) := h40878;
    (Or.elim h27599 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53958 (p2027 p2406 p2509 p2563 p3693 p4507 : Prop)
    (h40810 : (¬ p2027))
    (h27605 : p2027 ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2563) ∨ (¬ p3693) ∨ (¬ p4507))
    : (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2563) ∨ (¬ p3693) ∨ (¬ p4507) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27605 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53959 (p1997 p2027 p2192 p2764 p4033 p4110 p4191 p4363 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h27606 : (¬ p1997) ∨ p2027 ∨ (¬ p2192) ∨ p2764 ∨ (¬ p4033) ∨ (¬ p4110) ∨ (¬ p4191) ∨ (¬ p4363))
    : (¬ p2192) ∨ (¬ p4033) ∨ (¬ p4110) ∨ (¬ p4191) ∨ (¬ p4363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h27606 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53961 (p2027 p2352 p3323 p3568 p4137 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h27608 : p2027 ∨ (¬ p2352) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4137) ∨ (¬ p4405))
    : (¬ p2352) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4137) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27608 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53962 (p1997 p2027 p2299 p2633 p3791 p4110 p4204 p5660 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h27612 : (¬ p1997) ∨ p2027 ∨ (¬ p2299) ∨ p2633 ∨ (¬ p3791) ∨ (¬ p4110) ∨ (¬ p4204) ∨ (¬ p5660))
    : (¬ p2299) ∨ (¬ p3791) ∨ (¬ p4110) ∨ (¬ p4204) ∨ (¬ p5660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h27612 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53963 (p2027 p2138 p2247 p2744 p3063 p3093 p3097 p3366 p3758 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h27614 : p2027 ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3366) ∨ (¬ p3758) ∨ (¬ p4405))
    : (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3366) ∨ (¬ p3758) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27614 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step53965 (p1992 p2027 p2169 p2363 p2608 p3692 p3860 p3906 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h27617 : (¬ p1992) ∨ p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p3692) ∨ (¬ p3860) ∨ (¬ p3906))
    : (¬ p2363) ∨ (¬ p2608) ∨ (¬ p3692) ∨ (¬ p3860) ∨ (¬ p3906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h27617 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step53969 (p2027 p2406 p2651 p2952 p3879 p4814 : Prop)
    (h40810 : (¬ p2027))
    (h27623 : p2027 ∨ (¬ p2406) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4814))
    : (¬ p2406) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27623 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53975 (p1990 p2027 p2331 p2611 p2685 p3097 p3552 p4117 p4195 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h27629 : (¬ p1990) ∨ p2027 ∨ (¬ p2331) ∨ p2611 ∨ (¬ p2685) ∨ (¬ p3097) ∨ (¬ p3552) ∨ (¬ p4117) ∨ (¬ p4195))
    : (¬ p2331) ∨ (¬ p2685) ∨ (¬ p3097) ∨ (¬ p3552) ∨ (¬ p4117) ∨ (¬ p4195) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1990 := h2150;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2611) := h40877;
    (Or.elim h27629 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step53977 (p2027 p3527 p3659 p4173 p4344 p4431 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h27631 : p2027 ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p4173) ∨ (¬ p4344) ∨ (¬ p4431) ∨ (¬ p4558))
    : (¬ p3527) ∨ (¬ p3659) ∨ (¬ p4173) ∨ (¬ p4344) ∨ (¬ p4431) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27631 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53979 (p2027 p2641 p2696 p2751 p2780 p4337 : Prop)
    (h40810 : (¬ p2027))
    (h27633 : p2027 ∨ (¬ p2641) ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p2780) ∨ (¬ p4337))
    : (¬ p2641) ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p2780) ∨ (¬ p4337) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27633 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53980 (p2027 p2146 p2220 p3146 p4340 p4359 : Prop)
    (h40810 : (¬ p2027))
    (h27635 : p2027 ∨ (¬ p2146) ∨ (¬ p2220) ∨ (¬ p3146) ∨ (¬ p4340) ∨ (¬ p4359))
    : (¬ p2146) ∨ (¬ p2220) ∨ (¬ p3146) ∨ (¬ p4340) ∨ (¬ p4359) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27635 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53981 (p2027 p3548 p3631 p4133 p4347 p4636 p4695 : Prop)
    (h40810 : (¬ p2027))
    (h27636 : p2027 ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4636) ∨ (¬ p4695))
    : (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4636) ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3548 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27636 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step53984 (p1976 p2027 p2633 p2737 p3365 p3588 p3659 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h27641 : (¬ p1976) ∨ p2027 ∨ p2633 ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3588) ∨ (¬ p3659))
    : (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3588) ∨ (¬ p3659) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h27641 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step53985 (p2027 p2191 p2248 p2331 p3506 p3555 p3690 p3747 p4191 p4421 p4621 : Prop)
    (h40810 : (¬ p2027))
    (h27642 : p2027 ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p3747) ∨ (¬ p4191) ∨ (¬ p4421) ∨ (¬ p4621))
    : (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p3747) ∨ (¬ p4191) ∨ (¬ p4421) ∨ (¬ p4621) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27642 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step53989 (p2027 p3073 p4189 p4348 p4442 p5559 : Prop)
    (h40810 : (¬ p2027))
    (h27647 : p2027 ∨ (¬ p3073) ∨ (¬ p4189) ∨ (¬ p4348) ∨ (¬ p4442) ∨ (¬ p5559))
    : (¬ p3073) ∨ (¬ p4189) ∨ (¬ p4348) ∨ (¬ p4442) ∨ (¬ p5559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27647 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53994 (p2027 p2230 p2563 p3125 p3365 p3877 p4118 p4330 p4419 : Prop)
    (h40810 : (¬ p2027))
    (h27652 : p2027 ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4419))
    : (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27652 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step53996 (p2027 p2230 p2274 p2563 p3005 p3172 p3366 p3519 p3572 p4236 p4361 p4376 : Prop)
    (h40810 : (¬ p2027))
    (h27654 : p2027 ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3572) ∨ (¬ p4236) ∨ (¬ p4361) ∨ (¬ p4376))
    : (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3572) ∨ (¬ p4236) ∨ (¬ p4361) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h27654 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step53997 (p2027 p3115 p3413 p3684 p4750 p4948 : Prop)
    (h40810 : (¬ p2027))
    (h27655 : p2027 ∨ (¬ p3115) ∨ (¬ p3413) ∨ (¬ p3684) ∨ (¬ p4750) ∨ (¬ p4948))
    : (¬ p3115) ∨ (¬ p3413) ∨ (¬ p3684) ∨ (¬ p4750) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27655 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step53998 (p2027 p2241 p2750 p3631 p3687 p3821 p5206 : Prop)
    (h40810 : (¬ p2027))
    (h27656 : p2027 ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3821) ∨ (¬ p5206))
    : (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3821) ∨ (¬ p5206) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27656 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54002 (p2027 p2891 p3556 p3574 p3948 p4031 p4116 p4715 : Prop)
    (h40810 : (¬ p2027))
    (h27662 : p2027 ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3574) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4116) ∨ (¬ p4715))
    : (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3574) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4116) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h27662 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step54003 (p1986 p2027 p2114 p2470 p2493 p2579 p3541 p3874 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h27663 : (¬ p1986) ∨ p2027 ∨ p2114 ∨ (¬ p2470) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3541) ∨ (¬ p3874))
    : (¬ p2470) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3541) ∨ (¬ p3874) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1986 := h2146;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h27663 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step54007 (p2027 p3365 p3366 p3399 p3452 p3631 p3877 p3950 p4118 p4376 : Prop)
    (h40810 : (¬ p2027))
    (h27668 : p2027 ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3631) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4376))
    : (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3631) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27668 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54008 (p2027 p3452 p3998 p4376 p4492 p4874 p5242 p5693 : Prop)
    (h40810 : (¬ p2027))
    (h27669 : p2027 ∨ (¬ p3452) ∨ (¬ p3998) ∨ (¬ p4376) ∨ (¬ p4492) ∨ (¬ p4874) ∨ (¬ p5242) ∨ (¬ p5693))
    : (¬ p3452) ∨ (¬ p3998) ∨ (¬ p4376) ∨ (¬ p4492) ∨ (¬ p4874) ∨ (¬ p5242) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3452 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h27669 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step54015 (p1987 p2027 p2651 p2766 p2810 p3172 p4118 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h27676 : (¬ p1987) ∨ p2027 ∨ (¬ p2651) ∨ p2766 ∨ (¬ p2810) ∨ (¬ p3172) ∨ (¬ p4118))
    : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3172) ∨ (¬ p4118) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h27676 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54016 (p2027 p2210 p2247 p4154 p4282 p4563 : Prop)
    (h40810 : (¬ p2027))
    (h27677 : p2027 ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p4154) ∨ (¬ p4282) ∨ (¬ p4563))
    : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p4154) ∨ (¬ p4282) ∨ (¬ p4563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27677 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54018 (p2027 p2254 p2598 p2707 p2952 p3097 p3585 p3589 p3952 p4473 : Prop)
    (h40810 : (¬ p2027))
    (h27679 : p2027 ∨ (¬ p2254) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3952) ∨ (¬ p4473))
    : (¬ p2254) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3952) ∨ (¬ p4473) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h27679 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step54024 (p2027 p2264 p2363 p3947 p4445 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h27688 : p2027 ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p3947) ∨ (¬ p4445) ∨ (¬ p4503))
    : (¬ p2264) ∨ (¬ p2363) ∨ (¬ p3947) ∨ (¬ p4445) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27688 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54028 (p1992 p2027 p2284 p2743 p2950 p3361 p3497 p3578 p3646 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h27693 : (¬ p1992) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2743) ∨ (¬ p2950) ∨ (¬ p3361) ∨ (¬ p3497) ∨ p3578 ∨ (¬ p3646))
    : (¬ p2284) ∨ (¬ p2743) ∨ (¬ p2950) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1992 := h2152;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p3578) := h40900;
    (Or.elim h27693 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step54029 (p1992 p2027 p2766 p3584 p3585 p3956 p4347 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h27694 : (¬ p1992) ∨ p2027 ∨ p2766 ∨ (¬ p3584) ∨ (¬ p3585) ∨ (¬ p3956) ∨ (¬ p4347))
    : (¬ p3584) ∨ (¬ p3585) ∨ (¬ p3956) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3584 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h27694 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54034 (p2027 p2177 p2307 p2788 p3659 p3689 : Prop)
    (h40810 : (¬ p2027))
    (h27699 : p2027 ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2788) ∨ (¬ p3659) ∨ (¬ p3689))
    : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2788) ∨ (¬ p3659) ∨ (¬ p3689) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2788 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3689 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27699 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54035 (p2027 p2307 p2504 p2584 p2665 p3549 p3574 : Prop)
    (h40810 : (¬ p2027))
    (h27700 : p2027 ∨ (¬ p2307) ∨ (¬ p2504) ∨ (¬ p2584) ∨ (¬ p2665) ∨ (¬ p3549) ∨ (¬ p3574))
    : (¬ p2307) ∨ (¬ p2504) ∨ (¬ p2584) ∨ (¬ p2665) ∨ (¬ p3549) ∨ (¬ p3574) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h27700 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step54036 (p2027 p2307 p2506 p3452 p3549 p5020 : Prop)
    (h40810 : (¬ p2027))
    (h27701 : p2027 ∨ (¬ p2307) ∨ (¬ p2506) ∨ (¬ p3452) ∨ (¬ p3549) ∨ (¬ p5020))
    : (¬ p2307) ∨ (¬ p2506) ∨ (¬ p3452) ∨ (¬ p3549) ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27701 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54037 (p1989 p2027 p2210 p2766 p3548 p4348 p4366 : Prop)
    (h2149 : p1989)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h27702 : (¬ p1989) ∨ p2027 ∨ (¬ p2210) ∨ p2766 ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p4366))
    : (¬ p2210) ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1989 := h2149;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h27702 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step54038 (p2027 p2387 p3654 p4345 p4348 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h27703 : p2027 ∨ (¬ p2387) ∨ (¬ p3654) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p2387) ∨ (¬ p3654) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h27703 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step54039 (p2027 p2246 p2744 p2946 p3055 p3156 p3366 p3969 p4425 p5119 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h27705 : p2027 ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p5160))
    : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h27705 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step54041 (p2027 p2664 p2946 p3156 p3540 p3644 p3969 p4348 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h27707 : p2027 ∨ (¬ p2664) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3969) ∨ (¬ p4348) ∨ (¬ p5122))
    : (¬ p2664) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3969) ∨ (¬ p4348) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2664 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h27707 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step54043 (p1984 p2027 p2633 p3434 p3659 p3817 p4366 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h27709 : (¬ p1984) ∨ p2027 ∨ p2633 ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3817) ∨ (¬ p4366))
    : (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3817) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h27709 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

end ElevenRUP
