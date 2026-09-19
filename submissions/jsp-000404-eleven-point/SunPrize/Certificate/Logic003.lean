import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step42796 (p1985 p2027 p2387 p2427 p2766 p4110 p4347 p4356 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h13585 : (¬ p1985) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2427) ∨ p2766 ∨ (¬ p4110) ∨ (¬ p4347) ∨ (¬ p4356))
    : (¬ p2387) ∨ (¬ p2427) ∨ (¬ p4110) ∨ (¬ p4347) ∨ (¬ p4356) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1985 := h2145;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h13585 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42797 (p1987 p2027 p2737 p2766 p2785 p3324 p3567 p3688 p4347 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h13587 : (¬ p1987) ∨ p2027 ∨ (¬ p2737) ∨ p2766 ∨ (¬ p2785) ∨ (¬ p3324) ∨ (¬ p3567) ∨ (¬ p3688) ∨ (¬ p4347))
    : (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3324) ∨ (¬ p3567) ∨ (¬ p3688) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1987 := h2147;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2766) := h40884;
    (Or.elim h13587 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step42798 (p1987 p2027 p2598 p2737 p2780 p3585 p3586 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40901 : (¬ p3586))
    (h13588 : (¬ p1987) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3585) ∨ p3586)
    : (¬ p2598) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3585) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3586) := h40901;
    (Or.elim h13588 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step42800 (p1975 p2027 p2132 p2274 p2699 p2829 p3583 p3589 p4185 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13590 : (¬ p1975) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2274) ∨ p2699 ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4185))
    : (¬ p2132) ∨ (¬ p2274) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4185) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1975 := h2135;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2699) := h40881;
    (Or.elim h13590 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step42801 (p1992 p2409 p3585 p5217 : Prop)
    (h2152 : p1992)
    (h40874 : (¬ p2409))
    (h13591 : (¬ p1992) ∨ p2409 ∨ (¬ p3585) ∨ p5217)
    : (¬ p3585) ∨ p5217 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3585 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5217) := (fun h => hn (Or.inr h));
    let u2 : p1992 := h2152;
    let u3 : (¬ p2409) := h40874;
    (Or.elim h13591 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step42802 (p1987 p2027 p2138 p2598 p2737 p3474 p3585 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h13592 : (¬ p1987) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2598) ∨ (¬ p2737) ∨ p3474 ∨ (¬ p3585))
    : (¬ p2138) ∨ (¬ p2598) ∨ (¬ p2737) ∨ (¬ p3585) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3474) := h40898;
    (Or.elim h13592 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42807 (p1975 p2027 p2553 p2598 p2611 p2829 p3585 p4390 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h13597 : (¬ p1975) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2598) ∨ p2611 ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p4390))
    : (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p4390) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h13597 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42808 (p1979 p2027 p2766 p2946 p2963 p3324 p4347 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h13598 : (¬ p1979) ∨ p2027 ∨ p2766 ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4347))
    : (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1979 := h2139;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h13598 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42810 (p2003 p2027 p2295 p2313 p2766 p3324 p4347 : Prop)
    (h2163 : p2003)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h13600 : (¬ p2003) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2313) ∨ p2766 ∨ (¬ p3324) ∨ (¬ p4347))
    : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3324) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2003 := h2163;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h13600 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42811 (p1997 p2027 p2299 p2766 p3097 p4110 p4348 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h13601 : (¬ p1997) ∨ p2027 ∨ (¬ p2299) ∨ p2766 ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4348))
    : (¬ p2299) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h13601 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42812 (p1991 p2027 p2459 p2633 p2963 p3324 p4347 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h13602 : (¬ p1991) ∨ p2027 ∨ (¬ p2459) ∨ p2633 ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4347))
    : (¬ p2459) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h13602 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42816 (p1992 p2027 p2589 p2633 p3363 p3570 p3585 p4235 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h13606 : (¬ p1992) ∨ p2027 ∨ (¬ p2589) ∨ p2633 ∨ (¬ p3363) ∨ (¬ p3570) ∨ (¬ p3585) ∨ (¬ p4235))
    : (¬ p2589) ∨ (¬ p3363) ∨ (¬ p3570) ∨ (¬ p3585) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h13606 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42817 (p1985 p2027 p2427 p2598 p2699 p2839 p3585 p3589 p3695 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13608 : (¬ p1985) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p2598) ∨ p2699 ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3695))
    : (¬ p2427) ∨ (¬ p2598) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1985 := h2145;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2699) := h40881;
    (Or.elim h13608 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step42819 (p1994 p2027 p2651 p2766 p2963 p3324 p4347 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h13610 : (¬ p1994) ∨ p2027 ∨ (¬ p2651) ∨ p2766 ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4347))
    : (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h13610 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42823 (p1997 p2027 p2156 p2462 p3556 p3690 p4110 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h13614 : (¬ p1997) ∨ p2027 ∨ (¬ p2156) ∨ p2462 ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p4110))
    : (¬ p2156) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h13614 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42825 (p2004 p2766 p3817 p3950 : Prop)
    (h2164 : p2004)
    (h40884 : (¬ p2766))
    (h13684 : (¬ p2004) ∨ p2766 ∨ (¬ p3817) ∨ p3950)
    : (¬ p3817) ∨ p3950 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3817 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3950) := (fun h => hn (Or.inr h));
    let u2 : p2004 := h2164;
    let u3 : (¬ p2766) := h40884;
    (Or.elim h13684 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step42828 (p2002 p2027 p2829 p2938 p3246 p3588 p4324 : Prop)
    (h2162 : p2002)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h13687 : (¬ p2002) ∨ p2027 ∨ (¬ p2829) ∨ p2938 ∨ (¬ p3246) ∨ (¬ p3588) ∨ (¬ p4324))
    : (¬ p2829) ∨ (¬ p3246) ∨ (¬ p3588) ∨ (¬ p4324) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2002 := h2162;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h13687 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42831 (p1998 p2027 p2406 p2427 p2699 p2881 p3379 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13690 : (¬ p1998) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2427) ∨ p2699 ∨ (¬ p2881) ∨ (¬ p3379))
    : (¬ p2406) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13690 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42832 (p2006 p2027 p2598 p2839 p3425 p3437 p3585 : Prop)
    (h2166 : p2006)
    (h40810 : (¬ p2027))
    (h40896 : (¬ p3437))
    (h13691 : (¬ p2006) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p2839) ∨ (¬ p3425) ∨ p3437 ∨ (¬ p3585))
    : (¬ p2598) ∨ (¬ p2839) ∨ (¬ p3425) ∨ (¬ p3585) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2006 := h2166;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3437) := h40896;
    (Or.elim h13691 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42834 (p1978 p2027 p2284 p2462 p3646 p3690 p4320 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h13693 : (¬ p1978) ∨ p2027 ∨ (¬ p2284) ∨ p2462 ∨ (¬ p3646) ∨ (¬ p3690) ∨ (¬ p4320))
    : (¬ p2284) ∨ (¬ p3646) ∨ (¬ p3690) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1978 := h2138;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h13693 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42837 (p1982 p2027 p2528 p2598 p2699 p3537 p3585 p3589 p5373 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13696 : (¬ p1982) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p2598) ∨ p2699 ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p5373))
    : (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p5373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1982 := h2142;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2699) := h40881;
    (Or.elim h13696 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step42838 (p1975 p2027 p2274 p2608 p2699 p2839 p2860 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13714 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2839) ∨ (¬ p2860))
    : (¬ p2274) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13714 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42841 (p1985 p2027 p2699 p2911 p2922 p3379 p3570 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13717 : (¬ p1985) ∨ p2027 ∨ p2699 ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3570))
    : (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13717 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42842 (p1991 p2027 p2766 p2952 p3952 p3989 p4347 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h13718 : (¬ p1991) ∨ p2027 ∨ p2766 ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4347))
    : (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h13718 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42843 (p1998 p2027 p2177 p2493 p2553 p2699 p3379 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13719 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2493) ∨ (¬ p2553) ∨ p2699 ∨ (¬ p3379))
    : (¬ p2177) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13719 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42844 (p1997 p2027 p2493 p2699 p2850 p3379 p3584 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13720 : (¬ p1997) ∨ p2027 ∨ (¬ p2493) ∨ p2699 ∨ (¬ p2850) ∨ (¬ p3379) ∨ (¬ p3584))
    : (¬ p2493) ∨ (¬ p2850) ∨ (¬ p3379) ∨ (¬ p3584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13720 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42845 (p1975 p2027 p2553 p2608 p2699 p3367 p3422 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13721 : (¬ p1975) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p3367) ∨ (¬ p3422))
    : (¬ p2553) ∨ (¬ p2608) ∨ (¬ p3367) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13721 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42847 (p1998 p2027 p2608 p2699 p2839 p2870 p2881 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13723 : (¬ p1998) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p2881))
    : (¬ p2608) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13723 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42848 (p2001 p2169 p3989 p4509 : Prop)
    (h2161 : p2001)
    (h40866 : (¬ p2169))
    (h13724 : (¬ p2001) ∨ p2169 ∨ (¬ p3989) ∨ p4509)
    : (¬ p3989) ∨ p4509 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3989 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4509) := (fun h => hn (Or.inr h));
    let u2 : p2001 := h2161;
    let u3 : (¬ p2169) := h40866;
    (Or.elim h13724 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step42849 (p1990 p2027 p2563 p2608 p2699 p2850 p3367 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13725 : (¬ p1990) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2850) ∨ (¬ p3367))
    : (¬ p2563) ∨ (¬ p2608) ∨ (¬ p2850) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13725 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42850 (p1982 p2027 p2459 p2699 p2911 p2922 p3379 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13727 : (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ p2699 ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379))
    : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13727 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42853 (p1998 p2027 p2518 p2528 p2699 p3379 p4348 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13747 : (¬ p1998) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p2528) ∨ p2699 ∨ (¬ p3379) ∨ (¬ p4348))
    : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13747 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42854 (p1992 p2027 p2341 p3360 p3585 p3644 p3876 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40895 : (¬ p3360))
    (h13749 : (¬ p1992) ∨ p2027 ∨ (¬ p2341) ∨ p3360 ∨ (¬ p3585) ∨ (¬ p3644) ∨ (¬ p3876))
    : (¬ p2341) ∨ (¬ p3585) ∨ (¬ p3644) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3360) := h40895;
    (Or.elim h13749 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42855 (p2005 p2027 p2608 p2630 p2699 p2737 p3016 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13750 : (¬ p2005) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2630) ∨ p2699 ∨ (¬ p2737) ∨ (¬ p3016))
    : (¬ p2608) ∨ (¬ p2630) ∨ (¬ p2737) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13750 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42856 (p1985 p2027 p2284 p2323 p2427 p2651 p3413 p4110 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h13751 : (¬ p1985) ∨ p2027 ∨ (¬ p2284) ∨ p2323 ∨ (¬ p2427) ∨ (¬ p2651) ∨ (¬ p3413) ∨ (¬ p4110))
    : (¬ p2284) ∨ (¬ p2427) ∨ (¬ p2651) ∨ (¬ p3413) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1985 := h2145;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h13751 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42857 (p1985 p2027 p2233 p2427 p2542 p2573 p3574 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h13752 : (¬ p1985) ∨ p2027 ∨ p2233 ∨ (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3574))
    : (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3574) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2233) := h40868;
    (Or.elim h13752 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42858 (p1990 p2027 p2542 p2563 p2611 p2630 p2696 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h13753 : (¬ p1990) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p2563) ∨ p2611 ∨ (¬ p2630) ∨ (¬ p2696))
    : (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2630) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h13753 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42860 (p1998 p2027 p2323 p2881 p2946 p3027 p3662 p4333 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h13756 : (¬ p1998) ∨ p2027 ∨ p2323 ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3662) ∨ (¬ p4333))
    : (¬ p2881) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3662) ∨ (¬ p4333) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h13756 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42861 (p2004 p2027 p2202 p2589 p2911 p3389 p3548 : Prop)
    (h2164 : p2004)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h13757 : (¬ p2004) ∨ p2027 ∨ p2202 ∨ (¬ p2589) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3548))
    : (¬ p2589) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3548) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2004 := h2164;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h13757 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42863 (p2005 p2027 p2622 p2727 p3016 p3136 p3662 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h13759 : (¬ p2005) ∨ p2027 ∨ p2622 ∨ (¬ p2727) ∨ (¬ p3016) ∨ (¬ p3136) ∨ (¬ p3662))
    : (¬ p2727) ∨ (¬ p3016) ∨ (¬ p3136) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h13759 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42864 (p1980 p2027 p2545 p2641 p2657 p2946 p3662 : Prop)
    (h2140 : p1980)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h13760 : (¬ p1980) ∨ p2027 ∨ p2545 ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3662))
    : (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1980 := h2140;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h13760 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42865 (p1997 p2027 p2608 p2699 p2839 p2860 p4110 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13761 : (¬ p1997) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p4110))
    : (¬ p2608) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13761 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42867 (p1983 p2027 p2253 p2449 p2699 p2946 p3027 p3662 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13763 : (¬ p1983) ∨ p2027 ∨ (¬ p2253) ∨ (¬ p2449) ∨ p2699 ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3662))
    : (¬ p2253) ∨ (¬ p2449) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1983 := h2143;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h13763 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42868 (p2011 p2027 p2608 p2699 p2839 p3670 p4322 p5031 : Prop)
    (h2171 : p2011)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13781 : (¬ p2011) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2839) ∨ (¬ p3670) ∨ (¬ p4322) ∨ (¬ p5031))
    : (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3670) ∨ (¬ p4322) ∨ (¬ p5031) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2011 := h2171;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h13781 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42869 (p1995 p2027 p2499 p2764 p3956 p4347 p4444 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h13799 : (¬ p1995) ∨ p2027 ∨ (¬ p2499) ∨ p2764 ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4444))
    : (¬ p2499) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h13799 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42870 (p1996 p2027 p2545 p2657 p2946 p3027 p3662 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h13800 : (¬ p1996) ∨ p2027 ∨ p2545 ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3662))
    : (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1996 := h2156;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h13800 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42872 (p1992 p2254 p2323 p2608 p3576 p4794 : Prop)
    (h2152 : p1992)
    (h40870 : (¬ p2323))
    (h13802 : (¬ p1992) ∨ (¬ p2254) ∨ p2323 ∨ (¬ p2608) ∨ (¬ p3576) ∨ p4794)
    : (¬ p2254) ∨ (¬ p2608) ∨ (¬ p3576) ∨ p4794 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p4794) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2323) := h40870;
    (Or.elim h13802 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step42873 (p1983 p2766 p4348 p4668 : Prop)
    (h2143 : p1983)
    (h40884 : (¬ p2766))
    (h13803 : (¬ p1983) ∨ p2766 ∨ (¬ p4348) ∨ p4668)
    : (¬ p4348) ∨ p4668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4348 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4668) := (fun h => hn (Or.inr h));
    let u2 : p1983 := h2143;
    let u3 : (¬ p2766) := h40884;
    (Or.elim h13803 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step42874 (p1975 p2027 p2553 p2699 p2774 p2819 p3589 p3956 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13804 : (¬ p1975) ∨ p2027 ∨ (¬ p2553) ∨ p2699 ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3589) ∨ (¬ p3956))
    : (¬ p2553) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3589) ∨ (¬ p3956) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h13804 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42875 (p1981 p2027 p2518 p2528 p2699 p3379 p4347 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13806 : (¬ p1981) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p2528) ∨ p2699 ∨ (¬ p3379) ∨ (¬ p4347))
    : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13806 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42876 (p1983 p2027 p2122 p2396 p2608 p2699 p2829 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13807 : (¬ p1983) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2829))
    : (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2608) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13807 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42877 (p2005 p2027 p2588 p2598 p2611 p3309 p3585 p4869 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h13808 : (¬ p2005) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2598) ∨ p2611 ∨ (¬ p3309) ∨ (¬ p3585) ∨ (¬ p4869))
    : (¬ p2588) ∨ (¬ p2598) ∨ (¬ p3309) ∨ (¬ p3585) ∨ (¬ p4869) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2005 := h2165;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h13808 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42878 (p1992 p2027 p2143 p2765 p2901 p3556 p3583 p3952 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h13809 : (¬ p1992) ∨ p2027 ∨ (¬ p2143) ∨ p2765 ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p3952))
    : (¬ p2143) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h13809 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42879 (p1992 p2027 p2143 p2765 p3156 p3583 p3952 p4120 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h13810 : (¬ p1992) ∨ p2027 ∨ (¬ p2143) ∨ p2765 ∨ (¬ p3156) ∨ (¬ p3583) ∨ (¬ p3952) ∨ (¬ p4120))
    : (¬ p2143) ∨ (¬ p3156) ∨ (¬ p3583) ∨ (¬ p3952) ∨ (¬ p4120) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h13810 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42880 (p1983 p2027 p2417 p2598 p2611 p2707 p3585 p3658 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h13811 : (¬ p1983) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p2598) ∨ p2611 ∨ (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658))
    : (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1983 := h2143;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h13811 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42881 (p2010 p2027 p2608 p2699 p2707 p3434 p4278 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13812 : (¬ p2010) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p4278))
    : (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2010 := h2170;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13812 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42883 (p2008 p2027 p2699 p2707 p3654 p3688 p3917 p5020 : Prop)
    (h2168 : p2008)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13814 : (¬ p2008) ∨ p2027 ∨ p2699 ∨ (¬ p2707) ∨ (¬ p3654) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p5020))
    : (¬ p2707) ∨ (¬ p3654) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2008 := h2168;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h13814 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42884 (p1991 p2027 p2766 p2952 p3570 p4320 p4348 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h13815 : (¬ p1991) ∨ p2027 ∨ p2766 ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p4348))
    : (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h13815 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42885 (p1991 p2027 p2619 p2765 p2952 p3497 p3758 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h13816 : (¬ p1991) ∨ p2027 ∨ (¬ p2619) ∨ p2765 ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3758))
    : (¬ p2619) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3758) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h13816 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42886 (p1991 p2027 p2630 p2657 p2938 p4315 p4320 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h13817 : (¬ p1991) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p2657) ∨ p2938 ∨ (¬ p4315) ∨ (¬ p4320))
    : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p4315) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h13817 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42887 (p1987 p2027 p2331 p2938 p2952 p4195 p4320 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h13818 : (¬ p1987) ∨ p2027 ∨ (¬ p2331) ∨ p2938 ∨ (¬ p2952) ∨ (¬ p4195) ∨ (¬ p4320))
    : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p4195) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h13818 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42888 (p2010 p2027 p2437 p2598 p2611 p3422 p3574 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h13819 : (¬ p2010) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p2598) ∨ p2611 ∨ (¬ p3422) ∨ (¬ p3574))
    : (¬ p2437) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3574) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2010 := h2170;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h13819 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42889 (p1997 p2542 p2842 p4753 : Prop)
    (h2157 : p1997)
    (h40885 : (¬ p2842))
    (h13820 : (¬ p1997) ∨ (¬ p2542) ∨ p2842 ∨ p4753)
    : (¬ p2542) ∨ p4753 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4753) := (fun h => hn (Or.inr h));
    let u2 : p1997 := h2157;
    let u3 : (¬ p2842) := h40885;
    (Or.elim h13820 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step42891 (p1987 p2027 p2331 p2766 p3172 p4118 p4195 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h13822 : (¬ p1987) ∨ p2027 ∨ (¬ p2331) ∨ p2766 ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4195))
    : (¬ p2331) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4195) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h13822 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42894 (p2012 p2027 p2230 p2233 p3233 p3238 p3707 p4425 : Prop)
    (h2172 : p2012)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h13843 : (¬ p2012) ∨ p2027 ∨ (¬ p2230) ∨ p2233 ∨ (¬ p3233) ∨ (¬ p3238) ∨ (¬ p3707) ∨ (¬ p4425))
    : (¬ p2230) ∨ (¬ p3233) ∨ (¬ p3238) ∨ (¬ p3707) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2012 := h2172;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2233) := h40868;
    (Or.elim h13843 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42899 (p1982 p2027 p2608 p2619 p2699 p2839 p3146 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13899 : (¬ p1982) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2619) ∨ p2699 ∨ (¬ p2839) ∨ (¬ p3146))
    : (¬ p2608) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13899 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42901 (p1997 p2132 p2611 p4885 : Prop)
    (h2157 : p1997)
    (h40877 : (¬ p2611))
    (h13901 : (¬ p1997) ∨ (¬ p2132) ∨ p2611 ∨ p4885)
    : (¬ p2132) ∨ p4885 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4885) := (fun h => hn (Or.inr h));
    let u2 : p1997 := h2157;
    let u3 : (¬ p2611) := h40877;
    (Or.elim h13901 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step42902 (p2010 p2027 p2202 p2573 p2589 p3201 p3584 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h13902 : (¬ p2010) ∨ p2027 ∨ p2202 ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3201) ∨ (¬ p3584))
    : (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3201) ∨ (¬ p3584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2010 := h2170;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h13902 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42903 (p1983 p2027 p2406 p2427 p2699 p3246 p3379 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13903 : (¬ p1983) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2427) ∨ p2699 ∨ (¬ p3246) ∨ (¬ p3379))
    : (¬ p2406) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13903 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42904 (p1983 p2027 p2608 p2699 p2839 p2870 p3246 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13904 : (¬ p1983) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3246))
    : (¬ p2608) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13904 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42905 (p1990 p2388 p2901 p4555 : Prop)
    (h2150 : p1990)
    (h40873 : (¬ p2388))
    (h13905 : (¬ p1990) ∨ p2388 ∨ (¬ p2901) ∨ p4555)
    : (¬ p2901) ∨ p4555 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4555) := (fun h => hn (Or.inr h));
    let u2 : p1990 := h2150;
    let u3 : (¬ p2388) := h40873;
    (Or.elim h13905 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step42906 (p1985 p2027 p2122 p2132 p2177 p2611 p3570 p3985 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h13906 : (¬ p1985) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2132) ∨ (¬ p2177) ∨ p2611 ∨ (¬ p3570) ∨ (¬ p3985))
    : (¬ p2122) ∨ (¬ p2132) ∨ (¬ p2177) ∨ (¬ p3570) ∨ (¬ p3985) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1985 := h2145;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h13906 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42908 (p1976 p3055 p3474 p3684 p4885 : Prop)
    (h2136 : p1976)
    (h40898 : (¬ p3474))
    (h13909 : (¬ p1976) ∨ (¬ p3055) ∨ p3474 ∨ (¬ p3684) ∨ p4885)
    : (¬ p3055) ∨ (¬ p3684) ∨ p4885 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4885) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p1976 := h2136;
    let u4 : (¬ p3474) := h40898;
    (Or.elim h13909 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step42910 (p1976 p2027 p2138 p2284 p2938 p3758 p4320 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h13911 : (¬ p1976) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2284) ∨ p2938 ∨ (¬ p3758) ∨ (¬ p4320))
    : (¬ p2138) ∨ (¬ p2284) ∨ (¬ p3758) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h13911 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42911 (p1992 p2027 p2220 p2765 p3583 p3646 p3694 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h13931 : (¬ p1992) ∨ p2027 ∨ (¬ p2220) ∨ p2765 ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p3694))
    : (¬ p2220) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p3694) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h13931 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42912 (p1976 p2027 p2766 p3365 p3497 p3692 p4315 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h13932 : (¬ p1976) ∨ p2027 ∨ p2766 ∨ (¬ p3365) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4315))
    : (¬ p3365) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h13932 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42915 (p1985 p2027 p2344 p2427 p3654 p3744 p4110 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40871 : (¬ p2344))
    (h13935 : (¬ p1985) ∨ p2027 ∨ p2344 ∨ (¬ p2427) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p4110))
    : (¬ p2427) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2344) := h40871;
    (Or.elim h13935 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42916 (p1985 p2427 p2914 p4644 : Prop)
    (h2145 : p1985)
    (h40887 : (¬ p2914))
    (h13936 : (¬ p1985) ∨ (¬ p2427) ∨ p2914 ∨ p4644)
    : (¬ p2427) ∨ p4644 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4644) := (fun h => hn (Or.inr h));
    let u2 : p1985 := h2145;
    let u3 : (¬ p2914) := h40887;
    (Or.elim h13936 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step42917 (p1976 p2027 p2138 p2765 p3115 p3952 p4385 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h13937 : (¬ p1976) ∨ p2027 ∨ (¬ p2138) ∨ p2765 ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p4385))
    : (¬ p2138) ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p4385) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h13937 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42918 (p1981 p2027 p2187 p2230 p2476 p2563 p3498 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40899 : (¬ p3498))
    (h13938 : (¬ p1981) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2563) ∨ p3498)
    : (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3498) := h40899;
    (Or.elim h13938 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step42922 (p1983 p2027 p2299 p2396 p2842 p2911 p3201 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h13942 : (¬ p1983) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2396) ∨ p2842 ∨ (¬ p2911) ∨ (¬ p3201))
    : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2911) ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2842) := h40885;
    (Or.elim h13942 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42924 (p1983 p2027 p2396 p2553 p2598 p2611 p3422 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h13944 : (¬ p1983) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2598) ∨ p2611 ∨ (¬ p3422))
    : (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h13944 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42927 (p1992 p2027 p2132 p2914 p3055 p3583 p3876 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h13947 : (¬ p1992) ∨ p2027 ∨ (¬ p2132) ∨ p2914 ∨ (¬ p3055) ∨ (¬ p3583) ∨ (¬ p3876))
    : (¬ p2132) ∨ (¬ p3055) ∨ (¬ p3583) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h13947 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42928 (p1997 p2938 p4110 p4555 : Prop)
    (h2157 : p1997)
    (h40888 : (¬ p2938))
    (h13949 : (¬ p1997) ∨ p2938 ∨ (¬ p4110) ∨ p4555)
    : (¬ p4110) ∨ p4555 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4110 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4555) := (fun h => hn (Or.inr h));
    let u2 : p1997 := h2157;
    let u3 : (¬ p2938) := h40888;
    (Or.elim h13949 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step42929 (p1995 p2027 p2476 p2499 p2534 p2573 p2766 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h13950 : (¬ p1995) ∨ p2027 ∨ (¬ p2476) ∨ (¬ p2499) ∨ (¬ p2534) ∨ (¬ p2573) ∨ p2766)
    : (¬ p2476) ∨ (¬ p2499) ∨ (¬ p2534) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h13950 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step42930 (p1995 p2027 p2230 p2579 p2588 p2997 p3238 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h13951 : (¬ p1995) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2588) ∨ p2997 ∨ (¬ p3238))
    : (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3238) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h13951 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42932 (p1991 p2148 p2952 p2960 : Prop)
    (h2151 : p1991)
    (h40865 : (¬ p2148))
    (h13953 : (¬ p1991) ∨ p2148 ∨ (¬ p2952) ∨ p2960)
    : (¬ p2952) ∨ p2960 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2960) := (fun h => hn (Or.inr h));
    let u2 : p1991 := h2151;
    let u3 : (¬ p2148) := h40865;
    (Or.elim h13953 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step42933 (p1975 p2027 p2241 p2274 p2284 p2699 p2992 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13954 : (¬ p1975) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2274) ∨ (¬ p2284) ∨ p2699 ∨ (¬ p2992))
    : (¬ p2241) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13954 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42934 (p1992 p2027 p2138 p2696 p2743 p2938 p4244 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h13955 : (¬ p1992) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2743) ∨ p2938 ∨ (¬ p4244))
    : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p4244) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h13955 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42937 (p1988 p2027 p2608 p2699 p2707 p2761 p3434 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13975 : (¬ p1988) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2707) ∨ (¬ p2761) ∨ (¬ p3434))
    : (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2761) ∨ (¬ p3434) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13975 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42938 (p1992 p2027 p2766 p3266 p3322 p3688 p4191 p4358 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h13976 : (¬ p1992) ∨ p2027 ∨ p2766 ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3688) ∨ (¬ p4191) ∨ (¬ p4358))
    : (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3688) ∨ (¬ p4191) ∨ (¬ p4358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h13976 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42942 (p1992 p2027 p2387 p2764 p2785 p3688 p4347 p4444 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h13981 : (¬ p1992) ∨ p2027 ∨ (¬ p2387) ∨ p2764 ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4347) ∨ (¬ p4444))
    : (¬ p2387) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4347) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h13981 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42944 (p1976 p2027 p2764 p2780 p4347 p4358 p4444 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h13983 : (¬ p1976) ∨ p2027 ∨ p2764 ∨ (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4444))
    : (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2780 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h13983 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42945 (p1990 p2027 p2192 p2323 p2901 p2946 p3486 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h13984 : (¬ p1990) ∨ p2027 ∨ (¬ p2192) ∨ p2323 ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3486))
    : (¬ p2192) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3486) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h13984 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42946 (p1983 p2027 p2241 p2699 p2901 p2992 p3246 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13985 : (¬ p1983) ∨ p2027 ∨ (¬ p2241) ∨ p2699 ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3246))
    : (¬ p2241) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13985 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42947 (p1988 p2027 p2241 p2699 p3189 p3256 p3266 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13986 : (¬ p1988) ∨ p2027 ∨ (¬ p2241) ∨ p2699 ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3266))
    : (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13986 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42948 (p1988 p2027 p2241 p2641 p2699 p3323 p3461 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13987 : (¬ p1988) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2641) ∨ p2699 ∨ (¬ p3323) ∨ (¬ p3461))
    : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13987 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42952 (p1992 p2027 p2462 p2696 p2743 p3425 p4324 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h13991 : (¬ p1992) ∨ p2027 ∨ p2462 ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3425) ∨ (¬ p4324))
    : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3425) ∨ (¬ p4324) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h13991 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42954 (p1975 p2027 p2274 p2323 p2641 p2946 p3662 p3986 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h13993 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ p2323 ∨ (¬ p2641) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3986))
    : (¬ p2274) ∨ (¬ p2641) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h13993 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42955 (p2010 p2027 p2437 p2608 p2630 p2699 p2737 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13994 : (¬ p2010) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2630) ∨ p2699 ∨ (¬ p2737))
    : (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2630) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2010 := h2170;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13994 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42958 (p2005 p2027 p2230 p2233 p2493 p2982 p4202 p4363 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h13997 : (¬ p2005) ∨ p2027 ∨ (¬ p2230) ∨ p2233 ∨ (¬ p2493) ∨ (¬ p2982) ∨ (¬ p4202) ∨ (¬ p4363))
    : (¬ p2230) ∨ (¬ p2493) ∨ (¬ p2982) ∨ (¬ p4202) ∨ (¬ p4363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2005 := h2165;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2233) := h40868;
    (Or.elim h13997 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42959 (p1988 p2027 p2241 p2699 p2992 p3115 p3680 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h13998 : (¬ p1988) ∨ p2027 ∨ (¬ p2241) ∨ p2699 ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3680))
    : (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3680) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h13998 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42960 (p1992 p2027 p2462 p2774 p3425 p3688 p4107 p4471 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h13999 : (¬ p1992) ∨ p2027 ∨ p2462 ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p3688) ∨ (¬ p4107) ∨ (¬ p4471))
    : (¬ p2774) ∨ (¬ p3425) ∨ (¬ p3688) ∨ (¬ p4107) ∨ (¬ p4471) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2462) := h40875;
    (Or.elim h13999 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42962 (p1994 p2027 p2440 p2765 p3051 p3646 p4235 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14001 : (¬ p1994) ∨ p2027 ∨ (¬ p2440) ∨ p2765 ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4235))
    : (¬ p2440) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h14001 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42963 (p1997 p2027 p2608 p2699 p2839 p2870 p4235 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14002 : (¬ p1997) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p4235))
    : (¬ p2608) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14002 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42964 (p2004 p2027 p2241 p2449 p2699 p3027 p3817 : Prop)
    (h2164 : p2004)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14003 : (¬ p2004) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2449) ∨ p2699 ∨ (¬ p3027) ∨ (¬ p3817))
    : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3817) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2004 := h2164;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14003 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42965 (p1994 p2027 p2630 p2688 p3506 p3842 p5387 p5453 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h14022 : (¬ p1994) ∨ p2027 ∨ (¬ p2630) ∨ p2688 ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p5387) ∨ (¬ p5453))
    : (¬ p2630) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p5387) ∨ (¬ p5453) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h14022 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42966 (p1991 p2027 p2440 p2657 p2997 p3097 p4110 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14023 : (¬ p1991) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2657) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p4110))
    : (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3097) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h14023 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42967 (p2002 p2027 p2914 p3016 p3564 p3742 p3917 : Prop)
    (h2162 : p2002)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h14024 : (¬ p2002) ∨ p2027 ∨ p2914 ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3742) ∨ (¬ p3917))
    : (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3742) ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2002 := h2162;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h14024 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42970 (p1988 p2027 p2122 p2177 p2459 p3266 p3586 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40901 : (¬ p3586))
    (h14028 : (¬ p1988) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2459) ∨ (¬ p3266) ∨ p3586)
    : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2459) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3586) := h40901;
    (Or.elim h14028 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step42971 (p1997 p2027 p2542 p2938 p3246 p3742 p4278 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h14029 : (¬ p1997) ∨ p2027 ∨ (¬ p2542) ∨ p2938 ∨ (¬ p3246) ∨ (¬ p3742) ∨ (¬ p4278))
    : (¬ p2542) ∨ (¬ p3246) ∨ (¬ p3742) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h14029 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42973 (p2017 p2027 p2230 p2233 p2922 p3238 p3868 : Prop)
    (h2177 : p2017)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h14049 : (¬ p2017) ∨ p2027 ∨ (¬ p2230) ∨ p2233 ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3868))
    : (¬ p2230) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3868) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2017 := h2177;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2233) := h40868;
    (Or.elim h14049 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42975 (p1994 p2027 p2241 p2630 p2699 p3189 p3877 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14051 : (¬ p1994) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2630) ∨ p2699 ∨ (¬ p3189) ∨ (¬ p3877))
    : (¬ p2241) ∨ (¬ p2630) ∨ (¬ p3189) ∨ (¬ p3877) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14051 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42976 (p1982 p2027 p2611 p2696 p2743 p3537 p3609 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14052 : (¬ p1982) ∨ p2027 ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3537) ∨ (¬ p3609))
    : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3537) ∨ (¬ p3609) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14052 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42978 (p1982 p2027 p2611 p2774 p3537 p3609 p3688 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14054 : (¬ p1982) ∨ p2027 ∨ p2611 ∨ (¬ p2774) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3688))
    : (¬ p2774) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3688) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14054 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42979 (p1975 p2027 p2295 p2608 p2699 p2737 p2797 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14055 : (¬ p1975) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2737) ∨ (¬ p2797))
    : (¬ p2295) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14055 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42980 (p2008 p2027 p2341 p3360 p3548 p3631 p4324 : Prop)
    (h2168 : p2008)
    (h40810 : (¬ p2027))
    (h40895 : (¬ p3360))
    (h14056 : (¬ p2008) ∨ p2027 ∨ (¬ p2341) ∨ p3360 ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4324))
    : (¬ p2341) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4324) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2008 := h2168;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3360) := h40895;
    (Or.elim h14056 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42981 (p1975 p2027 p2608 p2699 p2707 p3434 p4107 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14057 : (¬ p1975) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p4107))
    : (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14057 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42982 (p1995 p2027 p2230 p2462 p3238 p3540 p4278 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h14058 : (¬ p1995) ∨ p2027 ∨ (¬ p2230) ∨ p2462 ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p4278))
    : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h14058 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42983 (p1975 p2027 p2274 p2323 p2331 p3323 p3744 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14059 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ p2323 ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3744))
    : (¬ p2274) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14059 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42984 (p1980 p3128 p3568 p4620 : Prop)
    (h2140 : p1980)
    (h40894 : (¬ p3128))
    (h14060 : (¬ p1980) ∨ p3128 ∨ (¬ p3568) ∨ p4620)
    : (¬ p3568) ∨ p4620 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4620) := (fun h => hn (Or.inr h));
    let u2 : p1980 := h2140;
    let u3 : (¬ p3128) := h40894;
    (Or.elim h14060 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step42985 (p1976 p2027 p2534 p2766 p2810 p3365 p4256 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14061 : (¬ p1976) ∨ p2027 ∨ (¬ p2534) ∨ p2766 ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4256))
    : (¬ p2534) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14061 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42986 (p1976 p2027 p2766 p3365 p3553 p3572 p4348 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14062 : (¬ p1976) ∨ p2027 ∨ p2766 ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4348))
    : (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14062 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42988 (p1976 p2027 p2766 p3055 p3584 p3956 p4347 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14064 : (¬ p1976) ∨ p2027 ∨ p2766 ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4347))
    : (¬ p3055) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14064 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42989 (p1977 p2027 p2202 p2573 p2589 p3574 p4111 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h14065 : (¬ p1977) ∨ p2027 ∨ p2202 ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3574) ∨ (¬ p4111))
    : (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3574) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h14065 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42990 (p1982 p2027 p2241 p2699 p2992 p3146 p3156 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14066 : (¬ p1982) ∨ p2027 ∨ (¬ p2241) ∨ p2699 ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p3156))
    : (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14066 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42991 (p1992 p2027 p2997 p3097 p3585 p3684 p4110 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14067 : (¬ p1992) ∨ p2027 ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p4110))
    : (¬ p3097) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3097 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h14067 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42995 (p1991 p2027 p2169 p2440 p2657 p3989 p4110 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14072 : (¬ p1991) ∨ p2027 ∨ p2169 ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3989) ∨ (¬ p4110))
    : (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3989) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h14072 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42996 (p1975 p2027 p2156 p2187 p2295 p2323 p2958 p3324 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14073 : (¬ p1975) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2295) ∨ p2323 ∨ (¬ p2958) ∨ (¬ p3324))
    : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2295) ∨ (¬ p2958) ∨ (¬ p3324) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h14073 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step42997 (p1992 p2027 p2588 p2741 p2997 p3564 p4037 p4111 p4194 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14074 : (¬ p1992) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2741) ∨ p2997 ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4111) ∨ (¬ p4194))
    : (¬ p2588) ∨ (¬ p2741) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4111) ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1992 := h2152;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2997) := h40890;
    (Or.elim h14074 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step42998 (p1992 p2027 p2764 p3584 p3585 p4137 p4191 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14075 : (¬ p1992) ∨ p2027 ∨ p2764 ∨ (¬ p3584) ∨ (¬ p3585) ∨ (¬ p4137) ∨ (¬ p4191))
    : (¬ p3584) ∨ (¬ p3585) ∨ (¬ p4137) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3584 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h14075 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step42999 (p1988 p2027 p2166 p2210 p2699 p3146 p3266 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14076 : (¬ p1988) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ p2699 ∨ (¬ p3146) ∨ (¬ p3266))
    : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3146) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14076 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43001 (p1992 p2027 p2588 p2651 p2741 p2963 p2997 p4111 p4389 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14078 : (¬ p1992) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (¬ p2963) ∨ p2997 ∨ (¬ p4111) ∨ (¬ p4389))
    : (¬ p2588) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (¬ p2963) ∨ (¬ p4111) ∨ (¬ p4389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1992 := h2152;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2997) := h40890;
    (Or.elim h14078 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u8 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43002 (p1990 p2148 p3051 p4555 : Prop)
    (h2150 : p1990)
    (h40865 : (¬ p2148))
    (h14079 : (¬ p1990) ∨ p2148 ∨ (¬ p3051) ∨ p4555)
    : (¬ p3051) ∨ p4555 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4555) := (fun h => hn (Or.inr h));
    let u2 : p1990 := h2150;
    let u3 : (¬ p2148) := h40865;
    (Or.elim h14079 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43003 (p2027 p2946 p3425 p4117 p4315 p4778 : Prop)
    (h40810 : (¬ p2027))
    (h14080 : p2027 ∨ (¬ p2946) ∨ (¬ p3425) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4778))
    : (¬ p2946) ∨ (¬ p3425) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h14080 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step43004 (p1992 p2027 p2542 p2589 p2914 p3363 p3585 p3742 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h14081 : (¬ p1992) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p2589) ∨ p2914 ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3742))
    : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2914) := h40887;
    (Or.elim h14081 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43005 (p1982 p2027 p2187 p2192 p2210 p2363 p2699 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14082 : (¬ p1982) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2363) ∨ p2699)
    : (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14082 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step43006 (p1992 p2027 p2202 p2563 p2743 p2952 p3361 p3952 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h14083 : (¬ p1992) ∨ p2027 ∨ p2202 ∨ (¬ p2563) ∨ (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3952))
    : (¬ p2563) ∨ (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h14083 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43007 (p1992 p2027 p2440 p2657 p2743 p2765 p3361 p4110 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14084 : (¬ p1992) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2743) ∨ p2765 ∨ (¬ p3361) ∨ (¬ p4110))
    : (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h14084 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43008 (p1992 p2027 p2743 p2766 p3361 p3414 p3553 p4348 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14085 : (¬ p1992) ∨ p2027 ∨ (¬ p2743) ∨ p2766 ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4348))
    : (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h14085 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43010 (p1992 p2027 p2633 p2696 p2743 p3425 p3659 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14087 : (¬ p1992) ∨ p2027 ∨ p2633 ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3425) ∨ (¬ p3659))
    : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3425) ∨ (¬ p3659) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h14087 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43011 (p1992 p2027 p2563 p2938 p3363 p3585 p3646 p3904 p4235 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h14088 : (¬ p1992) ∨ p2027 ∨ (¬ p2563) ∨ p2938 ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4235))
    : (¬ p2563) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1992 := h2152;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2938) := h40888;
    (Or.elim h14088 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43012 (p1994 p2027 p2598 p2622 p3201 p3365 p3742 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h14089 : (¬ p1994) ∨ p2027 ∨ (¬ p2598) ∨ p2622 ∨ (¬ p3201) ∨ (¬ p3365) ∨ (¬ p3742))
    : (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3365) ∨ (¬ p3742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h14089 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43013 (p1992 p2027 p2553 p2598 p3008 p3425 p3585 p4471 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h14090 : (¬ p1992) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2598) ∨ p3008 ∨ (¬ p3425) ∨ (¬ p3585) ∨ (¬ p4471))
    : (¬ p2553) ∨ (¬ p2598) ∨ (¬ p3425) ∨ (¬ p3585) ∨ (¬ p4471) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3008) := h40891;
    (Or.elim h14090 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43014 (p1992 p2027 p2387 p2598 p2766 p2778 p3585 p4347 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14091 : (¬ p1992) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2598) ∨ p2766 ∨ (¬ p2778) ∨ (¬ p3585) ∨ (¬ p4347))
    : (¬ p2387) ∨ (¬ p2598) ∨ (¬ p2778) ∨ (¬ p3585) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h14091 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43016 (p1992 p2027 p2352 p2387 p2588 p2785 p2997 p3688 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14093 : (¬ p1992) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p2785) ∨ p2997 ∨ (¬ p3688))
    : (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p2785) ∨ (¬ p3688) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h14093 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43018 (p1992 p2027 p2104 p2534 p2598 p2766 p3585 p5369 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14095 : (¬ p1992) ∨ p2027 ∨ (¬ p2104) ∨ (¬ p2534) ∨ (¬ p2598) ∨ p2766 ∨ (¬ p3585) ∨ (¬ p5369))
    : (¬ p2104) ∨ (¬ p2534) ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p5369) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h14095 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43020 (p1976 p2027 p2870 p3055 p3474 p3684 p4235 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h14097 : (¬ p1976) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p3055) ∨ p3474 ∨ (¬ p3684) ∨ (¬ p4235))
    : (¬ p2870) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3474) := h40898;
    (Or.elim h14097 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43021 (p1976 p2027 p2462 p2810 p3365 p3742 p4278 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h14098 : (¬ p1976) ∨ p2027 ∨ p2462 ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3742) ∨ (¬ p4278))
    : (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3742) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h14098 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43022 (p1995 p2027 p2499 p2914 p3019 p3323 p3742 p4137 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h14099 : (¬ p1995) ∨ p2027 ∨ (¬ p2499) ∨ p2914 ∨ (¬ p3019) ∨ (¬ p3323) ∨ (¬ p3742) ∨ (¬ p4137))
    : (¬ p2499) ∨ (¬ p3019) ∨ (¬ p3323) ∨ (¬ p3742) ∨ (¬ p4137) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2914) := h40887;
    (Or.elim h14099 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43023 (p1990 p2027 p2202 p2440 p3016 p3564 p3744 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h14100 : (¬ p1990) ∨ p2027 ∨ p2202 ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3744))
    : (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h14100 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43025 (p1976 p2027 p2440 p2810 p2938 p3365 p4235 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h14102 : (¬ p1976) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2810) ∨ p2938 ∨ (¬ p3365) ∨ (¬ p4235))
    : (¬ p2440) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h14102 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43029 (p1976 p2027 p2138 p2563 p2938 p3758 p4235 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h14106 : (¬ p1976) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2563) ∨ p2938 ∨ (¬ p3758) ∨ (¬ p4235))
    : (¬ p2138) ∨ (¬ p2563) ∨ (¬ p3758) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h14106 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43030 (p1990 p2027 p2156 p2901 p3497 p3556 p3578 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h14107 : (¬ p1990) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3556) ∨ p3578)
    : (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3578) := h40900;
    (Or.elim h14107 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step43033 (p1976 p2027 p2138 p2839 p2914 p3585 p3876 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h14110 : (¬ p1976) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2839) ∨ p2914 ∨ (¬ p3585) ∨ (¬ p3876))
    : (¬ p2138) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h14110 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43037 (p1992 p2027 p2169 p2363 p2534 p3573 p3584 p3585 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14148 : (¬ p1992) ∨ p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p3573) ∨ (¬ p3584) ∨ (¬ p3585))
    : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p3573) ∨ (¬ p3584) ∨ (¬ p3585) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h14148 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43040 (p2004 p2027 p2427 p2765 p3246 p3817 p4110 : Prop)
    (h2164 : p2004)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14153 : (¬ p2004) ∨ p2027 ∨ (¬ p2427) ∨ p2765 ∨ (¬ p3246) ∨ (¬ p3817) ∨ (¬ p4110))
    : (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3817) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2004 := h2164;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h14153 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43042 (p1975 p2027 p2241 p2553 p2699 p2727 p3016 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14155 : (¬ p1975) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2553) ∨ p2699 ∨ (¬ p2727) ∨ (¬ p3016))
    : (¬ p2241) ∨ (¬ p2553) ∨ (¬ p2727) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14155 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43043 (p1977 p2027 p2938 p2957 p3105 p3662 p4032 p4244 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h14156 : (¬ p1977) ∨ p2027 ∨ p2938 ∨ (¬ p2957) ∨ (¬ p3105) ∨ (¬ p3662) ∨ (¬ p4032) ∨ (¬ p4244))
    : (¬ p2957) ∨ (¬ p3105) ∨ (¬ p3662) ∨ (¬ p4032) ∨ (¬ p4244) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2938) := h40888;
    (Or.elim h14156 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43045 (p1997 p2938 p4948 p5104 : Prop)
    (h2157 : p1997)
    (h40888 : (¬ p2938))
    (h14158 : (¬ p1997) ∨ p2938 ∨ (¬ p4948) ∨ p5104)
    : (¬ p4948) ∨ p5104 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4948 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5104) := (fun h => hn (Or.inr h));
    let u2 : p1997 := h2157;
    let u3 : (¬ p2938) := h40888;
    (Or.elim h14158 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43046 (p1977 p2027 p2589 p2662 p2997 p3097 p4110 p4111 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14159 : (¬ p1977) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2662) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4111))
    : (¬ p2589) ∨ (¬ p2662) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h14159 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43047 (p1975 p2027 p2122 p2611 p2696 p2743 p2829 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14160 : (¬ p1975) ∨ p2027 ∨ (¬ p2122) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2829))
    : (¬ p2122) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14160 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43048 (p1975 p2027 p2295 p2611 p2774 p3483 p4037 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14161 : (¬ p1975) ∨ p2027 ∨ (¬ p2295) ∨ p2611 ∨ (¬ p2774) ∨ (¬ p3483) ∨ (¬ p4037))
    : (¬ p2295) ∨ (¬ p2774) ∨ (¬ p3483) ∨ (¬ p4037) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14161 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43050 (p1977 p2027 p2651 p2963 p3128 p4037 p4111 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40894 : (¬ p3128))
    (h14163 : (¬ p1977) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2963) ∨ p3128 ∨ (¬ p4037) ∨ (¬ p4111))
    : (¬ p2651) ∨ (¬ p2963) ∨ (¬ p4037) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3128) := h40894;
    (Or.elim h14163 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43052 (p2002 p2027 p2914 p3016 p3742 p3888 p4329 : Prop)
    (h2162 : p2002)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h14182 : (¬ p2002) ∨ p2027 ∨ p2914 ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3888) ∨ (¬ p4329))
    : (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3888) ∨ (¬ p4329) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2002 := h2162;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h14182 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43053 (p2000 p2027 p2169 p2579 p3737 p3989 p5514 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14183 : (¬ p2000) ∨ p2027 ∨ p2169 ∨ (¬ p2579) ∨ (¬ p3737) ∨ (¬ p3989) ∨ (¬ p5514))
    : (¬ p2579) ∨ (¬ p3737) ∨ (¬ p3989) ∨ (¬ p5514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2000 := h2160;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h14183 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43054 (p1995 p2027 p2764 p3238 p3744 p4110 p4191 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14184 : (¬ p1995) ∨ p2027 ∨ p2764 ∨ (¬ p3238) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4191))
    : (¬ p3238) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3238 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h14184 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43055 (p2000 p2027 p2169 p2579 p3125 p3989 p4137 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14185 : (¬ p2000) ∨ p2027 ∨ p2169 ∨ (¬ p2579) ∨ (¬ p3125) ∨ (¬ p3989) ∨ (¬ p4137))
    : (¬ p2579) ∨ (¬ p3125) ∨ (¬ p3989) ∨ (¬ p4137) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2000 := h2160;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h14185 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43056 (p1990 p2027 p2608 p2699 p2819 p2829 p3989 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14186 : (¬ p1990) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3989))
    : (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3989) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14186 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43057 (p1991 p2027 p2657 p2766 p3574 p3956 p4347 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14187 : (¬ p1991) ∨ p2027 ∨ (¬ p2657) ∨ p2766 ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4347))
    : (¬ p2657) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14187 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43059 (p1983 p2027 p2132 p2274 p2396 p2611 p2860 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14189 : (¬ p1983) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2274) ∨ (¬ p2396) ∨ p2611 ∨ (¬ p2860))
    : (¬ p2132) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14189 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43060 (p1985 p2027 p2287 p2870 p3323 p3744 p3758 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h14190 : (¬ p1985) ∨ p2027 ∨ p2287 ∨ (¬ p2870) ∨ (¬ p3323) ∨ (¬ p3744) ∨ (¬ p3758))
    : (¬ p2870) ∨ (¬ p3323) ∨ (¬ p3744) ∨ (¬ p3758) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2287) := h40869;
    (Or.elim h14190 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43061 (p1975 p2027 p2295 p2696 p2699 p2743 p2829 p3589 p4328 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14191 : (¬ p1975) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2696) ∨ p2699 ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3589) ∨ (¬ p4328))
    : (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3589) ∨ (¬ p4328) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1975 := h2135;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2699) := h40881;
    (Or.elim h14191 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43062 (p1985 p2027 p2132 p2611 p2860 p2901 p3952 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14192 : (¬ p1985) ∨ p2027 ∨ (¬ p2132) ∨ p2611 ∨ (¬ p2860) ∨ (¬ p2901) ∨ (¬ p3952))
    : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p2901) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14192 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43064 (p1977 p2027 p2633 p2946 p3414 p3553 p3662 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14194 : (¬ p1977) ∨ p2027 ∨ p2633 ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3662))
    : (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h14194 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43065 (p1983 p2027 p2299 p2396 p2699 p3399 p3527 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14195 : (¬ p1983) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2396) ∨ p2699 ∨ (¬ p3399) ∨ (¬ p3527))
    : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3399) ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14195 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43066 (p1998 p2027 p2437 p2611 p2630 p2696 p2911 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14196 : (¬ p1998) ∨ p2027 ∨ (¬ p2437) ∨ p2611 ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2911))
    : (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14196 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43070 (p2027 p2651 p2737 p2811 p3583 p4316 p4701 : Prop)
    (h40810 : (¬ p2027))
    (h14200 : p2027 ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3583) ∨ (¬ p4316) ∨ (¬ p4701))
    : (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3583) ∨ (¬ p4316) ∨ (¬ p4701) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4701 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h14200 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step43071 (p1984 p2027 p2928 p3008 p3201 p3452 p3584 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h14201 : (¬ p1984) ∨ p2027 ∨ (¬ p2928) ∨ p3008 ∨ (¬ p3201) ∨ (¬ p3452) ∨ (¬ p3584))
    : (¬ p2928) ∨ (¬ p3201) ∨ (¬ p3452) ∨ (¬ p3584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2928 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3008) := h40891;
    (Or.elim h14201 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43072 (p1975 p2027 p2274 p2323 p2542 p2563 p2651 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14202 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ p2323 ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2651))
    : (¬ p2274) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14202 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43073 (p1998 p2027 p2177 p2417 p2842 p3422 p3920 p4107 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h14203 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2417) ∨ p2842 ∨ (¬ p3422) ∨ (¬ p3920) ∨ (¬ p4107))
    : (¬ p2177) ∨ (¬ p2417) ∨ (¬ p3422) ∨ (¬ p3920) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2842) := h40885;
    (Or.elim h14203 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43074 (p1976 p2027 p2138 p2765 p3156 p3694 p3952 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14204 : (¬ p1976) ∨ p2027 ∨ (¬ p2138) ∨ p2765 ∨ (¬ p3156) ∨ (¬ p3694) ∨ (¬ p3952))
    : (¬ p2138) ∨ (¬ p3156) ∨ (¬ p3694) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h14204 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43078 (p1992 p2027 p2138 p2696 p2743 p2765 p3758 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14208 : (¬ p1992) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2743) ∨ p2765 ∨ (¬ p3758))
    : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3758) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h14208 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43079 (p1981 p2027 p2608 p2699 p2819 p3309 p3822 p4869 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14209 : (¬ p1981) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2819) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p4869))
    : (¬ p2608) ∨ (¬ p2819) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p4869) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1981 := h2141;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14209 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43080 (p1998 p2027 p2122 p2177 p2608 p2699 p2829 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14210 : (¬ p1998) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2829))
    : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2608) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14210 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43081 (p1998 p2027 p2177 p2241 p2295 p2641 p2699 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14211 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ p2699)
    : (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14211 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step43082 (p1998 p2027 p2253 p2264 p2331 p2699 p3027 p4154 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14212 : (¬ p1998) ∨ p2027 ∨ (¬ p2253) ∨ (¬ p2264) ∨ (¬ p2331) ∨ p2699 ∨ (¬ p3027) ∨ (¬ p4154))
    : (¬ p2253) ∨ (¬ p2264) ∨ (¬ p2331) ∨ (¬ p3027) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14212 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43083 (p1981 p2027 p2323 p2352 p2663 p3016 p3389 p3742 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14213 : (¬ p1981) ∨ p2027 ∨ p2323 ∨ (¬ p2352) ∨ (¬ p2663) ∨ (¬ p3016) ∨ (¬ p3389) ∨ (¬ p3742))
    : (¬ p2352) ∨ (¬ p2663) ∨ (¬ p3016) ∨ (¬ p3389) ∨ (¬ p3742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1981 := h2141;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h14213 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43087 (p1996 p2027 p2241 p2396 p2699 p3309 p3947 p4759 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14217 : (¬ p1996) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2396) ∨ p2699 ∨ (¬ p3309) ∨ (¬ p3947) ∨ (¬ p4759))
    : (¬ p2241) ∨ (¬ p2396) ∨ (¬ p3309) ∨ (¬ p3947) ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1996 := h2156;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14217 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43088 (p1988 p2027 p2396 p2611 p2761 p2774 p3309 p3918 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14218 : (¬ p1988) ∨ p2027 ∨ (¬ p2396) ∨ p2611 ∨ (¬ p2761) ∨ (¬ p2774) ∨ (¬ p3309) ∨ (¬ p3918))
    : (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2774) ∨ (¬ p3309) ∨ (¬ p3918) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h14218 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43089 (p1995 p2027 p2230 p2764 p3238 p3346 p4425 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14219 : (¬ p1995) ∨ p2027 ∨ (¬ p2230) ∨ p2764 ∨ (¬ p3238) ∨ (¬ p3346) ∨ (¬ p4425))
    : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3346) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h14219 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43090 (p1988 p2027 p2241 p2449 p2699 p2761 p3027 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14220 : (¬ p1988) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2449) ∨ p2699 ∨ (¬ p2761) ∨ (¬ p3027))
    : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p3027) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14220 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43091 (p1977 p2027 p2938 p3005 p4315 p4320 p4360 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h14221 : (¬ p1977) ∨ p2027 ∨ p2938 ∨ (¬ p3005) ∨ (¬ p4315) ∨ (¬ p4320) ∨ (¬ p4360))
    : (¬ p3005) ∨ (¬ p4315) ∨ (¬ p4320) ∨ (¬ p4360) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h14221 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43092 (p1995 p2027 p2230 p2476 p2545 p3083 p3238 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h14222 : (¬ p1995) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2476) ∨ p2545 ∨ (¬ p3083) ∨ (¬ p3238))
    : (¬ p2230) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p3238) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h14222 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43096 (p2010 p2027 p2608 p3201 p3367 p3623 p4366 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40903 : (¬ p3623))
    (h14226 : (¬ p2010) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3201) ∨ (¬ p3367) ∨ p3623 ∨ (¬ p4366))
    : (¬ p2608) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2010 := h2170;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3623) := h40903;
    (Or.elim h14226 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43098 (p1994 p2027 p2727 p2938 p2996 p3246 p3947 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h14228 : (¬ p1994) ∨ p2027 ∨ (¬ p2727) ∨ p2938 ∨ (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3947))
    : (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h14228 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43101 (p1995 p2027 p3008 p3238 p3584 p3609 p3697 p3857 p4031 p4354 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h14231 : (¬ p1995) ∨ p2027 ∨ p3008 ∨ (¬ p3238) ∨ (¬ p3584) ∨ (¬ p3609) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4031) ∨ (¬ p4354))
    : (¬ p3238) ∨ (¬ p3584) ∨ (¬ p3609) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4031) ∨ (¬ p4354) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3238 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4354 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p1995 := h2155;
    let u8 : (¬ p2027) := h40810;
    let u9 : (¬ p3008) := h40891;
    (Or.elim h14231 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u9 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step43105 (p1975 p2027 p2323 p2331 p2668 p3309 p3923 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14236 : (¬ p1975) ∨ p2027 ∨ p2323 ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3309) ∨ (¬ p3923))
    : (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3309) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14236 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43108 (p1995 p2027 p2187 p2386 p2387 p2499 p2997 p3097 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14239 : (¬ p1995) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2386) ∨ (¬ p2387) ∨ (¬ p2499) ∨ p2997 ∨ (¬ p3097))
    : (¬ p2187) ∨ (¬ p2386) ∨ (¬ p2387) ∨ (¬ p2499) ∨ (¬ p3097) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h14239 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43109 (p1997 p2027 p2766 p3266 p3744 p4110 p4191 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14240 : (¬ p1997) ∨ p2027 ∨ p2766 ∨ (¬ p3266) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4191))
    : (¬ p3266) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14240 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43111 (p1983 p2027 p2241 p2699 p3027 p3506 p4381 p4661 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14242 : (¬ p1983) ∨ p2027 ∨ (¬ p2241) ∨ p2699 ∨ (¬ p3027) ∨ (¬ p3506) ∨ (¬ p4381) ∨ (¬ p4661))
    : (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3506) ∨ (¬ p4381) ∨ (¬ p4661) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1983 := h2143;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14242 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43114 (p1995 p2027 p2169 p2230 p2579 p3096 p3238 p3989 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14245 : (¬ p1995) ∨ p2027 ∨ p2169 ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p3238) ∨ (¬ p3989))
    : (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p3238) ∨ (¬ p3989) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h14245 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43116 (p2020 p3941 p3944 p5559 : Prop)
    (h2180 : p2020)
    (h40908 : (¬ p3944))
    (h14281 : (¬ p2020) ∨ (¬ p3941) ∨ p3944 ∨ p5559)
    : (¬ p3941) ∨ p5559 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5559) := (fun h => hn (Or.inr h));
    let u2 : p2020 := h2180;
    let u3 : (¬ p3944) := h40908;
    (Or.elim h14281 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43117 (p1976 p2027 p2138 p2766 p3266 p4322 p4385 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14282 : (¬ p1976) ∨ p2027 ∨ (¬ p2138) ∨ p2766 ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4385))
    : (¬ p2138) ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4385) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14282 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43118 (p1992 p2027 p2166 p2210 p2699 p3583 p3694 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14283 : (¬ p1992) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ p2699 ∨ (¬ p3583) ∨ (¬ p3694))
    : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3583) ∨ (¬ p3694) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14283 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43122 (p1997 p2027 p2241 p2699 p2901 p2992 p4235 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14288 : (¬ p1997) ∨ p2027 ∨ (¬ p2241) ∨ p2699 ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4235))
    : (¬ p2241) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14288 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43123 (p1982 p2027 p2241 p2264 p2459 p2699 p3027 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14289 : (¬ p1982) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2459) ∨ p2699 ∨ (¬ p3027))
    : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p3027) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14289 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43124 (p1988 p2027 p2459 p2699 p3266 p3399 p3527 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14290 : (¬ p1988) ∨ p2027 ∨ (¬ p2459) ∨ p2699 ∨ (¬ p3266) ∨ (¬ p3399) ∨ (¬ p3527))
    : (¬ p2459) ∨ (¬ p3266) ∨ (¬ p3399) ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14290 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43125 (p1982 p2027 p2459 p3399 p3527 p3591 p3818 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40905 : (¬ p3818))
    (h14291 : (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3591) ∨ p3818)
    : (¬ p2459) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3591) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3818) := h40905;
    (Or.elim h14291 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step43126 (p1983 p2027 p2449 p2699 p3399 p3527 p3553 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14292 : (¬ p1983) ∨ p2027 ∨ (¬ p2449) ∨ p2699 ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3553))
    : (¬ p2449) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14292 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43127 (p1983 p2027 p2699 p3246 p3399 p3527 p3570 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14293 : (¬ p1983) ∨ p2027 ∨ p2699 ∨ (¬ p3246) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570))
    : (¬ p3246) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14293 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43129 (p1986 p2027 p2352 p3008 p3367 p3688 p4358 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h14295 : (¬ p1986) ∨ p2027 ∨ (¬ p2352) ∨ p3008 ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4358))
    : (¬ p2352) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1986 := h2146;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3008) := h40891;
    (Or.elim h14295 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43130 (p2027 p2780 p3471 p3549 p4475 p4867 : Prop)
    (h40810 : (¬ p2027))
    (h14296 : p2027 ∨ (¬ p2780) ∨ (¬ p3471) ∨ (¬ p3549) ∨ (¬ p4475) ∨ (¬ p4867))
    : (¬ p2780) ∨ (¬ p3471) ∨ (¬ p3549) ∨ (¬ p4475) ∨ (¬ p4867) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2780 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4867 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h14296 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step43131 (p2015 p2611 p2774 p4867 : Prop)
    (h2175 : p2015)
    (h40877 : (¬ p2611))
    (h14297 : (¬ p2015) ∨ p2611 ∨ (¬ p2774) ∨ p4867)
    : (¬ p2774) ∨ p4867 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4867) := (fun h => hn (Or.inr h));
    let u2 : p2015 := h2175;
    let u3 : (¬ p2611) := h40877;
    (Or.elim h14297 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43133 (p1975 p2027 p2765 p2951 p3051 p3246 p3952 p4107 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14299 : (¬ p1975) ∨ p2027 ∨ p2765 ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3952) ∨ (¬ p4107))
    : (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3952) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2951 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h14299 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43136 (p1992 p2027 p2274 p2743 p2765 p3568 p4195 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14302 : (¬ p1992) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2743) ∨ p2765 ∨ (¬ p3568) ∨ (¬ p4195))
    : (¬ p2274) ∨ (¬ p2743) ∨ (¬ p3568) ∨ (¬ p4195) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h14302 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43137 (p1976 p2027 p2997 p3097 p3365 p3952 p4315 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14303 : (¬ p1976) ∨ p2027 ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3365) ∨ (¬ p3952) ∨ (¬ p4315))
    : (¬ p3097) ∨ (¬ p3365) ∨ (¬ p3952) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3097 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h14303 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43138 (p1995 p2388 p3238 p4705 : Prop)
    (h2155 : p1995)
    (h40873 : (¬ p2388))
    (h14304 : (¬ p1995) ∨ p2388 ∨ (¬ p3238) ∨ p4705)
    : (¬ p3238) ∨ p4705 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3238 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4705) := (fun h => hn (Or.inr h));
    let u2 : p1995 := h2155;
    let u3 : (¬ p2388) := h40873;
    (Or.elim h14304 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43139 (p1982 p2027 p2274 p2313 p2363 p2765 p3063 p3204 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14305 : (¬ p1982) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2363) ∨ p2765 ∨ (¬ p3063) ∨ (¬ p3204))
    : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3204) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h14305 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43140 (p2005 p2027 p2230 p2476 p2493 p3238 p3498 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40899 : (¬ p3498))
    (h14307 : (¬ p2005) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2493) ∨ (¬ p3238) ∨ p3498)
    : (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2493) ∨ (¬ p3238) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3498) := h40899;
    (Or.elim h14307 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step43141 (p2027 p2499 p2797 p2810 p3984 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h14308 : p2027 ∨ (¬ p2499) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3984) ∨ (¬ p4811))
    : (¬ p2499) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3984) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h14308 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step43142 (p1992 p2027 p2766 p3570 p3583 p4244 p4348 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14309 : (¬ p1992) ∨ p2027 ∨ p2766 ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p4244) ∨ (¬ p4348))
    : (¬ p3570) ∨ (¬ p3583) ∨ (¬ p4244) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3570 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14309 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43145 (p1998 p2027 p2264 p2323 p2651 p3027 p4111 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14312 : (¬ p1998) ∨ p2027 ∨ (¬ p2264) ∨ p2323 ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p4111))
    : (¬ p2264) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14312 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43146 (p1981 p2027 p2241 p2352 p2699 p2727 p3016 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14313 : (¬ p1981) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2352) ∨ p2699 ∨ (¬ p2727) ∨ (¬ p3016))
    : (¬ p2241) ∨ (¬ p2352) ∨ (¬ p2727) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14313 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43149 (p1983 p2027 p2241 p2417 p2437 p2699 p2727 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14316 : (¬ p1983) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2417) ∨ (¬ p2437) ∨ p2699 ∨ (¬ p2727))
    : (¬ p2241) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14316 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43152 (p2005 p2027 p2187 p2387 p2765 p3654 p4137 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14319 : (¬ p2005) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2387) ∨ p2765 ∨ (¬ p3654) ∨ (¬ p4137))
    : (¬ p2187) ∨ (¬ p2387) ∨ (¬ p3654) ∨ (¬ p4137) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h14319 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43155 (p1992 p2027 p2132 p2169 p2780 p3583 p4358 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14322 : (¬ p1992) ∨ p2027 ∨ (¬ p2132) ∨ p2169 ∨ (¬ p2780) ∨ (¬ p3583) ∨ (¬ p4358))
    : (¬ p2132) ∨ (¬ p2780) ∨ (¬ p3583) ∨ (¬ p4358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h14322 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43156 (p1975 p2027 p2274 p2459 p2633 p3989 p4347 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14323 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2459) ∨ p2633 ∨ (¬ p3989) ∨ (¬ p4347))
    : (¬ p2274) ∨ (¬ p2459) ∨ (¬ p3989) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h14323 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43157 (p2015 p2027 p2352 p2493 p2699 p3379 p3923 : Prop)
    (h2175 : p2015)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14324 : (¬ p2015) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2493) ∨ p2699 ∨ (¬ p3379) ∨ (¬ p3923))
    : (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2015 := h2175;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14324 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43158 (p2005 p2027 p2406 p2440 p2699 p3016 p3379 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14325 : (¬ p2005) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2440) ∨ p2699 ∨ (¬ p3016) ∨ (¬ p3379))
    : (¬ p2406) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14325 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43161 (p1990 p2027 p2148 p2307 p2962 p3063 p3549 p3989 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h14328 : (¬ p1990) ∨ p2027 ∨ p2148 ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3989))
    : (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3989) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2148) := h40865;
    (Or.elim h14328 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43162 (p1981 p2027 p2187 p2406 p2563 p2699 p3379 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14329 : (¬ p1981) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2406) ∨ (¬ p2563) ∨ p2699 ∨ (¬ p3379))
    : (¬ p2187) ∨ (¬ p2406) ∨ (¬ p2563) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14329 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43163 (p1992 p2027 p2104 p2132 p2766 p3583 p3692 p4740 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14330 : (¬ p1992) ∨ p2027 ∨ (¬ p2104) ∨ (¬ p2132) ∨ p2766 ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p4740))
    : (¬ p2104) ∨ (¬ p2132) ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p4740) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h14330 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43164 (p1979 p2688 p2751 p2811 p2946 : Prop)
    (h2139 : p1979)
    (h40880 : (¬ p2688))
    (h14331 : (¬ p1979) ∨ p2688 ∨ p2751 ∨ (¬ p2811) ∨ (¬ p2946))
    : p2751 ∨ (¬ p2811) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2751) := (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p1979 := h2139;
    let u4 : (¬ p2688) := h40880;
    (Or.elim h14331 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step43165 (p2005 p2027 p2241 p2295 p2588 p2641 p2699 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14332 : (¬ p2005) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2588) ∨ (¬ p2641) ∨ p2699)
    : (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2588) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14332 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step43167 (p1989 p2027 p2191 p2545 p2657 p2946 p3156 : Prop)
    (h2149 : p1989)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h14334 : (¬ p1989) ∨ p2027 ∨ (¬ p2191) ∨ p2545 ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3156))
    : (¬ p2191) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1989 := h2149;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h14334 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43169 (p1987 p2027 p2138 p2696 p2766 p3692 p3694 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14336 : (¬ p1987) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2696) ∨ p2766 ∨ (¬ p3692) ∨ (¬ p3694))
    : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p3692) ∨ (¬ p3694) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14336 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43170 (p1992 p2027 p2307 p2545 p2797 p2810 p3549 p3567 p3953 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h14338 : (¬ p1992) ∨ p2027 ∨ (¬ p2307) ∨ p2545 ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p3953))
    : (¬ p2307) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p3953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1992 := h2152;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2545) := h40876;
    (Or.elim h14338 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43174 (p1990 p2027 p2166 p2563 p2699 p3379 p3880 p3948 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14343 : (¬ p1990) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2563) ∨ p2699 ∨ (¬ p3379) ∨ (¬ p3880) ∨ (¬ p3948))
    : (¬ p2166) ∨ (¬ p2563) ∨ (¬ p3379) ∨ (¬ p3880) ∨ (¬ p3948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14343 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43178 (p1987 p2027 p2462 p2946 p3414 p3690 p3699 p4315 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h14347 : (¬ p1987) ∨ p2027 ∨ p2462 ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3690) ∨ (¬ p3699) ∨ (¬ p4315))
    : (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3690) ∨ (¬ p3699) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2462) := h40875;
    (Or.elim h14347 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43179 (p1979 p2027 p2598 p2699 p2737 p3136 p3585 p3589 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14348 : (¬ p1979) ∨ p2027 ∨ (¬ p2598) ∨ p2699 ∨ (¬ p2737) ∨ (¬ p3136) ∨ (¬ p3585) ∨ (¬ p3589))
    : (¬ p2598) ∨ (¬ p2737) ∨ (¬ p3136) ∨ (¬ p3585) ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1979 := h2139;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14348 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43181 (p1989 p2027 p2210 p2459 p2633 p3544 p3692 p3906 p4366 : Prop)
    (h2149 : p1989)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14350 : (¬ p1989) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2459) ∨ p2633 ∨ (¬ p3544) ∨ (¬ p3692) ∨ (¬ p3906) ∨ (¬ p4366))
    : (¬ p2210) ∨ (¬ p2459) ∨ (¬ p3544) ∨ (¬ p3692) ∨ (¬ p3906) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1989 := h2149;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2633) := h40879;
    (Or.elim h14350 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43183 (p1998 p2027 p2114 p2363 p2383 p2584 p3367 p3759 p4348 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h14352 : (¬ p1998) ∨ p2027 ∨ p2114 ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4348))
    : (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1998 := h2158;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2114) := h40864;
    (Or.elim h14352 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43185 (p1998 p2027 p2598 p2699 p2707 p2911 p3585 p3589 p3658 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14354 : (¬ p1998) ∨ p2027 ∨ (¬ p2598) ∨ p2699 ∨ (¬ p2707) ∨ (¬ p2911) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3658))
    : (¬ p2598) ∨ (¬ p2707) ∨ (¬ p2911) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3658) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1998 := h2158;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2699) := h40881;
    (Or.elim h14354 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43187 (p2005 p2027 p2331 p2545 p2657 p2668 p3956 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h14356 : (¬ p2005) ∨ p2027 ∨ (¬ p2331) ∨ p2545 ∨ (¬ p2657) ∨ (¬ p2668) ∨ (¬ p3956))
    : (¬ p2331) ∨ (¬ p2657) ∨ (¬ p2668) ∨ (¬ p3956) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h14356 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43203 (p1985 p2027 p2323 p2437 p2651 p2911 p3570 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14373 : (¬ p1985) ∨ p2027 ∨ p2323 ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3570))
    : (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14373 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43208 (p1975 p2027 p2295 p2383 p2860 p3324 p3474 p3743 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h14378 : (¬ p1975) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2860) ∨ (¬ p3324) ∨ p3474 ∨ (¬ p3743))
    : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2860) ∨ (¬ p3324) ∨ (¬ p3743) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3474) := h40898;
    (Or.elim h14378 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43209 (p1975 p2027 p2202 p2295 p2383 p2584 p2589 p3324 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h14379 : (¬ p1975) ∨ p2027 ∨ p2202 ∨ (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2589) ∨ (¬ p3324))
    : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2589) ∨ (¬ p3324) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h14379 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43210 (p1975 p2027 p2295 p2352 p2842 p3324 p3422 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h14380 : (¬ p1975) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2352) ∨ p2842 ∨ (¬ p3324) ∨ (¬ p3422))
    : (¬ p2295) ∨ (¬ p2352) ∨ (¬ p3324) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2842) := h40885;
    (Or.elim h14380 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43213 (p1981 p2027 p2295 p2313 p2383 p2641 p2688 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h14383 : (¬ p1981) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p2641) ∨ p2688)
    : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h14383 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step43214 (p1981 p2027 p2323 p2946 p3146 p3156 p4347 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14384 : (¬ p1981) ∨ p2027 ∨ p2323 ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4347))
    : (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14384 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43217 (p1992 p2027 p2608 p2766 p3659 p4348 p4366 p4424 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14387 : (¬ p1992) ∨ p2027 ∨ (¬ p2608) ∨ p2766 ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4424))
    : (¬ p2608) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4424) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h14387 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43219 (p1996 p2027 p2202 p2417 p3201 p3684 p3947 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h14389 : (¬ p1996) ∨ p2027 ∨ p2202 ∨ (¬ p2417) ∨ (¬ p3201) ∨ (¬ p3684) ∨ (¬ p3947))
    : (¬ p2417) ∨ (¬ p3201) ∨ (¬ p3684) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1996 := h2156;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h14389 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43221 (p1988 p3266 p3982 p5118 : Prop)
    (h2148 : p1988)
    (h40909 : (¬ p3982))
    (h14425 : (¬ p1988) ∨ (¬ p3266) ∨ p3982 ∨ p5118)
    : (¬ p3266) ∨ p5118 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5118) := (fun h => hn (Or.inr h));
    let u2 : p1988 := h2148;
    let u3 : (¬ p3982) := h40909;
    (Or.elim h14425 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43222 (p1975 p2027 p2274 p2284 p2611 p2696 p3136 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14426 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2284) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p3136))
    : (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2696) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14426 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43223 (p1975 p2027 p2274 p2611 p2797 p2946 p3986 p4117 p4315 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14427 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ p2611 ∨ (¬ p2797) ∨ (¬ p2946) ∨ (¬ p3986) ∨ (¬ p4117) ∨ (¬ p4315))
    : (¬ p2274) ∨ (¬ p2797) ∨ (¬ p2946) ∨ (¬ p3986) ∨ (¬ p4117) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1975 := h2135;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2611) := h40877;
    (Or.elim h14427 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43224 (p1994 p2027 p2323 p2383 p2630 p3324 p3987 p4195 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14428 : (¬ p1994) ∨ p2027 ∨ p2323 ∨ (¬ p2383) ∨ (¬ p2630) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4195))
    : (¬ p2383) ∨ (¬ p2630) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4195) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h14428 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43225 (p2000 p2027 p2633 p3333 p3346 p3644 p3876 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14429 : (¬ p2000) ∨ p2027 ∨ p2633 ∨ (¬ p3333) ∨ (¬ p3346) ∨ (¬ p3644) ∨ (¬ p3876))
    : (¬ p3333) ∨ (¬ p3346) ∨ (¬ p3644) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2000 := h2160;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h14429 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43226 (p1988 p2027 p2284 p2323 p2946 p3125 p3461 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14430 : (¬ p1988) ∨ p2027 ∨ (¬ p2284) ∨ p2323 ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3461))
    : (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14430 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43227 (p1988 p2027 p2323 p2946 p3146 p3156 p3266 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14431 : (¬ p1988) ∨ p2027 ∨ p2323 ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3266))
    : (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14431 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43228 (p1975 p2027 p2323 p2383 p2449 p3324 p3987 p4107 p4156 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14432 : (¬ p1975) ∨ p2027 ∨ p2323 ∨ (¬ p2383) ∨ (¬ p2449) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4107) ∨ (¬ p4156))
    : (¬ p2383) ∨ (¬ p2449) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4107) ∨ (¬ p4156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1975 := h2135;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2323) := h40870;
    (Or.elim h14432 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43231 (p1975 p2027 p2622 p2707 p2743 p3434 p4107 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h14435 : (¬ p1975) ∨ p2027 ∨ p2622 ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3434) ∨ (¬ p4107))
    : (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3434) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h14435 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43232 (p1999 p2027 p2210 p2247 p2284 p2688 p3125 p4282 : Prop)
    (h2159 : p1999)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h14436 : (¬ p1999) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2284) ∨ p2688 ∨ (¬ p3125) ∨ (¬ p4282))
    : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2284) ∨ (¬ p3125) ∨ (¬ p4282) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1999 := h2159;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h14436 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43236 (p1994 p2027 p2622 p2743 p3201 p3367 p3742 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h14440 : (¬ p1994) ∨ p2027 ∨ p2622 ∨ (¬ p2743) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3742))
    : (¬ p2743) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h14440 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43237 (p1975 p2027 p2114 p2274 p2284 p2737 p2811 p2946 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h14441 : (¬ p1975) ∨ p2027 ∨ p2114 ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2946))
    : (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h14441 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43242 (p2020 p2027 p2611 p2696 p3136 p3156 p3969 : Prop)
    (h2180 : p2020)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14446 : (¬ p2020) ∨ p2027 ∨ p2611 ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3969))
    : (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3969) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2020 := h2180;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14446 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43251 (p1982 p2027 p2323 p2533 p2946 p3156 p3680 p4444 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14455 : (¬ p1982) ∨ p2027 ∨ p2323 ∨ (¬ p2533) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3680) ∨ (¬ p4444))
    : (¬ p2533) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3680) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2533 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h14455 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43252 (p1975 p2027 p2274 p3622 p3670 p3744 p4191 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40902 : (¬ p3622))
    (h14456 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ p3622 ∨ (¬ p3670) ∨ (¬ p3744) ∨ (¬ p4191))
    : (¬ p2274) ∨ (¬ p3670) ∨ (¬ p3744) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3622) := h40902;
    (Or.elim h14456 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43256 (p1994 p2027 p3008 p3434 p3584 p3742 p4278 p5085 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h14460 : (¬ p1994) ∨ p2027 ∨ p3008 ∨ (¬ p3434) ∨ (¬ p3584) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p5085))
    : (¬ p3434) ∨ (¬ p3584) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p5085) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5085 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3008) := h40891;
    (Or.elim h14460 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43261 (p2008 p2027 p2417 p2579 p3008 p3389 p4324 : Prop)
    (h2168 : p2008)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h14465 : (¬ p2008) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p2579) ∨ p3008 ∨ (¬ p3389) ∨ (¬ p4324))
    : (¬ p2417) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4324) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2008 := h2168;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3008) := h40891;
    (Or.elim h14465 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43264 (p1994 p2027 p2202 p3434 p3684 p3742 p4278 p5085 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h14469 : (¬ p1994) ∨ p2027 ∨ p2202 ∨ (¬ p3434) ∨ (¬ p3684) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p5085))
    : (¬ p3434) ∨ (¬ p3684) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p5085) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5085 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h14469 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43265 (p2020 p2964 p3276 p5119 : Prop)
    (h2180 : p2020)
    (h40889 : (¬ p2964))
    (h14470 : (¬ p2020) ∨ p2964 ∨ (¬ p3276) ∨ p5119)
    : (¬ p3276) ∨ p5119 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5119) := (fun h => hn (Or.inr h));
    let u2 : p2020 := h2180;
    let u3 : (¬ p2964) := h40889;
    (Or.elim h14470 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43270 (p1990 p2027 p2284 p2657 p2688 p2727 p2946 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h14492 : (¬ p1990) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2657) ∨ p2688 ∨ (¬ p2727) ∨ (¬ p2946))
    : (¬ p2284) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h14492 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43271 (p1984 p2027 p2247 p2633 p3644 p3742 p4111 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14493 : (¬ p1984) ∨ p2027 ∨ (¬ p2247) ∨ p2633 ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4111))
    : (¬ p2247) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h14493 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43272 (p1992 p2027 p2766 p3363 p3540 p3585 p3644 p4348 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14494 : (¬ p1992) ∨ p2027 ∨ p2766 ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p3644) ∨ (¬ p4348))
    : (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p3644) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h14494 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43273 (p1975 p2027 p2274 p2284 p2545 p2657 p2946 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h14495 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2284) ∨ p2545 ∨ (¬ p2657) ∨ (¬ p2946))
    : (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2657) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h14495 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43274 (p1975 p2027 p2274 p2764 p3989 p4138 p4348 p4444 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14496 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ p2764 ∨ (¬ p3989) ∨ (¬ p4138) ∨ (¬ p4348) ∨ (¬ p4444))
    : (¬ p2274) ∨ (¬ p3989) ∨ (¬ p4138) ∨ (¬ p4348) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h14496 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43275 (p1998 p2027 p2177 p2274 p2284 p2323 p2946 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14497 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2284) ∨ p2323 ∨ (¬ p2946))
    : (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14497 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43277 (p2021 p2027 p2202 p3276 p3333 p3684 p3773 : Prop)
    (h2181 : p2021)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h14499 : (¬ p2021) ∨ p2027 ∨ p2202 ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3684) ∨ (¬ p3773))
    : (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3684) ∨ (¬ p3773) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2021 := h2181;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h14499 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43278 (p2027 p2589 p3389 p3742 p3948 p4210 p4814 : Prop)
    (h40810 : (¬ p2027))
    (h14500 : p2027 ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p3948) ∨ (¬ p4210) ∨ (¬ p4814))
    : (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p3948) ∨ (¬ p4210) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h14500 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step43279 (p1982 p2027 p2323 p2352 p2363 p2651 p3016 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14501 : (¬ p1982) ∨ p2027 ∨ p2323 ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2651) ∨ (¬ p3016))
    : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2651) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14501 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43281 (p1975 p2027 p2611 p2797 p2946 p3125 p3986 p4025 p4117 p4315 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14503 : (¬ p1975) ∨ p2027 ∨ p2611 ∨ (¬ p2797) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3986) ∨ (¬ p4025) ∨ (¬ p4117) ∨ (¬ p4315))
    : (¬ p2797) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3986) ∨ (¬ p4025) ∨ (¬ p4117) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p1975 := h2135;
    let u8 : (¬ p2027) := h40810;
    let u9 : (¬ p2611) := h40877;
    (Or.elim h14503 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u9 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step43282 (p1984 p2027 p2766 p3588 p3659 p3954 p4348 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14504 : (¬ p1984) ∨ p2027 ∨ p2766 ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4348))
    : (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14504 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43283 (p1975 p2027 p2274 p2323 p2331 p2668 p3989 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14505 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ p2323 ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3989))
    : (¬ p2274) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3989) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14505 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43285 (p1994 p2202 p3684 p4753 : Prop)
    (h2154 : p1994)
    (h40867 : (¬ p2202))
    (h14507 : (¬ p1994) ∨ p2202 ∨ (¬ p3684) ∨ p4753)
    : (¬ p3684) ∨ p4753 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3684 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4753) := (fun h => hn (Or.inr h));
    let u2 : p1994 := h2154;
    let u3 : (¬ p2202) := h40867;
    (Or.elim h14507 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43287 (p1994 p3008 p3584 p4753 : Prop)
    (h2154 : p1994)
    (h40891 : (¬ p3008))
    (h14509 : (¬ p1994) ∨ p3008 ∨ (¬ p3584) ∨ p4753)
    : (¬ p3584) ∨ p4753 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3584 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4753) := (fun h => hn (Or.inr h));
    let u2 : p1994 := h2154;
    let u3 : (¬ p3008) := h40891;
    (Or.elim h14509 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43288 (p1990 p2027 p2352 p2764 p3989 p4137 p4191 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14510 : (¬ p1990) ∨ p2027 ∨ (¬ p2352) ∨ p2764 ∨ (¬ p3989) ∨ (¬ p4137) ∨ (¬ p4191))
    : (¬ p2352) ∨ (¬ p3989) ∨ (¬ p4137) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h14510 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43289 (p1975 p2027 p2202 p2295 p2383 p2563 p3324 p3743 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h14511 : (¬ p1975) ∨ p2027 ∨ p2202 ∨ (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2563) ∨ (¬ p3324) ∨ (¬ p3743))
    : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2563) ∨ (¬ p3324) ∨ (¬ p3743) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h14511 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43291 (p1986 p2611 p2696 p4752 : Prop)
    (h2146 : p1986)
    (h40877 : (¬ p2611))
    (h14513 : (¬ p1986) ∨ p2611 ∨ (¬ p2696) ∨ p4752)
    : (¬ p2696) ∨ p4752 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4752) := (fun h => hn (Or.inr h));
    let u2 : p1986 := h2146;
    let u3 : (¬ p2611) := h40877;
    (Or.elim h14513 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43292 (p1975 p2027 p2295 p2611 p2696 p2819 p3324 p4426 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14514 : (¬ p1975) ∨ p2027 ∨ (¬ p2295) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2819) ∨ (¬ p3324) ∨ (¬ p4426))
    : (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2819) ∨ (¬ p3324) ∨ (¬ p4426) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h14514 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43293 (p1987 p2027 p2633 p3016 p3364 p3584 p3644 p3742 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14515 : (¬ p1987) ∨ p2027 ∨ p2633 ∨ (¬ p3016) ∨ (¬ p3364) ∨ (¬ p3584) ∨ (¬ p3644) ∨ (¬ p3742))
    : (¬ p3016) ∨ (¬ p3364) ∨ (¬ p3584) ∨ (¬ p3644) ∨ (¬ p3742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h14515 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43294 (p2020 p3128 p3979 p4601 : Prop)
    (h2180 : p2020)
    (h40894 : (¬ p3128))
    (h14516 : (¬ p2020) ∨ p3128 ∨ (¬ p3979) ∨ p4601)
    : (¬ p3979) ∨ p4601 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4601) := (fun h => hn (Or.inr h));
    let u2 : p2020 := h2180;
    let u3 : (¬ p3128) := h40894;
    (Or.elim h14516 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43295 (p1975 p2027 p2295 p3146 p3324 p3578 p4347 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h14517 : (¬ p1975) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p3146) ∨ (¬ p3324) ∨ p3578 ∨ (¬ p4347))
    : (¬ p2295) ∨ (¬ p3146) ∨ (¬ p3324) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3578) := h40900;
    (Or.elim h14517 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43296 (p1975 p2027 p2295 p2611 p2797 p3166 p3877 p4117 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14518 : (¬ p1975) ∨ p2027 ∨ (¬ p2295) ∨ p2611 ∨ (¬ p2797) ∨ (¬ p3166) ∨ (¬ p3877) ∨ (¬ p4117))
    : (¬ p2295) ∨ (¬ p2797) ∨ (¬ p3166) ∨ (¬ p3877) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h14518 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43299 (p1983 p2027 p2114 p2417 p2437 p2630 p2737 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h14556 : (¬ p1983) ∨ p2027 ∨ p2114 ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2737))
    : (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h14556 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43301 (p1985 p2027 p2241 p2449 p2699 p3027 p3690 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14559 : (¬ p1985) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2449) ∨ p2699 ∨ (¬ p3027) ∨ (¬ p3690))
    : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3690) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14559 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43302 (p1985 p2027 p2156 p2409 p2427 p3452 p4110 p4172 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h14560 : (¬ p1985) ∨ p2027 ∨ (¬ p2156) ∨ p2409 ∨ (¬ p2427) ∨ (¬ p3452) ∨ (¬ p4110) ∨ (¬ p4172))
    : (¬ p2156) ∨ (¬ p2427) ∨ (¬ p3452) ∨ (¬ p4110) ∨ (¬ p4172) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1985 := h2145;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2409) := h40874;
    (Or.elim h14560 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43303 (p1994 p2027 p2169 p2307 p2387 p2588 p3574 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14561 : (¬ p1994) ∨ p2027 ∨ p2169 ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p3574))
    : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p3574) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h14561 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43305 (p1992 p2027 p2299 p2396 p2633 p3588 p3821 p3959 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14563 : (¬ p1992) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2396) ∨ p2633 ∨ (¬ p3588) ∨ (¬ p3821) ∨ (¬ p3959))
    : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3588) ∨ (¬ p3821) ∨ (¬ p3959) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h14563 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43307 (p1975 p2027 p2307 p2352 p2387 p2409 p2493 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h14565 : (¬ p1975) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2387) ∨ p2409 ∨ (¬ p2493))
    : (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2409) := h40874;
    (Or.elim h14565 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43317 (p1992 p2027 p2387 p2459 p2633 p2785 p3688 p4347 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14575 : (¬ p1992) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2459) ∨ p2633 ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4347))
    : (¬ p2387) ∨ (¬ p2459) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h14575 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43323 (p1988 p2027 p2241 p2699 p2727 p3276 p3343 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14582 : (¬ p1988) ∨ p2027 ∨ (¬ p2241) ∨ p2699 ∨ (¬ p2727) ∨ (¬ p3276) ∨ (¬ p3343))
    : (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3276) ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14582 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43324 (p2002 p2027 p2307 p3043 p3680 p3773 p3822 p5378 : Prop)
    (h2162 : p2002)
    (h40810 : (¬ p2027))
    (h40893 : (¬ p3043))
    (h14583 : (¬ p2002) ∨ p2027 ∨ (¬ p2307) ∨ p3043 ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p3822) ∨ (¬ p5378))
    : (¬ p2307) ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p3822) ∨ (¬ p5378) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2002 := h2162;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3043) := h40893;
    (Or.elim h14583 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43326 (p2010 p2027 p2323 p2499 p2651 p2922 p3016 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14585 : (¬ p2010) ∨ p2027 ∨ p2323 ∨ (¬ p2499) ∨ (¬ p2651) ∨ (¬ p2922) ∨ (¬ p3016))
    : (¬ p2499) ∨ (¬ p2651) ∨ (¬ p2922) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2010 := h2170;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14585 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43329 (p1997 p2027 p2295 p2588 p2590 p2611 p2696 p2797 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14588 : (¬ p1997) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2588) ∨ (¬ p2590) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2797))
    : (¬ p2295) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p2696) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h14588 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43331 (p1992 p2027 p2459 p2633 p2743 p3172 p3361 p4118 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14590 : (¬ p1992) ∨ p2027 ∨ (¬ p2459) ∨ p2633 ∨ (¬ p2743) ∨ (¬ p3172) ∨ (¬ p3361) ∨ (¬ p4118))
    : (¬ p2459) ∨ (¬ p2743) ∨ (¬ p3172) ∨ (¬ p3361) ∨ (¬ p4118) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h14590 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43336 (p1980 p2027 p2202 p2553 p2573 p2589 p3568 : Prop)
    (h2140 : p1980)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h14597 : (¬ p1980) ∨ p2027 ∨ p2202 ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3568))
    : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1980 := h2140;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h14597 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43338 (p1988 p2027 p2406 p2699 p2982 p3379 p3680 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14600 : (¬ p1988) ∨ p2027 ∨ (¬ p2406) ∨ p2699 ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3680))
    : (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3680) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14600 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43341 (p2015 p2027 p2307 p2764 p3549 p3946 p4191 : Prop)
    (h2175 : p2015)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14603 : (¬ p2015) ∨ p2027 ∨ (¬ p2307) ∨ p2764 ∨ (¬ p3549) ∨ (¬ p3946) ∨ (¬ p4191))
    : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3946) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2015 := h2175;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h14603 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43343 (p1989 p2027 p2191 p2406 p2699 p2982 p3379 p4335 : Prop)
    (h2149 : p1989)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14605 : (¬ p1989) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p2406) ∨ p2699 ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p4335))
    : (¬ p2191) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p4335) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1989 := h2149;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14605 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43344 (p1987 p2027 p2104 p2169 p2363 p2696 p4340 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14606 : (¬ p1987) ∨ p2027 ∨ (¬ p2104) ∨ p2169 ∨ (¬ p2363) ∨ (¬ p2696) ∨ (¬ p4340))
    : (¬ p2104) ∨ (¬ p2363) ∨ (¬ p2696) ∨ (¬ p4340) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h14606 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43348 (p2005 p2027 p2409 p2588 p3093 p3309 p3452 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h14610 : (¬ p2005) ∨ p2027 ∨ p2409 ∨ (¬ p2588) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3452))
    : (¬ p2588) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2409) := h40874;
    (Or.elim h14610 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43351 (p2005 p2027 p2166 p2307 p2588 p2873 p2962 p4120 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40886 : (¬ p2873))
    (h14613 : (¬ p2005) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2307) ∨ (¬ p2588) ∨ p2873 ∨ (¬ p2962) ∨ (¬ p4120))
    : (¬ p2166) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p2962) ∨ (¬ p4120) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2005 := h2165;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2873) := h40886;
    (Or.elim h14613 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43352 (p1982 p2027 p2177 p2761 p3309 p3818 p3945 p4444 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40905 : (¬ p3818))
    (h14615 : (¬ p1982) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2761) ∨ (¬ p3309) ∨ p3818 ∨ (¬ p3945) ∨ (¬ p4444))
    : (¬ p2177) ∨ (¬ p2761) ∨ (¬ p3309) ∨ (¬ p3945) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3818) := h40905;
    (Or.elim h14615 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43354 (p1978 p2027 p2169 p2891 p3556 p3989 p4173 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14617 : (¬ p1978) ∨ p2027 ∨ p2169 ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3989) ∨ (¬ p4173))
    : (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3989) ∨ (¬ p4173) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1978 := h2138;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h14617 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43355 (p1984 p2027 p2766 p3486 p3555 p3570 p4348 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14618 : (¬ p1984) ∨ p2027 ∨ p2766 ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4348))
    : (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3486 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14618 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43356 (p2005 p2027 p2274 p2313 p2765 p3654 p4137 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14619 : (¬ p2005) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2313) ∨ p2765 ∨ (¬ p3654) ∨ (¬ p4137))
    : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4137) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h14619 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43358 (p1999 p2027 p2114 p2230 p2563 p3125 p3367 p3759 : Prop)
    (h2159 : p1999)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h14622 : (¬ p1999) ∨ p2027 ∨ p2114 ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3367) ∨ (¬ p3759))
    : (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3367) ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1999 := h2159;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h14622 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43362 (p2005 p2027 p2307 p2588 p3319 p3818 p3946 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40905 : (¬ p3818))
    (h14626 : (¬ p2005) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p3319) ∨ p3818 ∨ (¬ p3946))
    : (¬ p2307) ∨ (¬ p2588) ∨ (¬ p3319) ∨ (¬ p3946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3818) := h40905;
    (Or.elim h14626 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43372 (p1981 p2765 p3063 p4514 : Prop)
    (h2141 : p1981)
    (h40883 : (¬ p2765))
    (h14636 : (¬ p1981) ∨ p2765 ∨ (¬ p3063) ∨ p4514)
    : (¬ p3063) ∨ p4514 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4514) := (fun h => hn (Or.inr h));
    let u2 : p1981 := h2141;
    let u3 : (¬ p2765) := h40883;
    (Or.elim h14636 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43375 (p1990 p2027 p2169 p2363 p2563 p3692 p3880 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14639 : (¬ p1990) ∨ p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p2563) ∨ (¬ p3692) ∨ (¬ p3880))
    : (¬ p2363) ∨ (¬ p2563) ∨ (¬ p3692) ∨ (¬ p3880) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h14639 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43376 (p1990 p2027 p2241 p2542 p2563 p2699 p2727 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14640 : (¬ p1990) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2542) ∨ (¬ p2563) ∨ p2699 ∨ (¬ p2727))
    : (¬ p2241) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14640 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43378 (p1990 p2027 p2253 p2563 p2651 p2699 p2992 p4111 p4241 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14642 : (¬ p1990) ∨ p2027 ∨ (¬ p2253) ∨ (¬ p2563) ∨ (¬ p2651) ∨ p2699 ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241))
    : (¬ p2253) ∨ (¬ p2563) ∨ (¬ p2651) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1990 := h2150;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2699) := h40881;
    (Or.elim h14642 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43379 (p2001 p2027 p2323 p2528 p2651 p3083 p3692 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14643 : (¬ p2001) ∨ p2027 ∨ p2323 ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3692))
    : (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3692) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2001 := h2161;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14643 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43380 (p2010 p2027 p2191 p2253 p2699 p2946 p3027 p3156 p3368 p3579 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14645 : (¬ p2010) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p2253) ∨ p2699 ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3156) ∨ (¬ p3368) ∨ (¬ p3579))
    : (¬ p2191) ∨ (¬ p2253) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3156) ∨ (¬ p3368) ∨ (¬ p3579) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2010 := h2170;
    let u8 : (¬ p2027) := h40810;
    let u9 : (¬ p2699) := h40881;
    (Or.elim h14645 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u9 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step43381 (p2015 p2027 p2169 p3426 p3434 p3549 p4107 p4358 : Prop)
    (h2175 : p2015)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14646 : (¬ p2015) ∨ p2027 ∨ p2169 ∨ (¬ p3426) ∨ (¬ p3434) ∨ (¬ p3549) ∨ (¬ p4107) ∨ (¬ p4358))
    : (¬ p3426) ∨ (¬ p3434) ∨ (¬ p3549) ∨ (¬ p4107) ∨ (¬ p4358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3426 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2015 := h2175;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h14646 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43383 (p1991 p2027 p2169 p2685 p3324 p3414 p4195 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14648 : (¬ p1991) ∨ p2027 ∨ p2169 ∨ (¬ p2685) ∨ (¬ p3324) ∨ (¬ p3414) ∨ (¬ p4195))
    : (¬ p2685) ∨ (¬ p3324) ∨ (¬ p3414) ∨ (¬ p4195) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h14648 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43386 (p1992 p2027 p2098 p2633 p3425 p3659 p4242 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14651 : (¬ p1992) ∨ p2027 ∨ (¬ p2098) ∨ p2633 ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4242))
    : (¬ p2098) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4242) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h14651 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43395 (p1987 p2027 p2132 p2737 p2842 p3055 p3583 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h14661 : (¬ p1987) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2737) ∨ p2842 ∨ (¬ p3055) ∨ (¬ p3583))
    : (¬ p2132) ∨ (¬ p2737) ∨ (¬ p3055) ∨ (¬ p3583) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2842) := h40885;
    (Or.elim h14661 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43396 (p1992 p2027 p2743 p2764 p2952 p3361 p4208 p4322 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14662 : (¬ p1992) ∨ p2027 ∨ (¬ p2743) ∨ p2764 ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p4208) ∨ (¬ p4322))
    : (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p4208) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h14662 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43398 (p1977 p2027 p2764 p2946 p3292 p3662 p4040 p4322 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14664 : (¬ p1977) ∨ p2027 ∨ p2764 ∨ (¬ p2946) ∨ (¬ p3292) ∨ (¬ p3662) ∨ (¬ p4040) ∨ (¬ p4322))
    : (¬ p2946) ∨ (¬ p3292) ∨ (¬ p3662) ∨ (¬ p4040) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h14664 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43404 (p1976 p2027 p2138 p2177 p2997 p3570 p4244 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14670 : (¬ p1976) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2177) ∨ p2997 ∨ (¬ p3570) ∨ (¬ p4244))
    : (¬ p2138) ∨ (¬ p2177) ∨ (¬ p3570) ∨ (¬ p4244) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h14670 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43407 (p1985 p2027 p2233 p2427 p2573 p2850 p3584 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h14673 : (¬ p1985) ∨ p2027 ∨ p2233 ∨ (¬ p2427) ∨ (¬ p2573) ∨ (¬ p2850) ∨ (¬ p3584))
    : (¬ p2427) ∨ (¬ p2573) ∨ (¬ p2850) ∨ (¬ p3584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2233) := h40868;
    (Or.elim h14673 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43408 (p2001 p2027 p2528 p2545 p2810 p3005 p3692 p4346 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h14674 : (¬ p2001) ∨ p2027 ∨ (¬ p2528) ∨ p2545 ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3692) ∨ (¬ p4346))
    : (¬ p2528) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3692) ∨ (¬ p4346) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2001 := h2161;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h14674 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43409 (p1977 p2027 p2331 p2764 p2811 p4035 p4154 p4190 p4191 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14675 : (¬ p1977) ∨ p2027 ∨ (¬ p2331) ∨ p2764 ∨ (¬ p2811) ∨ (¬ p4035) ∨ (¬ p4154) ∨ (¬ p4190) ∨ (¬ p4191))
    : (¬ p2331) ∨ (¬ p2811) ∨ (¬ p4035) ∨ (¬ p4154) ∨ (¬ p4190) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1977 := h2137;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2764) := h40882;
    (Or.elim h14675 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43411 (p1988 p2027 p2210 p2699 p2761 p2891 p3246 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14677 : (¬ p1988) ∨ p2027 ∨ (¬ p2210) ∨ p2699 ∨ (¬ p2761) ∨ (¬ p2891) ∨ (¬ p3246))
    : (¬ p2210) ∨ (¬ p2761) ∨ (¬ p2891) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14677 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43412 (p1976 p2027 p2764 p3365 p4037 p4191 p4195 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14678 : (¬ p1976) ∨ p2027 ∨ p2764 ∨ (¬ p3365) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4195))
    : (¬ p3365) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4195) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h14678 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43413 (p1977 p2027 p2331 p2462 p3414 p3947 p4154 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h14679 : (¬ p1977) ∨ p2027 ∨ (¬ p2331) ∨ p2462 ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4154))
    : (¬ p2331) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h14679 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43415 (p2005 p2027 p2230 p2493 p3238 p3441 p3860 p4079 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40897 : (¬ p3441))
    (h14681 : (¬ p2005) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2493) ∨ (¬ p3238) ∨ p3441 ∨ (¬ p3860) ∨ (¬ p4079))
    : (¬ p2230) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3860) ∨ (¬ p4079) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2005 := h2165;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3441) := h40897;
    (Or.elim h14681 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43416 (p1992 p2027 p2743 p2764 p2963 p3361 p4037 p4191 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14682 : (¬ p1992) ∨ p2027 ∨ (¬ p2743) ∨ p2764 ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p4037) ∨ (¬ p4191))
    : (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p4037) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h14682 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43417 (p2005 p2027 p2230 p2493 p2914 p3238 p3540 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h14683 : (¬ p2005) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2493) ∨ p2914 ∨ (¬ p3238) ∨ (¬ p3540))
    : (¬ p2230) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3540) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h14683 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43418 (p1998 p2027 p2470 p2528 p2656 p2914 p3742 p4348 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h14684 : (¬ p1998) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2656) ∨ p2914 ∨ (¬ p3742) ∨ (¬ p4348))
    : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2656) ∨ (¬ p3742) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2914) := h40887;
    (Or.elim h14684 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43419 (p1988 p2027 p2761 p3399 p3591 p3631 p3818 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40905 : (¬ p3818))
    (h14685 : (¬ p1988) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3591) ∨ (¬ p3631) ∨ p3818)
    : (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3591) ∨ (¬ p3631) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3818) := h40905;
    (Or.elim h14685 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step43421 (p1981 p2027 p2088 p2274 p2313 p2765 p4114 p4347 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14687 : (¬ p1981) ∨ p2027 ∨ (¬ p2088) ∨ (¬ p2274) ∨ (¬ p2313) ∨ p2765 ∨ (¬ p4114) ∨ (¬ p4347))
    : (¬ p2088) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p4114) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1981 := h2141;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h14687 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43423 (p1998 p2027 p2264 p2274 p2313 p2765 p3204 p3319 p3947 p4623 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14689 : (¬ p1998) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p2274) ∨ (¬ p2313) ∨ p2765 ∨ (¬ p3204) ∨ (¬ p3319) ∨ (¬ p3947) ∨ (¬ p4623))
    : (¬ p2264) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3204) ∨ (¬ p3319) ∨ (¬ p3947) ∨ (¬ p4623) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p1998 := h2158;
    let u8 : (¬ p2027) := h40810;
    let u9 : (¬ p2765) := h40883;
    (Or.elim h14689 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u9 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step43424 (p1988 p2027 p2192 p2210 p2699 p3125 p3461 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14690 : (¬ p1988) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p2210) ∨ p2699 ∨ (¬ p3125) ∨ (¬ p3461))
    : (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3125) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14690 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43425 (p1975 p2027 p2230 p2233 p2299 p2934 p3238 p3527 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h14691 : (¬ p1975) ∨ p2027 ∨ (¬ p2230) ∨ p2233 ∨ (¬ p2299) ∨ (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3527))
    : (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2934 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2233) := h40868;
    (Or.elim h14691 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43427 (p1975 p2027 p2241 p2264 p2299 p2641 p2699 p4156 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14693 : (¬ p1975) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2641) ∨ p2699 ∨ (¬ p4156))
    : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2641) ∨ (¬ p4156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14693 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43431 (p1975 p2027 p2274 p2699 p3093 p4053 p4393 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14697 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ p2699 ∨ (¬ p3093) ∨ (¬ p4053) ∨ (¬ p4393))
    : (¬ p2274) ∨ (¬ p3093) ∨ (¬ p4053) ∨ (¬ p4393) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14697 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43432 (p1988 p2027 p2230 p2233 p2563 p3125 p3461 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h14715 : (¬ p1988) ∨ p2027 ∨ (¬ p2230) ∨ p2233 ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3461))
    : (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2233) := h40868;
    (Or.elim h14715 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43437 (p1998 p2027 p2210 p2699 p2881 p3631 p3690 p4431 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14737 : (¬ p1998) ∨ p2027 ∨ (¬ p2210) ∨ p2699 ∨ (¬ p2881) ∨ (¬ p3631) ∨ (¬ p3690) ∨ (¬ p4431))
    : (¬ p2210) ∨ (¬ p2881) ∨ (¬ p3631) ∨ (¬ p3690) ∨ (¬ p4431) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14737 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43439 (p2017 p2027 p2608 p2685 p2699 p2737 p3931 : Prop)
    (h2177 : p2017)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14739 : (¬ p2017) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2685) ∨ p2699 ∨ (¬ p2737) ∨ (¬ p3931))
    : (¬ p2608) ∨ (¬ p2685) ∨ (¬ p2737) ∨ (¬ p3931) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2017 := h2177;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14739 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43441 (p2006 p2027 p2109 p2169 p2363 p2839 p3857 p4242 : Prop)
    (h2166 : p2006)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14741 : (¬ p2006) ∨ p2027 ∨ (¬ p2109) ∨ p2169 ∨ (¬ p2363) ∨ (¬ p2839) ∨ (¬ p3857) ∨ (¬ p4242))
    : (¬ p2109) ∨ (¬ p2363) ∨ (¬ p2839) ∨ (¬ p3857) ∨ (¬ p4242) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2109 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2006 := h2166;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h14741 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43444 (p1994 p2027 p2630 p2699 p3399 p3631 p4324 p4357 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14744 : (¬ p1994) ∨ p2027 ∨ (¬ p2630) ∨ p2699 ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p4324) ∨ (¬ p4357))
    : (¬ p2630) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p4324) ∨ (¬ p4357) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14744 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43445 (p1995 p2027 p2499 p2668 p2997 p3568 p3956 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14745 : (¬ p1995) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p2668) ∨ p2997 ∨ (¬ p3568) ∨ (¬ p3956))
    : (¬ p2499) ∨ (¬ p2668) ∨ (¬ p3568) ∨ (¬ p3956) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h14745 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43446 (p1987 p2027 p2169 p2737 p3979 p4242 p5612 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14746 : (¬ p1987) ∨ p2027 ∨ p2169 ∨ (¬ p2737) ∨ (¬ p3979) ∨ (¬ p4242) ∨ (¬ p5612))
    : (¬ p2737) ∨ (¬ p3979) ∨ (¬ p4242) ∨ (¬ p5612) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5612 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h14746 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43448 (p1993 p2027 p2952 p2997 p3097 p3166 p3952 : Prop)
    (h2153 : p1993)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14748 : (¬ p1993) ∨ p2027 ∨ (¬ p2952) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3166) ∨ (¬ p3952))
    : (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3166) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1993 := h2153;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h14748 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43450 (p1985 p2027 p2608 p2699 p2707 p2717 p3570 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14767 : (¬ p1985) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3570))
    : (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14767 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43451 (p1990 p2027 p2696 p2699 p2743 p2839 p2860 p3589 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14768 : (¬ p1990) ∨ p2027 ∨ (¬ p2696) ∨ p2699 ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p3589))
    : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14768 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43452 (p1981 p2027 p2352 p2608 p2699 p3367 p3422 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14769 : (¬ p1981) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p3367) ∨ (¬ p3422))
    : (¬ p2352) ∨ (¬ p2608) ∨ (¬ p3367) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14769 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43453 (p1981 p2027 p2187 p2608 p2699 p2839 p2860 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14770 : (¬ p1981) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2839) ∨ (¬ p2860))
    : (¬ p2187) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14770 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43454 (p1992 p2027 p2696 p2743 p2780 p2997 p3822 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14771 : (¬ p1992) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2780) ∨ p2997 ∨ (¬ p3822))
    : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2780) ∨ (¬ p3822) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h14771 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43455 (p1995 p2027 p2499 p2573 p2764 p3346 p4022 p4191 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14772 : (¬ p1995) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p2573) ∨ p2764 ∨ (¬ p3346) ∨ (¬ p4022) ∨ (¬ p4191))
    : (¬ p2499) ∨ (¬ p2573) ∨ (¬ p3346) ∨ (¬ p4022) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h14772 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43456 (p1981 p2027 p2187 p2241 p2284 p2699 p2992 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14773 : (¬ p1981) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2241) ∨ (¬ p2284) ∨ p2699 ∨ (¬ p2992))
    : (¬ p2187) ∨ (¬ p2241) ∨ (¬ p2284) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14773 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43457 (p1998 p2027 p2241 p2699 p3027 p3256 p4044 p4348 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14774 : (¬ p1998) ∨ p2027 ∨ (¬ p2241) ∨ p2699 ∨ (¬ p3027) ∨ (¬ p3256) ∨ (¬ p4044) ∨ (¬ p4348))
    : (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3256) ∨ (¬ p4044) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14774 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43459 (p1976 p2027 p2169 p2363 p3365 p4118 p4195 p4196 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14776 : (¬ p1976) ∨ p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p3365) ∨ (¬ p4118) ∨ (¬ p4195) ∨ (¬ p4196))
    : (¬ p2363) ∨ (¬ p3365) ∨ (¬ p4118) ∨ (¬ p4195) ∨ (¬ p4196) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h14776 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43460 (p1976 p2027 p2766 p3324 p3365 p4195 p4347 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14777 : (¬ p1976) ∨ p2027 ∨ p2766 ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p4347))
    : (¬ p3324) ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3324 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14777 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43461 (p1998 p2027 p2363 p2668 p2997 p3568 p4348 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14778 : (¬ p1998) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2668) ∨ p2997 ∨ (¬ p3568) ∨ (¬ p4348))
    : (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3568) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h14778 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43464 (p2009 p2027 p2545 p2810 p3005 p3256 p3857 : Prop)
    (h2169 : p2009)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h14782 : (¬ p2009) ∨ p2027 ∨ p2545 ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3857))
    : (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3857) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2009 := h2169;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h14782 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43468 (p2001 p2027 p2363 p2819 p2997 p3692 p3822 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14786 : (¬ p2001) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2819) ∨ p2997 ∨ (¬ p3692) ∨ (¬ p3822))
    : (¬ p2363) ∨ (¬ p2819) ∨ (¬ p3692) ∨ (¬ p3822) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2001 := h2161;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h14786 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43469 (p2015 p2027 p2774 p2819 p2842 p3055 p3923 : Prop)
    (h2175 : p2015)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h14787 : (¬ p2015) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p2819) ∨ p2842 ∨ (¬ p3055) ∨ (¬ p3923))
    : (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3055) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2015 := h2175;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2842) := h40885;
    (Or.elim h14787 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43470 (p1992 p2027 p2138 p2383 p2786 p3474 p3688 p4358 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h14788 : (¬ p1992) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2383) ∨ (¬ p2786) ∨ p3474 ∨ (¬ p3688) ∨ (¬ p4358))
    : (¬ p2138) ∨ (¬ p2383) ∨ (¬ p2786) ∨ (¬ p3688) ∨ (¬ p4358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3474) := h40898;
    (Or.elim h14788 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43471 (p1992 p2027 p2743 p2997 p3323 p3361 p3568 p3946 p3983 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14789 : (¬ p1992) ∨ p2027 ∨ (¬ p2743) ∨ p2997 ∨ (¬ p3323) ∨ (¬ p3361) ∨ (¬ p3568) ∨ (¬ p3946) ∨ (¬ p3983))
    : (¬ p2743) ∨ (¬ p3323) ∨ (¬ p3361) ∨ (¬ p3568) ∨ (¬ p3946) ∨ (¬ p3983) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1992 := h2152;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2997) := h40890;
    (Or.elim h14789 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43473 (p1992 p2027 p2169 p2363 p2743 p2963 p3361 p4118 p4196 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14791 : (¬ p1992) ∨ p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p4118) ∨ (¬ p4196))
    : (¬ p2363) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p4118) ∨ (¬ p4196) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1992 := h2152;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2169) := h40866;
    (Or.elim h14791 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43475 (p1977 p2027 p2545 p2668 p2797 p2810 p3923 p4245 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h14793 : (¬ p1977) ∨ p2027 ∨ p2545 ∨ (¬ p2668) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3923) ∨ (¬ p4245))
    : (¬ p2668) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3923) ∨ (¬ p4245) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h14793 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43476 (p1994 p2027 p2493 p2509 p2766 p3574 p4347 p4432 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14794 : (¬ p1994) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p2509) ∨ p2766 ∨ (¬ p3574) ∨ (¬ p4347) ∨ (¬ p4432))
    : (¬ p2493) ∨ (¬ p2509) ∨ (¬ p3574) ∨ (¬ p4347) ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h14794 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43478 (p1977 p2027 p2331 p2766 p3172 p4118 p4154 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14796 : (¬ p1977) ∨ p2027 ∨ (¬ p2331) ∨ p2766 ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4154))
    : (¬ p2331) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14796 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43483 (p1994 p2027 p2573 p2727 p2914 p3540 p4154 p4389 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h14801 : (¬ p1994) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2727) ∨ p2914 ∨ (¬ p3540) ∨ (¬ p4154) ∨ (¬ p4389))
    : (¬ p2573) ∨ (¬ p2727) ∨ (¬ p3540) ∨ (¬ p4154) ∨ (¬ p4389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2914) := h40887;
    (Or.elim h14801 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43484 (p1998 p2027 p2264 p2611 p2696 p2707 p2743 p4325 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14802 : (¬ p1998) ∨ p2027 ∨ (¬ p2264) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p4325))
    : (¬ p2264) ∨ (¬ p2696) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p4325) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h14802 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43485 (p1995 p2027 p2230 p2437 p3008 p3238 p3540 p3574 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h14803 : (¬ p1995) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2437) ∨ p3008 ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p3574))
    : (¬ p2230) ∨ (¬ p2437) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p3574) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3008) := h40891;
    (Or.elim h14803 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43486 (p1986 p2027 p2230 p2462 p3540 p3684 p3690 p4001 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h14804 : (¬ p1986) ∨ p2027 ∨ (¬ p2230) ∨ p2462 ∨ (¬ p3540) ∨ (¬ p3684) ∨ (¬ p3690) ∨ (¬ p4001))
    : (¬ p2230) ∨ (¬ p3540) ∨ (¬ p3684) ∨ (¬ p3690) ∨ (¬ p4001) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1986 := h2146;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2462) := h40875;
    (Or.elim h14804 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43487 (p1987 p2027 p2287 p2307 p2737 p3567 p3688 p3822 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h14805 : (¬ p1987) ∨ p2027 ∨ p2287 ∨ (¬ p2307) ∨ (¬ p2737) ∨ (¬ p3567) ∨ (¬ p3688) ∨ (¬ p3822))
    : (¬ p2307) ∨ (¬ p2737) ∨ (¬ p3567) ∨ (¬ p3688) ∨ (¬ p3822) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2287) := h40869;
    (Or.elim h14805 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43488 (p1981 p2027 p2122 p2611 p2774 p3063 p3549 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14806 : (¬ p1981) ∨ p2027 ∨ (¬ p2122) ∨ p2611 ∨ (¬ p2774) ∨ (¬ p3063) ∨ (¬ p3549))
    : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p3063) ∨ (¬ p3549) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14806 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43492 (p1991 p2027 p2299 p2766 p2963 p3568 p4348 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14810 : (¬ p1991) ∨ p2027 ∨ (¬ p2299) ∨ p2766 ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4348))
    : (¬ p2299) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14810 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43495 (p1997 p2027 p2611 p2696 p2743 p2850 p3367 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14813 : (¬ p1997) ∨ p2027 ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2850) ∨ (¬ p3367))
    : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2850) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14813 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43496 (p1998 p2027 p2699 p2707 p2717 p2774 p3589 p3688 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14814 : (¬ p1998) ∨ p2027 ∨ p2699 ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2774) ∨ (¬ p3589) ∨ (¬ p3688))
    : (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2774) ∨ (¬ p3589) ∨ (¬ p3688) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14814 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43497 (p1998 p2027 p2177 p2295 p2611 p2696 p2797 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14815 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2295) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2797))
    : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14815 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43498 (p1986 p2027 p2417 p2914 p3367 p3588 p4324 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h14816 : (¬ p1986) ∨ p2027 ∨ (¬ p2417) ∨ p2914 ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p4324))
    : (¬ p2417) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p4324) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1986 := h2146;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h14816 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43499 (p2001 p2027 p2611 p2619 p2774 p2839 p3688 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14817 : (¬ p2001) ∨ p2027 ∨ p2611 ∨ (¬ p2619) ∨ (¬ p2774) ∨ (¬ p2839) ∨ (¬ p3688))
    : (¬ p2619) ∨ (¬ p2774) ∨ (¬ p2839) ∨ (¬ p3688) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2001 := h2161;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14817 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43501 (p1998 p2027 p2177 p2611 p3434 p3471 p4107 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14819 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ p2611 ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p4107))
    : (¬ p2177) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14819 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43502 (p1986 p2027 p2109 p3146 p3367 p3578 p3857 p4242 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h14820 : (¬ p1986) ∨ p2027 ∨ (¬ p2109) ∨ (¬ p3146) ∨ (¬ p3367) ∨ p3578 ∨ (¬ p3857) ∨ (¬ p4242))
    : (¬ p2109) ∨ (¬ p3146) ∨ (¬ p3367) ∨ (¬ p3857) ∨ (¬ p4242) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2109 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1986 := h2146;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3578) := h40900;
    (Or.elim h14820 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43503 (p1995 p2027 p2608 p2699 p2850 p3238 p3367 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14821 : (¬ p1995) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p3367))
    : (¬ p2608) ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14821 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43505 (p1985 p2027 p2873 p3399 p3527 p3555 p3570 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40886 : (¬ p2873))
    (h14823 : (¬ p1985) ∨ p2027 ∨ p2873 ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3555) ∨ (¬ p3570))
    : (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3555) ∨ (¬ p3570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2873) := h40886;
    (Or.elim h14823 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43506 (p1994 p2027 p2651 p2938 p3246 p3414 p3947 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h14824 : (¬ p1994) ∨ p2027 ∨ (¬ p2651) ∨ p2938 ∨ (¬ p3246) ∨ (¬ p3414) ∨ (¬ p3947))
    : (¬ p2651) ∨ (¬ p3246) ∨ (¬ p3414) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h14824 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43507 (p1982 p2027 p2699 p3093 p3319 p3461 p4444 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14825 : (¬ p1982) ∨ p2027 ∨ p2699 ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p4444))
    : (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14825 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43509 (p1983 p2027 p2148 p2299 p2396 p2881 p3051 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h14827 : (¬ p1983) ∨ p2027 ∨ p2148 ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2881) ∨ (¬ p3051))
    : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2881) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2148) := h40865;
    (Or.elim h14827 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43510 (p1992 p2027 p2462 p2608 p2928 p3452 p4278 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h14828 : (¬ p1992) ∨ p2027 ∨ p2462 ∨ (¬ p2608) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278))
    : (¬ p2608) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h14828 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43512 (p1995 p2027 p2299 p2396 p2633 p2928 p4278 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14830 : (¬ p1995) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2396) ∨ p2633 ∨ (¬ p2928) ∨ (¬ p4278))
    : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2928) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h14830 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43513 (p1975 p2027 p2284 p2299 p2323 p2881 p2946 p3872 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14831 : (¬ p1975) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2299) ∨ p2323 ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p3872))
    : (¬ p2284) ∨ (¬ p2299) ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h14831 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43515 (p1982 p2027 p2187 p2284 p2323 p2363 p2946 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14833 : (¬ p1982) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2284) ∨ p2323 ∨ (¬ p2363) ∨ (¬ p2946))
    : (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2363) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14833 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43516 (p1984 p2027 p2534 p2766 p3585 p3874 p3954 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14834 : (¬ p1984) ∨ p2027 ∨ (¬ p2534) ∨ p2766 ∨ (¬ p3585) ∨ (¬ p3874) ∨ (¬ p3954))
    : (¬ p2534) ∨ (¬ p3585) ∨ (¬ p3874) ∨ (¬ p3954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14834 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43517 (p1984 p2027 p2509 p2914 p3452 p3641 p3876 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h14835 : (¬ p1984) ∨ p2027 ∨ (¬ p2509) ∨ p2914 ∨ (¬ p3452) ∨ (¬ p3641) ∨ (¬ p3876))
    : (¬ p2509) ∨ (¬ p3452) ∨ (¬ p3641) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h14835 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43518 (p1984 p2027 p2462 p3585 p3876 p3954 p4278 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h14836 : (¬ p1984) ∨ p2027 ∨ p2462 ∨ (¬ p3585) ∨ (¬ p3876) ∨ (¬ p3954) ∨ (¬ p4278))
    : (¬ p3585) ∨ (¬ p3876) ∨ (¬ p3954) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3585 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h14836 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43519 (p1982 p2027 p2187 p2331 p2363 p2388 p2952 p3986 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h14837 : (¬ p1982) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2331) ∨ (¬ p2363) ∨ p2388 ∨ (¬ p2952) ∨ (¬ p3986))
    : (¬ p2187) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2388) := h40873;
    (Or.elim h14837 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43520 (p1982 p2027 p2323 p2437 p2459 p2651 p2911 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14838 : (¬ p1982) ∨ p2027 ∨ p2323 ∨ (¬ p2437) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p2911))
    : (¬ p2437) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14838 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43522 (p1998 p2027 p2437 p2622 p2911 p3422 p3475 p3574 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h14840 : (¬ p1998) ∨ p2027 ∨ (¬ p2437) ∨ p2622 ∨ (¬ p2911) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p3574))
    : (¬ p2437) ∨ (¬ p2911) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p3574) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2622) := h40878;
    (Or.elim h14840 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43525 (p1975 p2027 p2148 p2299 p2962 p3527 p3654 p4026 p4452 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h14843 : (¬ p1975) ∨ p2027 ∨ p2148 ∨ (¬ p2299) ∨ (¬ p2962) ∨ (¬ p3527) ∨ (¬ p3654) ∨ (¬ p4026) ∨ (¬ p4452))
    : (¬ p2299) ∨ (¬ p2962) ∨ (¬ p3527) ∨ (¬ p3654) ∨ (¬ p4026) ∨ (¬ p4452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1975 := h2135;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2148) := h40865;
    (Or.elim h14843 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43526 (p1987 p2027 p2766 p2946 p3172 p4118 p4315 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14844 : (¬ p1987) ∨ p2027 ∨ p2766 ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4315))
    : (¬ p2946) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14844 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43528 (p1987 p2027 p2589 p2737 p2765 p3363 p3585 p4110 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14846 : (¬ p1987) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2737) ∨ p2765 ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4110))
    : (¬ p2589) ∨ (¬ p2737) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h14846 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43529 (p1992 p2027 p2287 p2598 p3365 p3585 p4195 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h14847 : (¬ p1992) ∨ p2027 ∨ p2287 ∨ (¬ p2598) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p4195))
    : (¬ p2598) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p4195) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2287) := h40869;
    (Or.elim h14847 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43531 (p1991 p2027 p2685 p2765 p3414 p3952 p4315 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14849 : (¬ p1991) ∨ p2027 ∨ (¬ p2685) ∨ p2765 ∨ (¬ p3414) ∨ (¬ p3952) ∨ (¬ p4315))
    : (¬ p2685) ∨ (¬ p3414) ∨ (¬ p3952) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h14849 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43532 (p1996 p2027 p2287 p2651 p2685 p2810 p2963 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h14850 : (¬ p1996) ∨ p2027 ∨ p2287 ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p2963))
    : (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p2963) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1996 := h2156;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2287) := h40869;
    (Or.elim h14850 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43533 (p1979 p2027 p2114 p2319 p2641 p2749 p3136 p3516 p3567 p4324 p4357 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h14851 : (¬ p1979) ∨ p2027 ∨ p2114 ∨ (¬ p2319) ∨ (¬ p2641) ∨ (¬ p2749) ∨ (¬ p3136) ∨ (¬ p3516) ∨ (¬ p3567) ∨ (¬ p4324) ∨ (¬ p4357))
    : (¬ p2319) ∨ (¬ p2641) ∨ (¬ p2749) ∨ (¬ p3136) ∨ (¬ p3516) ∨ (¬ p3567) ∨ (¬ p4324) ∨ (¬ p4357) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p1979 := h2139;
    let u9 : (¬ p2027) := h40810;
    let u10 : (¬ p2114) := h40864;
    (Or.elim h14851 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u10 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step43534 (p1984 p2027 p2766 p3238 p3452 p3692 p3880 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14853 : (¬ p1984) ∨ p2027 ∨ p2766 ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3692) ∨ (¬ p3880))
    : (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3692) ∨ (¬ p3880) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3238 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14853 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43535 (p2027 p2373 p2946 p3172 p3906 p4288 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h14854 : p2027 ∨ (¬ p2373) ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p3906) ∨ (¬ p4288) ∨ (¬ p4702))
    : (¬ p2373) ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p3906) ∨ (¬ p4288) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h14854 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step43536 (p1988 p2027 p2264 p2459 p2622 p2685 p3266 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h14855 : (¬ p1988) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p2459) ∨ p2622 ∨ (¬ p2685) ∨ (¬ p3266))
    : (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2685) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2622) := h40878;
    (Or.elim h14855 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43539 (p1984 p2027 p2462 p3238 p3452 p3690 p4235 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h14858 : (¬ p1984) ∨ p2027 ∨ p2462 ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3690) ∨ (¬ p4235))
    : (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3690) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3238 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h14858 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43540 (p1994 p2622 p2651 p4787 : Prop)
    (h2154 : p1994)
    (h40878 : (¬ p2622))
    (h14859 : (¬ p1994) ∨ p2622 ∨ (¬ p2651) ∨ p4787)
    : (¬ p2651) ∨ p4787 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4787) := (fun h => hn (Or.inr h));
    let u2 : p1994 := h2154;
    let u3 : (¬ p2622) := h40878;
    (Or.elim h14859 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43541 (p1984 p2027 p2765 p3585 p3684 p3954 p4110 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14860 : (¬ p1984) ∨ p2027 ∨ p2765 ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p3954) ∨ (¬ p4110))
    : (¬ p3585) ∨ (¬ p3684) ∨ (¬ p3954) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3585 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h14860 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43542 (p1984 p2027 p2202 p2440 p2509 p3083 p3452 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h14862 : (¬ p1984) ∨ p2027 ∨ p2202 ∨ (¬ p2440) ∨ (¬ p2509) ∨ (¬ p3083) ∨ (¬ p3452))
    : (¬ p2440) ∨ (¬ p2509) ∨ (¬ p3083) ∨ (¬ p3452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h14862 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43543 (p1984 p2027 p2406 p2589 p2764 p3193 p4108 p4425 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14863 : (¬ p1984) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2589) ∨ p2764 ∨ (¬ p3193) ∨ (¬ p4108) ∨ (¬ p4425))
    : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p3193) ∨ (¬ p4108) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h14863 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43544 (p1976 p2027 p2406 p2509 p3055 p3498 p3684 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40899 : (¬ p3498))
    (h14864 : (¬ p1976) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p3055) ∨ p3498 ∨ (¬ p3684))
    : (¬ p2406) ∨ (¬ p2509) ∨ (¬ p3055) ∨ (¬ p3684) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3498) := h40899;
    (Or.elim h14864 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43546 (p1984 p2027 p2406 p2462 p2589 p2928 p4108 p4278 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h14867 : (¬ p1984) ∨ p2027 ∨ (¬ p2406) ∨ p2462 ∨ (¬ p2589) ∨ (¬ p2928) ∨ (¬ p4108) ∨ (¬ p4278))
    : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2928) ∨ (¬ p4108) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2462) := h40875;
    (Or.elim h14867 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43556 (p1982 p2027 p2169 p3096 p3461 p3564 p3989 p4444 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14878 : (¬ p1982) ∨ p2027 ∨ p2169 ∨ (¬ p3096) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3989) ∨ (¬ p4444))
    : (¬ p3096) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3989) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3096 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h14878 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43557 (p1976 p3055 p3586 p5221 : Prop)
    (h2136 : p1976)
    (h40901 : (¬ p3586))
    (h14879 : (¬ p1976) ∨ (¬ p3055) ∨ p3586 ∨ p5221)
    : (¬ p3055) ∨ p5221 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5221) := (fun h => hn (Or.inr h));
    let u2 : p1976 := h2136;
    let u3 : (¬ p3586) := h40901;
    (Or.elim h14879 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43559 (p1998 p2027 p2323 p2437 p2528 p2651 p3875 p4348 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14881 : (¬ p1998) ∨ p2027 ∨ p2323 ∨ (¬ p2437) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3875) ∨ (¬ p4348))
    : (¬ p2437) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3875) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h14881 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43562 (p1977 p2355 p4111 p4650 : Prop)
    (h2137 : p1977)
    (h40872 : (¬ p2355))
    (h14884 : (¬ p1977) ∨ p2355 ∨ (¬ p4111) ∨ p4650)
    : (¬ p4111) ∨ p4650 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4111 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4650) := (fun h => hn (Or.inr h));
    let u2 : p1977 := h2137;
    let u3 : (¬ p2355) := h40872;
    (Or.elim h14884 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43564 (p1988 p2027 p2132 p2611 p2761 p2870 p3246 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14886 : (¬ p1988) ∨ p2027 ∨ (¬ p2132) ∨ p2611 ∨ (¬ p2761) ∨ (¬ p2870) ∨ (¬ p3246))
    : (¬ p2132) ∨ (¬ p2761) ∨ (¬ p2870) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14886 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43568 (p1991 p2027 p2202 p2440 p3027 p3414 p4111 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h14890 : (¬ p1991) ∨ p2027 ∨ p2202 ∨ (¬ p2440) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111))
    : (¬ p2440) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h14890 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43570 (p1999 p2027 p2699 p3063 p3093 p3483 p4358 : Prop)
    (h2159 : p1999)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14892 : (¬ p1999) ∨ p2027 ∨ p2699 ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3483) ∨ (¬ p4358))
    : (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3483) ∨ (¬ p4358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1999 := h2159;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14892 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43572 (p2010 p2027 p2396 p2699 p3093 p3309 p4278 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14894 : (¬ p2010) ∨ p2027 ∨ (¬ p2396) ∨ p2699 ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p4278))
    : (¬ p2396) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2010 := h2170;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14894 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43573 (p1994 p2027 p2169 p2427 p3989 p4110 p4320 p4700 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14896 : (¬ p1994) ∨ p2027 ∨ p2169 ∨ (¬ p2427) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4320) ∨ (¬ p4700))
    : (¬ p2427) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4320) ∨ (¬ p4700) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2169) := h40866;
    (Or.elim h14896 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43574 (p1979 p2210 p2699 p4960 : Prop)
    (h2139 : p1979)
    (h40881 : (¬ p2699))
    (h14897 : (¬ p1979) ∨ (¬ p2210) ∨ p2699 ∨ p4960)
    : (¬ p2210) ∨ p4960 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4960) := (fun h => hn (Or.inr h));
    let u2 : p1979 := h2139;
    let u3 : (¬ p2699) := h40881;
    (Or.elim h14897 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43575 (p1975 p2027 p2169 p2274 p2387 p3654 p3744 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14898 : (¬ p1975) ∨ p2027 ∨ p2169 ∨ (¬ p2274) ∨ (¬ p2387) ∨ (¬ p3654) ∨ (¬ p3744))
    : (¬ p2274) ∨ (¬ p2387) ∨ (¬ p3654) ∨ (¬ p3744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h14898 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43583 (p1977 p2027 p2764 p2996 p3553 p4348 p4444 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14906 : (¬ p1977) ∨ p2027 ∨ p2764 ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4444))
    : (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h14906 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43585 (p1977 p2027 p2662 p2766 p3540 p3644 p4111 p4348 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14908 : (¬ p1977) ∨ p2027 ∨ (¬ p2662) ∨ p2766 ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4111) ∨ (¬ p4348))
    : (¬ p2662) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4111) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h14908 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43587 (p1977 p2027 p2169 p2651 p2963 p3324 p4111 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h14910 : (¬ p1977) ∨ p2027 ∨ p2169 ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4111))
    : (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h14910 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43589 (p1977 p2027 p2476 p2534 p2662 p3146 p3578 p4111 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h14912 : (¬ p1977) ∨ p2027 ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p3146) ∨ p3578 ∨ (¬ p4111))
    : (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p3146) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3578) := h40900;
    (Or.elim h14912 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43590 (p1996 p2027 p2114 p2685 p2696 p3055 p3367 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h14913 : (¬ p1996) ∨ p2027 ∨ p2114 ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3367))
    : (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1996 := h2156;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h14913 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43594 (p1988 p2027 p2363 p2699 p3063 p3093 p3266 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14917 : (¬ p1988) ∨ p2027 ∨ (¬ p2363) ∨ p2699 ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3266))
    : (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14917 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43596 (p2001 p2027 p2166 p2355 p2449 p3486 p3690 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40872 : (¬ p2355))
    (h14919 : (¬ p2001) ∨ p2027 ∨ (¬ p2166) ∨ p2355 ∨ (¬ p2449) ∨ (¬ p3486) ∨ (¬ p3690))
    : (¬ p2166) ∨ (¬ p2449) ∨ (¬ p3486) ∨ (¬ p3690) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2001 := h2161;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2355) := h40872;
    (Or.elim h14919 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43598 (p1989 p2027 p2156 p2388 p2901 p3556 p4173 : Prop)
    (h2149 : p1989)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h14921 : (¬ p1989) ∨ p2027 ∨ (¬ p2156) ∨ p2388 ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p4173))
    : (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p4173) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1989 := h2149;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2388) := h40873;
    (Or.elim h14921 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43599 (p1976 p2027 p2766 p3055 p3684 p3692 p3880 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14922 : (¬ p1976) ∨ p2027 ∨ p2766 ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p3692) ∨ (¬ p3880))
    : (¬ p3055) ∨ (¬ p3684) ∨ (¬ p3692) ∨ (¬ p3880) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14922 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43602 (p1977 p2027 p2765 p2881 p3644 p3742 p3872 p4111 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14925 : (¬ p1977) ∨ p2027 ∨ p2765 ∨ (¬ p2881) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p3872) ∨ (¬ p4111))
    : (¬ p2881) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p3872) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h14925 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43603 (p1987 p2027 p2651 p2810 p2911 p2914 p3172 p4548 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h14926 : (¬ p1987) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2911) ∨ p2914 ∨ (¬ p3172) ∨ (¬ p4548))
    : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2911) ∨ (¬ p3172) ∨ (¬ p4548) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2914) := h40887;
    (Or.elim h14926 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43604 (p1977 p2027 p2651 p2963 p2997 p3568 p4111 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14927 : (¬ p1977) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2963) ∨ p2997 ∨ (¬ p3568) ∨ (¬ p4111))
    : (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h14927 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43607 (p1999 p2027 p2765 p2972 p3680 p4034 p4110 p4191 : Prop)
    (h2159 : p1999)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h14931 : (¬ p1999) ∨ p2027 ∨ p2765 ∨ (¬ p2972) ∨ (¬ p3680) ∨ (¬ p4034) ∨ (¬ p4110) ∨ (¬ p4191))
    : (¬ p2972) ∨ (¬ p3680) ∨ (¬ p4034) ∨ (¬ p4110) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1999 := h2159;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h14931 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43608 (p1977 p2027 p2651 p2764 p3292 p4111 p4425 p5171 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14932 : (¬ p1977) ∨ p2027 ∨ (¬ p2651) ∨ p2764 ∨ (¬ p3292) ∨ (¬ p4111) ∨ (¬ p4425) ∨ (¬ p5171))
    : (¬ p2651) ∨ (¬ p3292) ∨ (¬ p4111) ∨ (¬ p4425) ∨ (¬ p5171) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h14932 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43610 (p1977 p2027 p2662 p3043 p3346 p3680 p4111 p4425 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40893 : (¬ p3043))
    (h14934 : (¬ p1977) ∨ p2027 ∨ (¬ p2662) ∨ p3043 ∨ (¬ p3346) ∨ (¬ p3680) ∨ (¬ p4111) ∨ (¬ p4425))
    : (¬ p2662) ∨ (¬ p3346) ∨ (¬ p3680) ∨ (¬ p4111) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3043) := h40893;
    (Or.elim h14934 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43611 (p1981 p2027 p2287 p2963 p3166 p3256 p4347 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h14935 : (¬ p1981) ∨ p2027 ∨ p2287 ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p4347))
    : (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2287) := h40869;
    (Or.elim h14935 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43612 (p2006 p2027 p2287 p2946 p3156 p3414 p3694 p4156 : Prop)
    (h2166 : p2006)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h14936 : (¬ p2006) ∨ p2027 ∨ p2287 ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3414) ∨ (¬ p3694) ∨ (¬ p4156))
    : (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3414) ∨ (¬ p3694) ∨ (¬ p4156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2006 := h2166;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2287) := h40869;
    (Or.elim h14936 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43613 (p1986 p2611 p2774 p5221 : Prop)
    (h2146 : p1986)
    (h40877 : (¬ p2611))
    (h14937 : (¬ p1986) ∨ p2611 ∨ (¬ p2774) ∨ p5221)
    : (¬ p2774) ∨ p5221 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5221) := (fun h => hn (Or.inr h));
    let u2 : p1986 := h2146;
    let u3 : (¬ p2611) := h40877;
    (Or.elim h14937 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43618 (p1983 p2027 p2132 p2699 p2707 p3246 p3583 p3589 p4344 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14942 : (¬ p1983) ∨ p2027 ∨ (¬ p2132) ∨ p2699 ∨ (¬ p2707) ∨ (¬ p3246) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4344))
    : (¬ p2132) ∨ (¬ p2707) ∨ (¬ p3246) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4344) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1983 := h2143;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2699) := h40881;
    (Or.elim h14942 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43620 (p1987 p2027 p2766 p2810 p3266 p3359 p4425 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14944 : (¬ p1987) ∨ p2027 ∨ p2766 ∨ (¬ p2810) ∨ (¬ p3266) ∨ (¬ p3359) ∨ (¬ p4425))
    : (¬ p2810) ∨ (¬ p3266) ∨ (¬ p3359) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14944 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43621 (p1977 p2027 p2476 p2534 p2662 p2764 p4111 p4444 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14945 : (¬ p1977) ∨ p2027 ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ p2764 ∨ (¬ p4111) ∨ (¬ p4444))
    : (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p4111) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h14945 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43622 (p1995 p2027 p2476 p2534 p2766 p2928 p3389 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14946 : (¬ p1995) ∨ p2027 ∨ (¬ p2476) ∨ (¬ p2534) ∨ p2766 ∨ (¬ p2928) ∨ (¬ p3389))
    : (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2928) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h14946 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43623 (p1995 p2027 p2474 p2528 p2928 p3389 p3498 p3857 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40899 : (¬ p3498))
    (h14947 : (¬ p1995) ∨ p2027 ∨ (¬ p2474) ∨ (¬ p2528) ∨ (¬ p2928) ∨ (¬ p3389) ∨ p3498 ∨ (¬ p3857))
    : (¬ p2474) ∨ (¬ p2528) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3857) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2474 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3498) := h40899;
    (Or.elim h14947 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43624 (p1988 p2027 p2148 p2156 p3105 p3680 p3758 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h14948 : (¬ p1988) ∨ p2027 ∨ p2148 ∨ (¬ p2156) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p3758))
    : (¬ p2156) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p3758) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2148) := h40865;
    (Or.elim h14948 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43629 (p1977 p2027 p2662 p2764 p3540 p4111 p4278 p4381 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h14953 : (¬ p1977) ∨ p2027 ∨ (¬ p2662) ∨ p2764 ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p4381))
    : (¬ p2662) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h14953 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43632 (p1977 p2027 p2474 p2662 p2964 p3276 p3857 p4111 p4444 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40889 : (¬ p2964))
    (h14956 : (¬ p1977) ∨ p2027 ∨ (¬ p2474) ∨ (¬ p2662) ∨ p2964 ∨ (¬ p3276) ∨ (¬ p3857) ∨ (¬ p4111) ∨ (¬ p4444))
    : (¬ p2474) ∨ (¬ p2662) ∨ (¬ p3276) ∨ (¬ p3857) ∨ (¬ p4111) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2474 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1977 := h2137;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2964) := h40889;
    (Or.elim h14956 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43634 (p1975 p2027 p2156 p2274 p2619 p3474 p4120 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40898 : (¬ p3474))
    (h14958 : (¬ p1975) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2619) ∨ p3474 ∨ (¬ p4120))
    : (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2619) ∨ (¬ p4120) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3474) := h40898;
    (Or.elim h14958 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43635 (p1977 p2027 p2462 p2662 p2911 p3551 p4111 p4278 p5197 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h14959 : (¬ p1977) ∨ p2027 ∨ p2462 ∨ (¬ p2662) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p5197))
    : (¬ p2662) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1977 := h2137;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2462) := h40875;
    (Or.elim h14959 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43636 (p1988 p2027 p2132 p2611 p2860 p3125 p3461 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h14960 : (¬ p1988) ∨ p2027 ∨ (¬ p2132) ∨ p2611 ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3461))
    : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h14960 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43637 (p1981 p2027 p2166 p2210 p2699 p3146 p4347 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14962 : (¬ p1981) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ p2699 ∨ (¬ p3146) ∨ (¬ p4347))
    : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3146) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h14962 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43639 (p1994 p2202 p3574 p4717 : Prop)
    (h2154 : p1994)
    (h40867 : (¬ p2202))
    (h14964 : (¬ p1994) ∨ p2202 ∨ (¬ p3574) ∨ p4717)
    : (¬ p3574) ∨ p4717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3574 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4717) := (fun h => hn (Or.inr h));
    let u2 : p1994 := h2154;
    let u3 : (¬ p2202) := h40867;
    (Or.elim h14964 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step43645 (p1977 p2027 p2387 p2459 p2633 p2667 p4154 p4347 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14970 : (¬ p1977) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2459) ∨ p2633 ∨ (¬ p2667) ∨ (¬ p4154) ∨ (¬ p4347))
    : (¬ p2387) ∨ (¬ p2459) ∨ (¬ p2667) ∨ (¬ p4154) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h14970 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43646 (p1977 p2027 p2459 p2476 p2534 p2633 p2662 p4111 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14971 : (¬ p1977) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ p2633 ∨ (¬ p2662) ∨ (¬ p4111))
    : (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h14971 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43647 (p1977 p2027 p2462 p2667 p2761 p3946 p4154 p4191 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h14972 : (¬ p1977) ∨ p2027 ∨ p2462 ∨ (¬ p2667) ∨ (¬ p2761) ∨ (¬ p3946) ∨ (¬ p4154) ∨ (¬ p4191))
    : (¬ p2667) ∨ (¬ p2761) ∨ (¬ p3946) ∨ (¬ p4154) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2667 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2462) := h40875;
    (Or.elim h14972 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43649 (p1983 p2027 p2323 p2449 p2651 p3027 p4111 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14974 : (¬ p1983) ∨ p2027 ∨ p2323 ∨ (¬ p2449) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p4111))
    : (¬ p2449) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14974 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43650 (p2002 p2027 p2177 p2829 p2997 p3551 p3588 p3959 : Prop)
    (h2162 : p2002)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h14975 : (¬ p2002) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2829) ∨ p2997 ∨ (¬ p3551) ∨ (¬ p3588) ∨ (¬ p3959))
    : (¬ p2177) ∨ (¬ p2829) ∨ (¬ p3551) ∨ (¬ p3588) ∨ (¬ p3959) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2002 := h2162;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h14975 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43653 (p1990 p2027 p2331 p2388 p2952 p3097 p3309 p4319 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h14978 : (¬ p1990) ∨ p2027 ∨ (¬ p2331) ∨ p2388 ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4319))
    : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4319) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2388) := h40873;
    (Or.elim h14978 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43656 (p1975 p2027 p2274 p2383 p2388 p2952 p3987 p3989 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h14981 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2383) ∨ p2388 ∨ (¬ p2952) ∨ (¬ p3987) ∨ (¬ p3989))
    : (¬ p2274) ∨ (¬ p2383) ∨ (¬ p2952) ∨ (¬ p3987) ∨ (¬ p3989) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2388) := h40873;
    (Or.elim h14981 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43657 (p1996 p2027 p2331 p2388 p2952 p3027 p4154 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h14982 : (¬ p1996) ∨ p2027 ∨ (¬ p2331) ∨ p2388 ∨ (¬ p2952) ∨ (¬ p3027) ∨ (¬ p4154))
    : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3027) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1996 := h2156;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2388) := h40873;
    (Or.elim h14982 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43658 (p1977 p2027 p2633 p2996 p3246 p3570 p3821 p4155 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14983 : (¬ p1977) ∨ p2027 ∨ p2633 ∨ (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3821) ∨ (¬ p4155))
    : (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3821) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h14983 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43659 (p1977 p2027 p2299 p2633 p2957 p3097 p3646 p3662 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14984 : (¬ p1977) ∨ p2027 ∨ (¬ p2299) ∨ p2633 ∨ (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3662))
    : (¬ p2299) ∨ (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h14984 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43662 (p1977 p2027 p2957 p3556 p3570 p3662 p3982 p5558 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40909 : (¬ p3982))
    (h14987 : (¬ p1977) ∨ p2027 ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ p3982 ∨ (¬ p5558))
    : (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3982) := h40909;
    (Or.elim h14987 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43663 (p1982 p2027 p2253 p2363 p2699 p3166 p4009 p5580 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h14988 : (¬ p1982) ∨ p2027 ∨ (¬ p2253) ∨ (¬ p2363) ∨ p2699 ∨ (¬ p3166) ∨ (¬ p4009) ∨ (¬ p5580))
    : (¬ p2253) ∨ (¬ p2363) ∨ (¬ p3166) ∨ (¬ p4009) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h14988 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43664 (p1977 p2027 p2766 p2957 p3556 p3570 p3662 p4348 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h14989 : (¬ p1977) ∨ p2027 ∨ p2766 ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4348))
    : (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h14989 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43666 (p1999 p2027 p2633 p2761 p3246 p3570 p4191 : Prop)
    (h2159 : p1999)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14991 : (¬ p1999) ∨ p2027 ∨ p2633 ∨ (¬ p2761) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4191))
    : (¬ p2761) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1999 := h2159;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h14991 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43668 (p1975 p2027 p2323 p2331 p2553 p2668 p3956 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14993 : (¬ p1975) ∨ p2027 ∨ p2323 ∨ (¬ p2331) ∨ (¬ p2553) ∨ (¬ p2668) ∨ (¬ p3956))
    : (¬ p2331) ∨ (¬ p2553) ∨ (¬ p2668) ∨ (¬ p3956) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14993 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43671 (p1977 p2027 p2459 p2633 p2957 p3662 p3692 p4120 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14996 : (¬ p1977) ∨ p2027 ∨ (¬ p2459) ∨ p2633 ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p4120))
    : (¬ p2459) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p4120) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h14996 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43672 (p1982 p2027 p2190 p2202 p2363 p2563 p3969 p5580 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h14997 : (¬ p1982) ∨ p2027 ∨ (¬ p2190) ∨ p2202 ∨ (¬ p2363) ∨ (¬ p2563) ∨ (¬ p3969) ∨ (¬ p5580))
    : (¬ p2190) ∨ (¬ p2363) ∨ (¬ p2563) ∨ (¬ p3969) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h14997 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43673 (p1988 p2027 p2323 p2651 p3016 p3461 p3564 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h14998 : (¬ p1988) ∨ p2027 ∨ p2323 ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3461) ∨ (¬ p3564))
    : (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3461) ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h14998 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43674 (p1977 p2027 p2633 p2957 p3570 p3662 p4129 p4372 p4984 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h14999 : (¬ p1977) ∨ p2027 ∨ p2633 ∨ (¬ p2957) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4129) ∨ (¬ p4372) ∨ (¬ p4984))
    : (¬ p2957) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4129) ∨ (¬ p4372) ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1977 := h2137;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2633) := h40879;
    (Or.elim h14999 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43676 (p1988 p2027 p2608 p2699 p2829 p3461 p3483 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h15018 : (¬ p1988) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2829) ∨ (¬ p3461) ∨ (¬ p3483))
    : (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3461) ∨ (¬ p3483) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h15018 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43682 (p1997 p2027 p2323 p2641 p2807 p2996 p3986 p4110 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h15024 : (¬ p1997) ∨ p2027 ∨ p2323 ∨ (¬ p2641) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p3986) ∨ (¬ p4110))
    : (¬ p2641) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p3986) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h15024 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43683 (p1977 p2027 p2462 p2881 p2957 p3551 p3662 p3690 p4984 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h15025 : (¬ p1977) ∨ p2027 ∨ p2462 ∨ (¬ p2881) ∨ (¬ p2957) ∨ (¬ p3551) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p4984))
    : (¬ p2881) ∨ (¬ p2957) ∨ (¬ p3551) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1977 := h2137;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2462) := h40875;
    (Or.elim h15025 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43686 (p1981 p2027 p2699 p3093 p3527 p3941 p4452 p5580 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h15028 : (¬ p1981) ∨ p2027 ∨ p2699 ∨ (¬ p3093) ∨ (¬ p3527) ∨ (¬ p3941) ∨ (¬ p4452) ∨ (¬ p5580))
    : (¬ p3093) ∨ (¬ p3527) ∨ (¬ p3941) ∨ (¬ p4452) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1981 := h2141;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h15028 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43687 (p1976 p2027 p2299 p2780 p2881 p2938 p3822 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h15029 : (¬ p1976) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2780) ∨ (¬ p2881) ∨ p2938 ∨ (¬ p3822))
    : (¬ p2299) ∨ (¬ p2780) ∨ (¬ p2881) ∨ (¬ p3822) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h15029 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43689 (p1975 p2027 p2253 p2331 p2553 p2699 p3323 p4137 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h15031 : (¬ p1975) ∨ p2027 ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2553) ∨ p2699 ∨ (¬ p3323) ∨ (¬ p4137))
    : (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2553) ∨ (¬ p3323) ∨ (¬ p4137) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h15031 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43690 (p1975 p2027 p2299 p2323 p3527 p3654 p3987 p4026 p4452 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h15032 : (¬ p1975) ∨ p2027 ∨ (¬ p2299) ∨ p2323 ∨ (¬ p3527) ∨ (¬ p3654) ∨ (¬ p3987) ∨ (¬ p4026) ∨ (¬ p4452))
    : (¬ p2299) ∨ (¬ p3527) ∨ (¬ p3654) ∨ (¬ p3987) ∨ (¬ p4026) ∨ (¬ p4452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1975 := h2135;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2323) := h40870;
    (Or.elim h15032 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step43691 (p1975 p2027 p2299 p2764 p3527 p3817 p4444 p4445 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h15033 : (¬ p1975) ∨ p2027 ∨ (¬ p2299) ∨ p2764 ∨ (¬ p3527) ∨ (¬ p3817) ∨ (¬ p4444) ∨ (¬ p4445))
    : (¬ p2299) ∨ (¬ p3527) ∨ (¬ p3817) ∨ (¬ p4444) ∨ (¬ p4445) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h15033 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43692 (p2004 p2027 p2881 p2938 p3516 p3551 p3817 : Prop)
    (h2164 : p2004)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h15034 : (¬ p2004) ∨ p2027 ∨ (¬ p2881) ∨ p2938 ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3817))
    : (¬ p2881) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3817) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2004 := h2164;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h15034 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43695 (p1982 p2027 p2363 p2765 p2881 p3872 p3941 p5580 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h15037 : (¬ p1982) ∨ p2027 ∨ (¬ p2363) ∨ p2765 ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p3941) ∨ (¬ p5580))
    : (¬ p2363) ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p3941) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h15037 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43698 (p1975 p2027 p2295 p2964 p3276 p4037 p4191 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40889 : (¬ p2964))
    (h15040 : (¬ p1975) ∨ p2027 ∨ (¬ p2295) ∨ p2964 ∨ (¬ p3276) ∨ (¬ p4037) ∨ (¬ p4191))
    : (¬ p2295) ∨ (¬ p3276) ∨ (¬ p4037) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2964) := h40889;
    (Or.elim h15040 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43702 (p1990 p2027 p2323 p2553 p2651 p3016 p3097 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h15044 : (¬ p1990) ∨ p2027 ∨ p2323 ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3097))
    : (¬ p2553) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3097) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h15044 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43704 (p1999 p2027 p2295 p2323 p2331 p2588 p3564 : Prop)
    (h2159 : p1999)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h15046 : (¬ p1999) ∨ p2027 ∨ (¬ p2295) ∨ p2323 ∨ (¬ p2331) ∨ (¬ p2588) ∨ (¬ p3564))
    : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2588) ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1999 := h2159;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h15046 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43708 (p1975 p2027 p2299 p2699 p2881 p2891 p3379 p3948 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h15050 : (¬ p1975) ∨ p2027 ∨ (¬ p2299) ∨ p2699 ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3379) ∨ (¬ p3948))
    : (¬ p2299) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3379) ∨ (¬ p3948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h15050 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step43717 (p1997 p2027 p2633 p2972 p3486 p3570 p4948 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h15061 : (¬ p1997) ∨ p2027 ∨ p2633 ∨ (¬ p2972) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4948))
    : (¬ p2972) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h15061 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step43732 (p1992 p2027 p2598 p2633 p3425 p3585 p3659 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h15077 : (¬ p1992) ∨ p2027 ∨ (¬ p2598) ∨ p2633 ∨ (¬ p3425) ∨ (¬ p3585) ∨ (¬ p3659))
    : (¬ p2598) ∨ (¬ p3425) ∨ (¬ p3585) ∨ (¬ p3659) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h15077 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

end ElevenRUP
