import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step120942 (p2166 p2619 p2737 p3371 p5052 : Prop)
    (h105473 : p5052)
    (h84710 : p2737 ∨ p2619 ∨ (¬ p2166) ∨ (¬ p5052) ∨ (¬ p3371))
    : p2619 ∨ (¬ p3371) ∨ (¬ p2166) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5052 := h105473;
    (Or.elim h84710 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step120945 (p2437 p2608 p2619 p2839 p3083 p3389 p4158 p5190 : Prop)
    (h105487 : p5190)
    (h106187 : p4158)
    (h84717 : (¬ p3389) ∨ p2437 ∨ (¬ p5190) ∨ p2619 ∨ (¬ p4158) ∨ p2839 ∨ p2608 ∨ (¬ p3083))
    : (¬ p3083) ∨ p2608 ∨ p2619 ∨ p2839 ∨ (¬ p3389) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5190 := h105487;
    let u7 : p4158 := h106187;
    (Or.elim h84717 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step120947 (p2248 p2363 p2608 p2619 p2839 p3166 p3256 p4134 : Prop)
    (h105365 : p2248)
    (h105379 : p4134)
    (h84730 : (¬ p3256) ∨ p2363 ∨ (¬ p4134) ∨ p2839 ∨ (¬ p3166) ∨ p2608 ∨ p2619 ∨ (¬ p2248))
    : (¬ p3166) ∨ p2619 ∨ (¬ p3256) ∨ p2608 ∨ p2363 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4134 := h105379;
    (Or.elim h84730 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step120952 (p2132 p2307 p2553 p2619 p2781 p3146 p3564 p4330 : Prop)
    (h106329 : p4330)
    (h84741 : (¬ p2307) ∨ p2619 ∨ p3146 ∨ p2553 ∨ (¬ p2781) ∨ (¬ p3564) ∨ p2132 ∨ (¬ p4330))
    : (¬ p3564) ∨ (¬ p2307) ∨ p2619 ∨ p2132 ∨ p2553 ∨ p3146 ∨ (¬ p2781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4330 := h106329;
    (Or.elim h84741 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step120954 (p2132 p2619 p3146 p3461 p3707 p3830 p4330 p4736 : Prop)
    (h105431 : p4736)
    (h106329 : p4330)
    (h84749 : (¬ p3707) ∨ p3461 ∨ p2619 ∨ (¬ p3830) ∨ (¬ p4736) ∨ p2132 ∨ (¬ p4330) ∨ p3146)
    : (¬ p3707) ∨ p2619 ∨ (¬ p3830) ∨ p3146 ∨ p3461 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4330 := h106329;
    (Or.elim h84749 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step120956 (p2528 p2532 p2619 p3105 p4158 : Prop)
    (h106187 : p4158)
    (h84755 : (¬ p3105) ∨ p2528 ∨ (¬ p2532) ∨ p2619 ∨ (¬ p4158))
    : p2619 ∨ p2528 ∨ (¬ p2532) ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4158 := h106187;
    (Or.elim h84755 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step120957 (p2532 p2619 p3105 p3256 p5063 : Prop)
    (h105474 : p5063)
    (h84760 : (¬ p3105) ∨ p3256 ∨ (¬ p2532) ∨ p2619 ∨ (¬ p5063))
    : p2619 ∨ (¬ p3105) ∨ p3256 ∨ (¬ p2532) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5063 := h105474;
    (Or.elim h84760 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step120960 (p2528 p2619 p3146 p4355 p4882 : Prop)
    (h105453 : p4882)
    (h84768 : p2619 ∨ p3146 ∨ (¬ p4882) ∨ (¬ p2528) ∨ (¬ p4355))
    : (¬ p4355) ∨ (¬ p2528) ∨ p2619 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4882 := h105453;
    (Or.elim h84768 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step120963 (p2246 p2553 p2619 p2651 p2744 p2870 p3016 p3051 p3645 p4506 p4874 : Prop)
    (h106503 : p2744)
    (h84776 : (¬ p4874) ∨ (¬ p2246) ∨ (¬ p3645) ∨ (¬ p2553) ∨ (¬ p3016) ∨ (¬ p2870) ∨ (¬ p2744) ∨ (¬ p4506) ∨ p3051 ∨ p2619 ∨ (¬ p2651))
    : p2619 ∨ (¬ p3645) ∨ (¬ p3016) ∨ p3051 ∨ (¬ p4506) ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p2870) ∨ (¬ p2553) ∨ (¬ p4874) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    (Or.elim h84776 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u0 q9))) (fun r9 => (False.elim (r9 u5)))))))))))))))))))))))

theorem step120965 (p2177 p2248 p2295 p2331 p2608 p2619 p2839 p4905 : Prop)
    (h105365 : p2248)
    (h105995 : p4905)
    (h84778 : p2608 ∨ p2839 ∨ (¬ p2177) ∨ (¬ p4905) ∨ (¬ p2331) ∨ (¬ p2248) ∨ p2619 ∨ (¬ p2295))
    : p2839 ∨ p2619 ∨ (¬ p2331) ∨ p2608 ∨ (¬ p2177) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4905 := h105995;
    (Or.elim h84778 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step120966 (p2132 p2396 p2553 p2573 p2619 p3146 p3366 p3519 p3950 p4376 : Prop)
    (h106320 : p4376)
    (h84780 : (¬ p2553) ∨ (¬ p3519) ∨ (¬ p2396) ∨ (¬ p4376) ∨ (¬ p3950) ∨ (¬ p3366) ∨ p2619 ∨ p3146 ∨ (¬ p2573) ∨ p2132)
    : (¬ p2553) ∨ p2132 ∨ p2619 ∨ (¬ p3366) ∨ (¬ p3950) ∨ (¬ p2396) ∨ (¬ p3519) ∨ p3146 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h84780 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (u1 r8)))))))))))))))))))))

theorem step120971 (p2132 p2619 p2651 p3016 p3146 p3564 p4330 p4786 : Prop)
    (h106425 : p4786)
    (h106329 : p4330)
    (h84793 : p2132 ∨ (¬ p3564) ∨ (¬ p2651) ∨ p3146 ∨ (¬ p4330) ∨ (¬ p4786) ∨ p2619 ∨ (¬ p3016))
    : (¬ p3564) ∨ (¬ p3016) ∨ (¬ p2651) ∨ p3146 ∨ p2619 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4786 := h106425;
    let u7 : p4330 := h106329;
    (Or.elim h84793 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step120973 (p2136 p2156 p2459 p2619 p2860 p3166 p3256 p4786 p4905 : Prop)
    (h105995 : p4905)
    (h106425 : p4786)
    (h84797 : (¬ p3256) ∨ p2619 ∨ (¬ p3166) ∨ p2156 ∨ (¬ p2860) ∨ (¬ p2136) ∨ (¬ p4786) ∨ p2459 ∨ (¬ p4905))
    : p2619 ∨ (¬ p2860) ∨ p2156 ∨ (¬ p3166) ∨ (¬ p2136) ∨ p2459 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4905 := h105995;
    let u8 : p4786 := h106425;
    (Or.elim h84797 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step120977 (p2132 p2619 p2761 p3146 p3286 p3506 p3950 p4786 : Prop)
    (h106425 : p4786)
    (h84803 : (¬ p3506) ∨ p2761 ∨ p2132 ∨ (¬ p4786) ∨ (¬ p3286) ∨ p2619 ∨ (¬ p3950) ∨ p3146)
    : (¬ p3506) ∨ (¬ p3286) ∨ p2132 ∨ p2761 ∨ p2619 ∨ p3146 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    (Or.elim h84803 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u5 r6)))))))))))))))))

theorem step120978 (p2156 p2220 p2619 p2870 p4558 : Prop)
    (h105400 : p4558)
    (h84807 : (¬ p2220) ∨ p2619 ∨ (¬ p2870) ∨ p2156 ∨ (¬ p4558))
    : p2619 ∨ (¬ p2870) ∨ p2156 ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h84807 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step120979 (p2132 p2331 p2363 p2619 p2668 p4786 p5118 p5568 : Prop)
    (h106425 : p4786)
    (h105482 : p5118)
    (h84808 : (¬ p5568) ∨ (¬ p2668) ∨ (¬ p4786) ∨ p2619 ∨ p2132 ∨ (¬ p2363) ∨ (¬ p5118) ∨ (¬ p2331))
    : p2619 ∨ (¬ p5568) ∨ p2132 ∨ (¬ p2668) ∨ (¬ p2331) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4786 := h106425;
    let u7 : p5118 := h105482;
    (Or.elim h84808 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step120980 (p2619 p4149 p4355 p4882 p5568 : Prop)
    (h105453 : p4882)
    (h84810 : (¬ p5568) ∨ (¬ p4149) ∨ (¬ p4355) ∨ p2619 ∨ (¬ p4882))
    : (¬ p4149) ∨ (¬ p4355) ∨ p2619 ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4882 := h105453;
    (Or.elim h84810 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step120981 (p2132 p2331 p2619 p3323 p3461 p4786 p5123 p5568 : Prop)
    (h106425 : p4786)
    (h84811 : (¬ p3323) ∨ (¬ p3461) ∨ p2132 ∨ (¬ p5568) ∨ (¬ p5123) ∨ (¬ p4786) ∨ p2619 ∨ (¬ p2331))
    : (¬ p5568) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p2331) ∨ p2132 ∨ p2619 ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    (Or.elim h84811 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step120982 (p2373 p2563 p2619 p2870 p4558 : Prop)
    (h105400 : p4558)
    (h84819 : (¬ p2870) ∨ p2619 ∨ (¬ p4558) ∨ (¬ p2373) ∨ p2563)
    : p2619 ∨ p2563 ∨ (¬ p2870) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h84819 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step120984 (p2132 p2573 p2619 p3366 p3461 p3519 p3564 p4376 p5123 p5568 : Prop)
    (h106320 : p4376)
    (h84823 : (¬ p5568) ∨ p2132 ∨ p2619 ∨ (¬ p3519) ∨ (¬ p3564) ∨ (¬ p2573) ∨ (¬ p3366) ∨ (¬ p5123) ∨ (¬ p4376) ∨ (¬ p3461))
    : (¬ p2573) ∨ (¬ p3519) ∨ (¬ p3461) ∨ (¬ p5568) ∨ (¬ p3564) ∨ (¬ p3366) ∨ p2619 ∨ p2132 ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h84823 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step120985 (p2619 p2751 p2992 p3156 p4392 : Prop)
    (h106343 : p2751)
    (h84824 : (¬ p2992) ∨ p2619 ∨ (¬ p2751) ∨ (¬ p4392) ∨ (¬ p3156))
    : (¬ p4392) ∨ p2619 ∨ (¬ p2992) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4392 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    (Or.elim h84824 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step120988 (p2132 p2352 p2363 p2573 p2619 p3366 p3519 p4376 p5118 p5568 : Prop)
    (h106320 : p4376)
    (h105482 : p5118)
    (h84832 : (¬ p5568) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p3519) ∨ (¬ p5118) ∨ (¬ p3366) ∨ p2132 ∨ p2619 ∨ (¬ p2573) ∨ (¬ p4376))
    : (¬ p2573) ∨ p2132 ∨ (¬ p2363) ∨ (¬ p2352) ∨ p2619 ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p5118 := h105482;
    (Or.elim h84832 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step120989 (p2132 p2619 p3366 p3379 p3707 p3830 p4376 p5123 p5568 : Prop)
    (h106320 : p4376)
    (h84833 : (¬ p5568) ∨ (¬ p3830) ∨ (¬ p4376) ∨ (¬ p5123) ∨ p3379 ∨ (¬ p3366) ∨ p2132 ∨ (¬ p3707) ∨ p2619)
    : (¬ p3707) ∨ (¬ p5568) ∨ p2619 ∨ (¬ p5123) ∨ (¬ p3366) ∨ (¬ p3830) ∨ p2132 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    (Or.elim h84833 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (u2 r7)))))))))))))))))))

theorem step120991 (p2156 p2220 p2284 p2619 p4906 : Prop)
    (h105632 : p4906)
    (h84842 : (¬ p2220) ∨ p2619 ∨ (¬ p2284) ∨ (¬ p4906) ∨ p2156)
    : p2156 ∨ p2619 ∨ (¬ p2220) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4906 := h105632;
    (Or.elim h84842 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step120996 (p2132 p2774 p2870 p4185 p4555 : Prop)
    (h105542 : p4555)
    (h84868 : p2870 ∨ p2132 ∨ (¬ p4555) ∨ (¬ p4185) ∨ (¬ p2774))
    : (¬ p2774) ∨ p2132 ∨ p2870 ∨ (¬ p4185) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    (Or.elim h84868 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step120997 (p2143 p2829 p2839 p3051 p4185 p4555 : Prop)
    (h105542 : p4555)
    (h84872 : (¬ p2829) ∨ p2839 ∨ (¬ p2143) ∨ (¬ p4185) ∨ p3051 ∨ (¬ p4555))
    : (¬ p2829) ∨ p3051 ∨ (¬ p4185) ∨ (¬ p2143) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4555 := h105542;
    (Or.elim h84872 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step120999 (p2156 p2187 p2449 p2651 p2753 p2761 p3580 p3645 p4117 p4877 p5123 p5580 : Prop)
    (h105451 : p4877)
    (h84893 : (¬ p5580) ∨ (¬ p5123) ∨ (¬ p4117) ∨ (¬ p4877) ∨ (¬ p2753) ∨ (¬ p3580) ∨ (¬ p2449) ∨ (¬ p2761) ∨ p2187 ∨ (¬ p3645) ∨ (¬ p2651) ∨ p2156)
    : (¬ p2761) ∨ (¬ p2449) ∨ p2156 ∨ (¬ p5123) ∨ p2187 ∨ (¬ p3580) ∨ (¬ p2753) ∨ (¬ p4117) ∨ (¬ p3645) ∨ (¬ p2651) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4877 := h105451;
    (Or.elim h84893 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (u2 r10)))))))))))))))))))))))))

theorem step121002 (p2331 p2668 p2761 p3051 p3246 p3366 p3519 p4236 p4376 p4399 p5123 p5580 : Prop)
    (h106320 : p4376)
    (h84897 : (¬ p5580) ∨ (¬ p3519) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3051) ∨ p2668 ∨ (¬ p4399) ∨ (¬ p5123) ∨ (¬ p4236) ∨ (¬ p2761) ∨ (¬ p4376) ∨ p2331)
    : (¬ p4236) ∨ (¬ p3519) ∨ (¬ p3246) ∨ (¬ p3051) ∨ p2331 ∨ (¬ p3366) ∨ p2668 ∨ (¬ p2761) ∨ (¬ p5580) ∨ (¬ p4399) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4376 := h106320;
    (Or.elim h84897 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (False.elim (u4 r10)))))))))))))))))))))))))

theorem step121004 (p2190 p2274 p3969 p4405 p5580 : Prop)
    (h105512 : p4405)
    (h84901 : (¬ p5580) ∨ (¬ p2190) ∨ (¬ p3969) ∨ (¬ p4405) ∨ p2274)
    : (¬ p3969) ∨ (¬ p5580) ∨ (¬ p2190) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    (Or.elim h84901 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step121005 (p2352 p2528 p3564 p5118 p5580 : Prop)
    (h105482 : p5118)
    (h84903 : (¬ p5580) ∨ (¬ p5118) ∨ (¬ p2528) ∨ (¬ p3564) ∨ p2352)
    : (¬ p3564) ∨ (¬ p5580) ∨ (¬ p2528) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5118 := h105482;
    (Or.elim h84903 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step121008 (p2774 p2819 p2946 p3115 p3680 p4786 p5123 p5580 : Prop)
    (h106425 : p4786)
    (h84912 : (¬ p5580) ∨ (¬ p3115) ∨ (¬ p2946) ∨ (¬ p3680) ∨ (¬ p5123) ∨ p2774 ∨ (¬ p4786) ∨ p2819)
    : (¬ p3680) ∨ (¬ p3115) ∨ (¬ p2946) ∨ (¬ p5580) ∨ p2774 ∨ p2819 ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    (Or.elim h84912 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u5 r6)))))))))))))))))

theorem step121013 (p2241 p2744 p2819 p2829 p3073 p3449 p5118 p5580 : Prop)
    (h106503 : p2744)
    (h105482 : p5118)
    (h84921 : (¬ p5580) ∨ (¬ p5118) ∨ p2241 ∨ (¬ p2744) ∨ (¬ p3449) ∨ p2819 ∨ (¬ p3073) ∨ p2829)
    : (¬ p3449) ∨ (¬ p5580) ∨ p2241 ∨ p2829 ∨ p2819 ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2744 := h106503;
    let u7 : p5118 := h105482;
    (Or.elim h84921 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step121014 (p2136 p2156 p2187 p2241 p2744 p3073 p3366 p3449 p5118 p5580 : Prop)
    (h106503 : p2744)
    (h105482 : p5118)
    (h84922 : (¬ p5580) ∨ p2241 ∨ (¬ p5118) ∨ p2156 ∨ (¬ p3449) ∨ (¬ p3073) ∨ (¬ p2744) ∨ (¬ p3366) ∨ p2187 ∨ (¬ p2136))
    : (¬ p3449) ∨ (¬ p5580) ∨ p2187 ∨ (¬ p2136) ∨ p2156 ∨ (¬ p3366) ∨ (¬ p3073) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p5118 := h105482;
    (Or.elim h84922 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u2 q8))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step121016 (p2252 p2331 p2608 p2668 p2750 p3707 p3830 p5123 p5580 : Prop)
    (h106345 : p2750)
    (h84925 : (¬ p5580) ∨ p2608 ∨ p2331 ∨ (¬ p3707) ∨ (¬ p2750) ∨ p2668 ∨ (¬ p3830) ∨ (¬ p5123) ∨ (¬ p2252))
    : (¬ p3707) ∨ (¬ p5580) ∨ p2668 ∨ p2331 ∨ (¬ p2252) ∨ (¬ p3830) ∨ p2608 ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    (Or.elim h84925 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step121020 (p2651 p2774 p2819 p3276 p3343 p4786 p5123 p5580 : Prop)
    (h106425 : p4786)
    (h84929 : (¬ p5580) ∨ (¬ p5123) ∨ (¬ p3276) ∨ (¬ p3343) ∨ p2774 ∨ (¬ p2651) ∨ p2819 ∨ (¬ p4786))
    : (¬ p3276) ∨ (¬ p3343) ∨ (¬ p5580) ∨ p2819 ∨ (¬ p2651) ∨ p2774 ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    (Or.elim h84929 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121022 (p2510 p2553 p4149 p4405 p5580 : Prop)
    (h105512 : p4405)
    (h84935 : (¬ p4149) ∨ (¬ p5580) ∨ p2553 ∨ (¬ p4405) ∨ (¬ p2510))
    : (¬ p2510) ∨ (¬ p5580) ∨ (¬ p4149) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2510 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    (Or.elim h84935 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step121023 (p2249 p2331 p2656 p2727 p3212 p3680 p3922 p3923 p4399 p5123 p5580 : Prop)
    (h106513 : p2249)
    (h84945 : (¬ p5580) ∨ (¬ p3680) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p2249) ∨ (¬ p3212) ∨ (¬ p2727) ∨ (¬ p2656) ∨ (¬ p4399) ∨ p2331 ∨ (¬ p5123))
    : (¬ p3212) ∨ p2331 ∨ (¬ p4399) ∨ (¬ p5580) ∨ (¬ p3922) ∨ (¬ p2727) ∨ (¬ p3923) ∨ (¬ p2656) ∨ (¬ p3680) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2249 := h106513;
    (Or.elim h84945 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u1 q9))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step121024 (p2156 p2187 p2696 p2753 p3506 p3645 p3755 p4877 p5123 p5580 : Prop)
    (h105451 : p4877)
    (h84947 : (¬ p5580) ∨ (¬ p2753) ∨ p2187 ∨ (¬ p3645) ∨ (¬ p3755) ∨ p2156 ∨ (¬ p3506) ∨ (¬ p4877) ∨ (¬ p2696) ∨ (¬ p5123))
    : (¬ p3506) ∨ (¬ p3755) ∨ p2156 ∨ (¬ p5580) ∨ p2187 ∨ (¬ p2696) ∨ (¬ p3645) ∨ (¬ p2753) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4877 := h105451;
    (Or.elim h84947 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step121027 (p2383 p2668 p2946 p3987 p4566 : Prop)
    (h106307 : p4566)
    (h84976 : (¬ p2383) ∨ p2668 ∨ (¬ p4566) ∨ (¬ p3987) ∨ p2946)
    : p2946 ∨ (¬ p2383) ∨ p2668 ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4566 := h106307;
    (Or.elim h84976 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step121028 (p2383 p2668 p2797 p3987 p4790 : Prop)
    (h106424 : p4790)
    (h84982 : p2797 ∨ (¬ p2383) ∨ p2668 ∨ (¬ p4790) ∨ (¬ p3987))
    : p2797 ∨ (¬ p2383) ∨ (¬ p3987) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    (Or.elim h84982 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121035 (p2210 p2553 p2598 p2881 p3422 p3527 p4431 p4556 p4736 : Prop)
    (h105431 : p4736)
    (h105399 : p4556)
    (h85069 : (¬ p3527) ∨ (¬ p4736) ∨ (¬ p4556) ∨ p2553 ∨ (¬ p2210) ∨ p3422 ∨ p2598 ∨ p2881 ∨ (¬ p4431))
    : p3422 ∨ (¬ p3527) ∨ p2553 ∨ (¬ p4431) ∨ p2598 ∨ (¬ p2210) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4556 := h105399;
    (Or.elim h85069 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step121037 (p2295 p2696 p2797 p2881 p3399 p3527 p4556 p4736 : Prop)
    (h105431 : p4736)
    (h105399 : p4556)
    (h85077 : (¬ p3527) ∨ (¬ p4556) ∨ (¬ p3399) ∨ p2881 ∨ p2696 ∨ p2295 ∨ p2797 ∨ (¬ p4736))
    : p2797 ∨ p2696 ∨ p2881 ∨ (¬ p3399) ∨ p2295 ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4556 := h105399;
    (Or.elim h85077 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step121041 (p2341 p2427 p3527 p3959 p4344 p4431 p4632 : Prop)
    (h106257 : p4632)
    (h85086 : (¬ p3527) ∨ p2341 ∨ (¬ p4344) ∨ (¬ p3959) ∨ p2427 ∨ (¬ p4632) ∨ (¬ p4431))
    : p2341 ∨ (¬ p3527) ∨ (¬ p4344) ∨ p2427 ∨ (¬ p4431) ∨ (¬ p3959) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4632 := h106257;
    (Or.elim h85086 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step121042 (p2156 p2274 p2396 p2441 p2608 p2911 p3399 p3527 p3645 p4877 : Prop)
    (h105451 : p4877)
    (h85090 : (¬ p3527) ∨ p2396 ∨ (¬ p2441) ∨ (¬ p4877) ∨ p2156 ∨ p2608 ∨ (¬ p3645) ∨ (¬ p3399) ∨ p2911 ∨ p2274)
    : (¬ p2441) ∨ (¬ p3645) ∨ p2608 ∨ p2156 ∨ (¬ p3527) ∨ (¬ p3399) ∨ p2274 ∨ p2396 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4877 := h105451;
    (Or.elim h85090 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u8 q8))) (fun r8 => (False.elim (u6 r8)))))))))))))))))))))

theorem step121045 (p2177 p2254 p2685 p2946 p3136 p3399 p3527 p4361 : Prop)
    (h105366 : p2254)
    (h105382 : p4361)
    (h85099 : (¬ p3527) ∨ (¬ p3136) ∨ p2177 ∨ (¬ p3399) ∨ (¬ p4361) ∨ (¬ p2254) ∨ p2685 ∨ p2946)
    : p2946 ∨ (¬ p3136) ∨ p2685 ∨ (¬ p3399) ∨ p2177 ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4361 := h105382;
    (Or.elim h85099 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step121048 (p2254 p2274 p2284 p2717 p2946 p3399 p3527 p4473 : Prop)
    (h105366 : p2254)
    (h85123 : (¬ p3527) ∨ p2946 ∨ (¬ p2254) ∨ (¬ p4473) ∨ (¬ p3399) ∨ p2717 ∨ p2284 ∨ p2274)
    : p2717 ∨ p2946 ∨ p2274 ∨ (¬ p3527) ∨ (¬ p3399) ∨ p2284 ∨ (¬ p4473) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h85123 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (u2 r6)))))))))))))))))

theorem step121059 (p2295 p2751 p2797 p3309 p4759 : Prop)
    (h106343 : p2751)
    (h85159 : p2797 ∨ p2295 ∨ (¬ p2751) ∨ (¬ p4759) ∨ (¬ p3309))
    : p2797 ∨ (¬ p3309) ∨ p2295 ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    (Or.elim h85159 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121062 (p2396 p2696 p3005 p3093 p3256 p3309 p3950 p4736 : Prop)
    (h105431 : p4736)
    (h85175 : (¬ p3309) ∨ (¬ p2396) ∨ (¬ p3093) ∨ p3005 ∨ p2696 ∨ p3256 ∨ (¬ p4736) ∨ (¬ p3950))
    : p3005 ∨ (¬ p3950) ∨ (¬ p3093) ∨ (¬ p3309) ∨ p3256 ∨ (¬ p2396) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h85175 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step121065 (p2177 p2449 p2685 p2696 p3093 p3309 p4666 p4736 : Prop)
    (h105431 : p4736)
    (h105658 : p4666)
    (h85191 : p2449 ∨ (¬ p3309) ∨ p2696 ∨ (¬ p4666) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p4736) ∨ p2685)
    : p2696 ∨ p2685 ∨ (¬ p3093) ∨ p2449 ∨ (¬ p2177) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4666 := h105658;
    (Or.elim h85191 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step121069 (p2307 p3309 p3361 p3367 p3983 p4749 p4869 : Prop)
    (h105432 : p4749)
    (h85201 : (¬ p3309) ∨ (¬ p4869) ∨ (¬ p3983) ∨ p2307 ∨ (¬ p3361) ∨ (¬ p4749) ∨ p3367)
    : (¬ p3361) ∨ (¬ p3983) ∨ (¬ p3309) ∨ p3367 ∨ (¬ p4869) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3361 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4749 := h105432;
    (Or.elim h85201 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (u3 r5)))))))))))))))

theorem step121071 (p2132 p3093 p3105 p3276 p3309 p3791 p4736 p4826 p4952 : Prop)
    (h105431 : p4736)
    (h105444 : p4826)
    (h85213 : (¬ p3791) ∨ p3276 ∨ p3105 ∨ (¬ p4952) ∨ p2132 ∨ (¬ p3309) ∨ (¬ p4826) ∨ (¬ p4736) ∨ (¬ p3093))
    : (¬ p3791) ∨ p3105 ∨ p2132 ∨ p3276 ∨ (¬ p3309) ∨ (¬ p4952) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4826 := h105444;
    (Or.elim h85213 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step121073 (p2295 p2727 p3309 p4759 p4975 : Prop)
    (h105464 : p4975)
    (h85224 : (¬ p3309) ∨ p2727 ∨ p2295 ∨ (¬ p4975) ∨ (¬ p4759))
    : p2727 ∨ (¬ p3309) ∨ p2295 ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4975 := h105464;
    (Or.elim h85224 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121076 (p2307 p2386 p2406 p2505 p3309 p4717 : Prop)
    (h105424 : p4717)
    (h85232 : (¬ p3309) ∨ p2307 ∨ p2406 ∨ (¬ p4717) ∨ (¬ p2386) ∨ (¬ p2505))
    : (¬ p3309) ∨ p2406 ∨ p2307 ∨ (¬ p2386) ∨ (¬ p2505) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2406) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4717 := h105424;
    (Or.elim h85232 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step121078 (p2307 p2373 p2598 p2850 p3309 p3923 p4433 p4733 p5015 : Prop)
    (h105430 : p4733)
    (h106150 : p4433)
    (h85245 : (¬ p3309) ∨ (¬ p2850) ∨ (¬ p4433) ∨ (¬ p2598) ∨ (¬ p3923) ∨ (¬ p4733) ∨ p2307 ∨ (¬ p2373) ∨ (¬ p5015))
    : (¬ p2598) ∨ (¬ p5015) ∨ (¬ p3309) ∨ (¬ p2373) ∨ p2307 ∨ (¬ p3923) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    let u8 : p4433 := h106150;
    (Or.elim h85245 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step121079 (p2254 p2396 p2528 p2651 p3083 p3093 p3309 p3950 : Prop)
    (h105366 : p2254)
    (h85255 : (¬ p3309) ∨ (¬ p3950) ∨ p2651 ∨ (¬ p3093) ∨ p3083 ∨ p2528 ∨ (¬ p2254) ∨ (¬ p2396))
    : (¬ p3309) ∨ (¬ p3093) ∨ p3083 ∨ p2651 ∨ p2528 ∨ (¬ p2396) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h85255 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step121082 (p2088 p2177 p2255 p2331 p2474 p2528 p2662 p2727 p3309 p4319 p4438 : Prop)
    (h105367 : p2255)
    (h85261 : (¬ p3309) ∨ (¬ p4319) ∨ (¬ p2528) ∨ (¬ p2255) ∨ p2727 ∨ (¬ p4438) ∨ (¬ p2474) ∨ (¬ p2177) ∨ p2088 ∨ (¬ p2662) ∨ (¬ p2331))
    : (¬ p2474) ∨ (¬ p4319) ∨ (¬ p4438) ∨ (¬ p2528) ∨ p2727 ∨ p2088 ∨ (¬ p2662) ∨ (¬ p2331) ∨ (¬ p3309) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2474 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2255 := h105367;
    (Or.elim h85261 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step121087 (p2307 p2608 p3309 p4866 p5015 : Prop)
    (h106063 : p4866)
    (h85272 : (¬ p3309) ∨ (¬ p5015) ∨ (¬ p4866) ∨ (¬ p2608) ∨ p2307)
    : (¬ p3309) ∨ (¬ p2608) ∨ p2307 ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4866 := h106063;
    (Or.elim h85272 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step121088 (p2177 p2254 p3093 p3146 p3166 p3256 p3309 p4905 : Prop)
    (h105366 : p2254)
    (h105995 : p4905)
    (h85276 : p3166 ∨ p3256 ∨ (¬ p4905) ∨ (¬ p2177) ∨ (¬ p3146) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p2254))
    : p3256 ∨ (¬ p3309) ∨ p3166 ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4905 := h105995;
    (Or.elim h85276 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step121094 (p2264 p2312 p2341 p3309 p4067 p4761 : Prop)
    (h106234 : p4761)
    (h85298 : (¬ p2341) ∨ (¬ p3309) ∨ (¬ p4761) ∨ p2264 ∨ (¬ p4067) ∨ (¬ p2312))
    : (¬ p2312) ∨ (¬ p3309) ∨ (¬ p2341) ∨ (¬ p4067) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2312 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4761 := h106234;
    (Or.elim h85298 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step121095 (p2274 p2331 p2630 p2797 p3093 p3309 p3366 p3379 p4236 p4376 : Prop)
    (h106320 : p4376)
    (h85300 : (¬ p3309) ∨ (¬ p2797) ∨ (¬ p3366) ∨ p2630 ∨ p3379 ∨ p2331 ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p3093) ∨ p2274)
    : (¬ p4236) ∨ p2331 ∨ (¬ p3093) ∨ p2274 ∨ (¬ p2797) ∨ p2630 ∨ p3379 ∨ (¬ p3309) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h85300 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (u3 r8)))))))))))))))))))))

theorem step121096 (p2177 p2230 p2850 p3093 p3309 p3641 p4438 p5193 : Prop)
    (h105488 : p5193)
    (h85306 : (¬ p3309) ∨ (¬ p2177) ∨ (¬ p5193) ∨ (¬ p2850) ∨ (¬ p3093) ∨ (¬ p4438) ∨ p2230 ∨ p3641)
    : p3641 ∨ (¬ p2850) ∨ (¬ p3309) ∨ (¬ p3093) ∨ (¬ p2177) ∨ p2230 ∨ (¬ p4438) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h85306 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step121097 (p2321 p2341 p3309 p3923 p4138 : Prop)
    (h105369 : p2321)
    (h48375 : (¬ p2321) ∨ (¬ p2341) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4138))
    : (¬ p4138) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2321 := h105369;
    (Or.elim h48375 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step121099 (p2177 p2255 p2331 p2957 p2992 p3051 p3246 p3309 p4319 p4666 : Prop)
    (h105367 : p2255)
    (h105658 : p4666)
    (h85310 : (¬ p3309) ∨ (¬ p2331) ∨ (¬ p4666) ∨ p3246 ∨ (¬ p2177) ∨ p3051 ∨ (¬ p2957) ∨ (¬ p2255) ∨ p2992 ∨ (¬ p4319))
    : (¬ p2957) ∨ p3051 ∨ (¬ p3309) ∨ (¬ p4319) ∨ (¬ p2177) ∨ (¬ p2331) ∨ p2992 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2255 := h105367;
    let u9 : p4666 := h105658;
    (Or.elim h85310 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u6 q8))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step121100 (p2881 p3309 p3923 p3960 p4113 p4559 : Prop)
    (h105701 : p4559)
    (h41876 : (¬ p2881) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p3960) ∨ (¬ p4113) ∨ (¬ p4559))
    : (¬ p3923) ∨ (¬ p3309) ∨ (¬ p2881) ∨ (¬ p4113) ∨ (¬ p3960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3923 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4559 := h105701;
    (Or.elim h41876 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121101 (p2396 p2528 p2598 p3093 p3309 p3641 p3950 p4736 : Prop)
    (h105431 : p4736)
    (h85316 : p2528 ∨ (¬ p3309) ∨ p3641 ∨ (¬ p3950) ∨ (¬ p3093) ∨ (¬ p4736) ∨ p2598 ∨ (¬ p2396))
    : p3641 ∨ p2598 ∨ p2528 ∨ (¬ p2396) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h85316 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step121103 (p2685 p2807 p3005 p3093 p3309 p3366 p3379 p4236 p4376 p4769 : Prop)
    (h106320 : p4376)
    (h85327 : p3005 ∨ p3379 ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p2685) ∨ p2807 ∨ (¬ p4376) ∨ (¬ p4236) ∨ (¬ p4769))
    : p3005 ∨ (¬ p2685) ∨ (¬ p3366) ∨ (¬ p3093) ∨ (¬ p4769) ∨ (¬ p3309) ∨ p2807 ∨ (¬ p4236) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h85327 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step121105 (p2307 p2386 p2505 p3016 p3309 p4814 : Prop)
    (h105440 : p4814)
    (h85328 : (¬ p3309) ∨ p3016 ∨ p2307 ∨ (¬ p2386) ∨ (¬ p4814) ∨ (¬ p2505))
    : (¬ p2386) ∨ (¬ p3309) ∨ p2307 ∨ (¬ p2505) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2386 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4814 := h105440;
    (Or.elim h85328 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step121106 (p2255 p2331 p2662 p2727 p3276 p3309 p3346 p3791 p4319 p4826 : Prop)
    (h105367 : p2255)
    (h105444 : p4826)
    (h85331 : (¬ p3791) ∨ (¬ p4319) ∨ (¬ p3309) ∨ (¬ p4826) ∨ p3276 ∨ (¬ p2255) ∨ (¬ p2331) ∨ p2727 ∨ (¬ p3346) ∨ (¬ p2662))
    : (¬ p3791) ∨ (¬ p3346) ∨ p2727 ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3309) ∨ p3276 ∨ (¬ p4319) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2255 := h105367;
    let u9 : p4826 := h105444;
    (Or.elim h85331 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step121110 (p2396 p2598 p2911 p3093 p3201 p3309 p4668 p4736 : Prop)
    (h105431 : p4736)
    (h105414 : p4668)
    (h85345 : (¬ p3309) ∨ (¬ p2396) ∨ (¬ p4736) ∨ p2911 ∨ (¬ p4668) ∨ p3201 ∨ (¬ p3093) ∨ p2598)
    : p2598 ∨ p3201 ∨ (¬ p2396) ∨ (¬ p3309) ∨ (¬ p3093) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2598) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4668 := h105414;
    (Or.elim h85345 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step121111 (p2396 p2598 p2850 p2982 p3093 p3309 p3951 p4736 : Prop)
    (h105431 : p4736)
    (h106536 : p3951)
    (h85346 : (¬ p3309) ∨ (¬ p2396) ∨ (¬ p3951) ∨ (¬ p4736) ∨ p2982 ∨ p2850 ∨ p2598 ∨ (¬ p3093))
    : p2598 ∨ (¬ p3309) ∨ p2850 ∨ (¬ p3093) ∨ p2982 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2598) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p3951 := h106536;
    (Or.elim h85346 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step121112 (p2383 p2427 p2598 p2850 p3309 p3923 p4559 p4736 p5020 : Prop)
    (h105431 : p4736)
    (h105701 : p4559)
    (h85348 : (¬ p3309) ∨ (¬ p2383) ∨ (¬ p4559) ∨ p2598 ∨ p2427 ∨ (¬ p3923) ∨ p2850 ∨ (¬ p4736) ∨ (¬ p5020))
    : (¬ p3923) ∨ (¬ p3309) ∨ (¬ p2383) ∨ p2598 ∨ p2850 ∨ p2427 ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3923 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4559 := h105701;
    (Or.elim h85348 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step121113 (p2177 p2417 p2598 p3093 p3201 p3309 p4666 p4736 : Prop)
    (h105431 : p4736)
    (h105658 : p4666)
    (h85349 : (¬ p3309) ∨ p2417 ∨ (¬ p4736) ∨ (¬ p4666) ∨ p3201 ∨ (¬ p2177) ∨ (¬ p3093) ∨ p2598)
    : p3201 ∨ p2417 ∨ p2598 ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4666 := h105658;
    (Or.elim h85349 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (u2 r6)))))))))))))))))

theorem step121118 (p2098 p2177 p2528 p3093 p3309 p3609 p4438 p4736 : Prop)
    (h105431 : p4736)
    (h85361 : (¬ p3309) ∨ (¬ p3093) ∨ (¬ p2528) ∨ (¬ p2177) ∨ (¬ p4736) ∨ p2098 ∨ (¬ p4438) ∨ p3609)
    : p2098 ∨ p3609 ∨ (¬ p2528) ∨ (¬ p3093) ∨ (¬ p2177) ∨ (¬ p3309) ∨ (¬ p4438) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h85361 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step121119 (p2307 p2505 p2608 p3309 p4376 p5015 : Prop)
    (h106320 : p4376)
    (h85366 : (¬ p3309) ∨ (¬ p5015) ∨ (¬ p2505) ∨ (¬ p2608) ∨ (¬ p4376) ∨ p2307)
    : (¬ p5015) ∨ (¬ p2608) ∨ (¬ p2505) ∨ p2307 ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5015 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4376 := h106320;
    (Or.elim h85366 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step121120 (p2156 p2553 p3051 p3958 p4140 : Prop)
    (h105378 : p3958)
    (h85385 : (¬ p3051) ∨ (¬ p4140) ∨ p2553 ∨ p2156 ∨ (¬ p3958))
    : (¬ p3051) ∨ p2156 ∨ p2553 ∨ (¬ p4140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3958 := h105378;
    (Or.elim h85385 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121121 (p2156 p2264 p2274 p2396 p2608 p3037 p3399 p3645 p4666 p4877 : Prop)
    (h105658 : p4666)
    (h105451 : p4877)
    (h85388 : p2608 ∨ p2396 ∨ (¬ p3645) ∨ p2274 ∨ p2156 ∨ (¬ p4877) ∨ (¬ p3399) ∨ (¬ p4666) ∨ (¬ p3037) ∨ (¬ p2264))
    : (¬ p3645) ∨ p2156 ∨ p2608 ∨ p2396 ∨ (¬ p3037) ∨ p2274 ∨ (¬ p3399) ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3645 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4666 := h105658;
    let u9 : p4877 := h105451;
    (Or.elim h85388 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step121122 (p2156 p3246 p3516 p4558 p4988 : Prop)
    (h105400 : p4558)
    (h85390 : (¬ p3516) ∨ p3246 ∨ (¬ p4558) ∨ (¬ p4988) ∨ p2156)
    : (¬ p4988) ∨ p2156 ∨ p3246 ∨ (¬ p3516) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4988 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h85390 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step121123 (p2156 p2220 p2553 p3958 p4119 p4140 : Prop)
    (h105378 : p3958)
    (h85394 : (¬ p4140) ∨ p2553 ∨ (¬ p2220) ∨ p2156 ∨ (¬ p4119) ∨ (¬ p3958))
    : (¬ p4119) ∨ (¬ p4140) ∨ p2553 ∨ (¬ p2220) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4119 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3958 := h105378;
    (Or.elim h85394 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121127 (p2156 p2187 p2352 p3660 p4533 : Prop)
    (h105394 : p4533)
    (h85406 : (¬ p2352) ∨ p2156 ∨ p2187 ∨ (¬ p4533) ∨ (¬ p3660))
    : (¬ p2352) ∨ p2156 ∨ (¬ p3660) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4533 := h105394;
    (Or.elim h85406 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121132 (p2156 p2274 p3212 p4624 p5045 : Prop)
    (h105408 : p4624)
    (h85438 : (¬ p3212) ∨ (¬ p5045) ∨ p2274 ∨ p2156 ∨ (¬ p4624))
    : (¬ p5045) ∨ (¬ p3212) ∨ p2274 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5045 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    (Or.elim h85438 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121133 (p2156 p2220 p2284 p2373 p4705 : Prop)
    (h106238 : p4705)
    (h85443 : (¬ p2220) ∨ p2156 ∨ p2373 ∨ (¬ p2284) ∨ (¬ p4705))
    : (¬ p2220) ∨ p2156 ∨ p2373 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4705 := h106238;
    (Or.elim h85443 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121136 (p2156 p2563 p3389 p3904 p4646 : Prop)
    (h105534 : p4646)
    (h85449 : (¬ p3389) ∨ p2156 ∨ (¬ p2563) ∨ (¬ p4646) ∨ (¬ p3904))
    : p2156 ∨ (¬ p3904) ∨ (¬ p3389) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4646 := h105534;
    (Or.elim h85449 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121139 (p2156 p2341 p2881 p4558 p4988 : Prop)
    (h105400 : p4558)
    (h85470 : (¬ p4988) ∨ (¬ p2341) ∨ (¬ p4558) ∨ p2881 ∨ p2156)
    : (¬ p4988) ∨ p2156 ∨ p2881 ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4988 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h85470 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step121145 (p2098 p2156 p2252 p2598 p2748 p2950 p3125 p3461 p4019 p4749 p5119 : Prop)
    (h105432 : p4749)
    (h85504 : (¬ p4019) ∨ p3461 ∨ p3125 ∨ (¬ p2098) ∨ (¬ p2748) ∨ (¬ p2252) ∨ (¬ p2950) ∨ (¬ p5119) ∨ p2156 ∨ p2598 ∨ (¬ p4749))
    : (¬ p4019) ∨ (¬ p2098) ∨ (¬ p2950) ∨ p3461 ∨ p2598 ∨ (¬ p2252) ∨ (¬ p2748) ∨ p2156 ∨ p3125 ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4749 := h105432;
    (Or.elim h85504 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u4 q9))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step121147 (p2156 p2254 p2284 p2901 p2911 p2950 p3399 p3527 p4277 : Prop)
    (h105366 : p2254)
    (h105380 : p4277)
    (h85516 : (¬ p2284) ∨ p2901 ∨ (¬ p3527) ∨ (¬ p2950) ∨ p2156 ∨ (¬ p2254) ∨ p2911 ∨ (¬ p3399) ∨ (¬ p4277))
    : (¬ p2950) ∨ p2156 ∨ p2901 ∨ (¬ p3527) ∨ (¬ p3399) ∨ p2911 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2950 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p4277 := h105380;
    (Or.elim h85516 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step121148 (p2156 p2254 p2284 p2608 p2707 p2717 p2950 p3156 p4905 : Prop)
    (h105366 : p2254)
    (h105995 : p4905)
    (h85517 : (¬ p2284) ∨ (¬ p2707) ∨ p2156 ∨ p3156 ∨ (¬ p2608) ∨ (¬ p2254) ∨ (¬ p2950) ∨ (¬ p2717) ∨ (¬ p4905))
    : (¬ p2707) ∨ p2156 ∨ (¬ p2608) ∨ (¬ p2284) ∨ (¬ p2717) ∨ p3156 ∨ (¬ p2950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p4905 := h105995;
    (Or.elim h85517 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step121149 (p2156 p2284 p2807 p2950 p3413 p4652 : Prop)
    (h105413 : p4652)
    (h85518 : (¬ p2284) ∨ (¬ p2950) ∨ (¬ p4652) ∨ (¬ p3413) ∨ p2156 ∨ (¬ p2807))
    : (¬ p2950) ∨ p2156 ∨ (¬ p2807) ∨ (¬ p3413) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2950 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4652 := h105413;
    (Or.elim h85518 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step121152 (p2156 p2284 p2440 p2573 p2659 p2911 p3016 p3413 p3872 p4705 : Prop)
    (h106238 : p4705)
    (h85525 : (¬ p3872) ∨ (¬ p3413) ∨ p2573 ∨ (¬ p2284) ∨ (¬ p4705) ∨ p2440 ∨ (¬ p3016) ∨ (¬ p2911) ∨ (¬ p2659) ∨ p2156)
    : p2573 ∨ (¬ p3413) ∨ (¬ p2284) ∨ (¬ p2911) ∨ p2440 ∨ (¬ p3016) ∨ p2156 ∨ (¬ p3872) ∨ (¬ p2659) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4705 := h106238;
    (Or.elim h85525 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (u6 r8)))))))))))))))))))))

theorem step121158 (p2145 p2156 p2284 p2761 p3115 p3276 p3355 p3362 p3951 : Prop)
    (h106536 : p3951)
    (h85553 : p2761 ∨ (¬ p3276) ∨ (¬ p3951) ∨ (¬ p2145) ∨ (¬ p3362) ∨ p2156 ∨ p3115 ∨ (¬ p2284) ∨ (¬ p3355))
    : (¬ p3276) ∨ (¬ p3355) ∨ p3115 ∨ p2761 ∨ (¬ p3362) ∨ p2156 ∨ (¬ p2284) ∨ (¬ p2145) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3951 := h106536;
    (Or.elim h85553 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step121161 (p2156 p2264 p2341 p4333 p4558 p4988 : Prop)
    (h105400 : p4558)
    (h85569 : (¬ p2341) ∨ (¬ p4333) ∨ p2264 ∨ (¬ p4988) ∨ p2156 ∨ (¬ p4558))
    : (¬ p2341) ∨ (¬ p4988) ∨ p2264 ∨ (¬ p4333) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    (Or.elim h85569 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121165 (p2156 p2274 p2396 p2911 p2922 p3379 p4666 : Prop)
    (h105658 : p4666)
    (h85573 : p2396 ∨ p2274 ∨ (¬ p4666) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p2911) ∨ p2156)
    : p2156 ∨ (¬ p3379) ∨ p2396 ∨ (¬ p2922) ∨ (¬ p2911) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4666 := h105658;
    (Or.elim h85573 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (u0 r5)))))))))))))))

theorem step121169 (p2177 p2274 p2341 p3546 p3922 p4105 p4564 : Prop)
    (h105401 : p4564)
    (h85587 : p2341 ∨ (¬ p2274) ∨ (¬ p3546) ∨ (¬ p4105) ∨ (¬ p3922) ∨ (¬ p4564) ∨ (¬ p2177))
    : (¬ p3922) ∨ p2341 ∨ (¬ p2274) ∨ (¬ p3546) ∨ (¬ p4105) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4564 := h105401;
    (Or.elim h85587 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step121178 (p2145 p2753 p3645 p4877 : Prop)
    (h105451 : p4877)
    (h23731 : p2145 ∨ (¬ p2753) ∨ (¬ p3645) ∨ (¬ p4877))
    : p2145 ∨ (¬ p2753) ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2145) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4877 := h105451;
    (Or.elim h23731 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step121183 (p2383 p2584 p2668 p2761 p3323 p3519 p3645 p4032 p4322 p4376 p4621 p4874 : Prop)
    (h106320 : p4376)
    (h105407 : p4621)
    (h85643 : (¬ p4322) ∨ (¬ p2383) ∨ p2668 ∨ (¬ p4032) ∨ (¬ p2761) ∨ (¬ p3519) ∨ (¬ p3323) ∨ (¬ p4621) ∨ (¬ p3645) ∨ (¬ p4376) ∨ (¬ p2584) ∨ (¬ p4874))
    : p2668 ∨ (¬ p3323) ∨ (¬ p4032) ∨ (¬ p2383) ∨ (¬ p4322) ∨ (¬ p2761) ∨ (¬ p2584) ∨ (¬ p3519) ∨ (¬ p3645) ∨ (¬ p4874) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2668) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4376 := h106320;
    let u11 : p4621 := h105407;
    (Or.elim h85643 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u6))) (fun r10 => (False.elim (r10 u9)))))))))))))))))))))))))

theorem step121186 (p2156 p2187 p2246 p2651 p2749 p3276 p3333 p3645 p4343 p4877 p5123 p5580 : Prop)
    (h105451 : p4877)
    (h85660 : (¬ p5580) ∨ (¬ p5123) ∨ (¬ p3645) ∨ p2156 ∨ (¬ p2246) ∨ (¬ p4877) ∨ (¬ p3333) ∨ p2187 ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p4343) ∨ (¬ p3276))
    : (¬ p2749) ∨ p2156 ∨ (¬ p2651) ∨ (¬ p4343) ∨ (¬ p3276) ∨ (¬ p3333) ∨ p2187 ∨ (¬ p5580) ∨ (¬ p2246) ∨ (¬ p3645) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2749 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4877 := h105451;
    (Or.elim h85660 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u3))) (fun r10 => (False.elim (r10 u4)))))))))))))))))))))))))

theorem step121197 (p2132 p2493 p2509 p2573 p2870 p2881 p4108 p4438 p4733 : Prop)
    (h105430 : p4733)
    (h85722 : (¬ p2870) ∨ (¬ p2881) ∨ p2573 ∨ (¬ p2132) ∨ (¬ p4438) ∨ (¬ p2493) ∨ (¬ p4733) ∨ (¬ p4108) ∨ (¬ p2509))
    : (¬ p2509) ∨ (¬ p2132) ∨ (¬ p2493) ∨ (¬ p4438) ∨ (¬ p2881) ∨ (¬ p2870) ∨ (¬ p4108) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4733 := h105430;
    (Or.elim h85722 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step121198 (p2132 p2406 p2493 p2573 p2870 p2901 p3115 p4108 p4733 : Prop)
    (h105430 : p4733)
    (h85723 : (¬ p2870) ∨ p2901 ∨ p2573 ∨ (¬ p4108) ∨ (¬ p4733) ∨ (¬ p2132) ∨ (¬ p2493) ∨ p2406 ∨ (¬ p3115))
    : (¬ p3115) ∨ p2901 ∨ (¬ p2493) ∨ (¬ p4108) ∨ p2573 ∨ p2406 ∨ (¬ p2132) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4733 := h105430;
    (Or.elim h85723 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step121203 (p2331 p2493 p2651 p4389 p4814 : Prop)
    (h105440 : p4814)
    (h85739 : p2331 ∨ (¬ p4389) ∨ (¬ p4814) ∨ (¬ p2651) ∨ (¬ p2493))
    : p2331 ∨ (¬ p2493) ∨ (¬ p2651) ∨ (¬ p4389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4814 := h105440;
    (Or.elim h85739 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121206 (p2255 p2352 p2493 p2651 p2881 p2957 p2992 p3051 p4116 p4133 : Prop)
    (h105367 : p2255)
    (h105712 : p4133)
    (h85744 : (¬ p2493) ∨ (¬ p2651) ∨ (¬ p4116) ∨ p2881 ∨ (¬ p4133) ∨ (¬ p2255) ∨ (¬ p2957) ∨ (¬ p2352) ∨ p3051 ∨ p2992)
    : p2992 ∨ (¬ p2352) ∨ (¬ p2957) ∨ p3051 ∨ (¬ p2651) ∨ p2881 ∨ (¬ p4116) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2255 := h105367;
    let u9 : p4133 := h105712;
    (Or.elim h85744 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (False.elim (u0 r8)))))))))))))))))))))

theorem step121207 (p2254 p2352 p2459 p2493 p3166 p3256 p3379 p4133 : Prop)
    (h105366 : p2254)
    (h105712 : p4133)
    (h85747 : (¬ p2493) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p4133) ∨ p3256 ∨ p3166 ∨ (¬ p2254))
    : p3166 ∨ (¬ p3379) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2493) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4133 := h105712;
    (Or.elim h85747 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step121210 (p2254 p2352 p2493 p2881 p2901 p2946 p3379 p4133 : Prop)
    (h105366 : p2254)
    (h105712 : p4133)
    (h85752 : (¬ p2493) ∨ p2901 ∨ (¬ p2254) ∨ (¬ p4133) ∨ (¬ p2352) ∨ (¬ p3379) ∨ p2881 ∨ p2946)
    : p2901 ∨ p2946 ∨ (¬ p3379) ∨ (¬ p2352) ∨ (¬ p2493) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4133 := h105712;
    (Or.elim h85752 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step121211 (p2220 p2352 p2459 p2493 p3146 p3379 p4133 : Prop)
    (h105712 : p4133)
    (h85755 : (¬ p2493) ∨ (¬ p2352) ∨ (¬ p2459) ∨ p3146 ∨ (¬ p4133) ∨ p2220 ∨ (¬ p3379))
    : p2220 ∨ (¬ p3379) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2459) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4133 := h105712;
    (Or.elim h85755 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step121212 (p2254 p2352 p2459 p2493 p2807 p3256 p3379 p3919 p4133 : Prop)
    (h105366 : p2254)
    (h105712 : p4133)
    (h85757 : p2807 ∨ (¬ p2352) ∨ (¬ p4133) ∨ (¬ p2459) ∨ (¬ p2493) ∨ p3256 ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p3919))
    : (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3919) ∨ (¬ p2352) ∨ p3256 ∨ p2807 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p4133 := h105712;
    (Or.elim h85757 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step121213 (p2352 p2493 p2668 p4194 p4814 : Prop)
    (h105440 : p4814)
    (h85759 : (¬ p2493) ∨ (¬ p2352) ∨ (¬ p4814) ∨ p2668 ∨ (¬ p4194))
    : (¬ p4194) ∨ (¬ p2352) ∨ p2668 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4194 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4814 := h105440;
    (Or.elim h85759 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step121214 (p2254 p2493 p2946 p3146 p3156 p3379 p3564 p4330 : Prop)
    (h105366 : p2254)
    (h106329 : p4330)
    (h85763 : (¬ p3564) ∨ p3146 ∨ (¬ p2493) ∨ (¬ p3379) ∨ p2946 ∨ (¬ p2254) ∨ p3156 ∨ (¬ p4330))
    : p3156 ∨ (¬ p3564) ∨ (¬ p3379) ∨ p3146 ∨ p2946 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4330 := h106329;
    (Or.elim h85763 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121215 (p2493 p2651 p2946 p3879 p4116 p4717 : Prop)
    (h105424 : p4717)
    (h85767 : p2946 ∨ (¬ p4116) ∨ (¬ p2651) ∨ (¬ p4717) ∨ (¬ p3879) ∨ (¬ p2493))
    : p2946 ∨ (¬ p4116) ∨ (¬ p2651) ∨ (¬ p3879) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4717 := h105424;
    (Or.elim h85767 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step121218 (p2210 p2493 p3379 p4034 p4717 : Prop)
    (h105424 : p4717)
    (h85780 : p2210 ∨ (¬ p3379) ∨ (¬ p2493) ∨ (¬ p4717) ∨ (¬ p4034))
    : p2210 ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p4034) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4717 := h105424;
    (Or.elim h85780 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121221 (p2156 p2406 p2493 p4203 p4533 : Prop)
    (h105394 : p4533)
    (h85790 : p2156 ∨ (¬ p4203) ∨ p2406 ∨ (¬ p2493) ∨ (¬ p4533))
    : p2156 ∨ (¬ p2493) ∨ (¬ p4203) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4533 := h105394;
    (Or.elim h85790 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121222 (p2284 p2406 p2493 p4203 p4702 : Prop)
    (h106079 : p4702)
    (h85791 : (¬ p4702) ∨ p2284 ∨ p2406 ∨ (¬ p2493) ∨ (¬ p4203))
    : p2284 ∨ (¬ p2493) ∨ (¬ p4203) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4702 := h106079;
    (Or.elim h85791 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121223 (p2341 p2493 p2926 p3527 p3575 p3741 p4717 : Prop)
    (h105424 : p4717)
    (h85802 : p3527 ∨ (¬ p2341) ∨ (¬ p3741) ∨ (¬ p2493) ∨ (¬ p2926) ∨ (¬ p3575) ∨ (¬ p4717))
    : (¬ p3575) ∨ (¬ p2341) ∨ (¬ p2926) ∨ (¬ p2493) ∨ p3527 ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3575 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2926 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4717 := h105424;
    (Or.elim h85802 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step121224 (p2417 p2493 p2926 p3631 p3741 p4717 : Prop)
    (h105424 : p4717)
    (h85803 : p3631 ∨ (¬ p2926) ∨ (¬ p2417) ∨ (¬ p2493) ∨ (¬ p3741) ∨ (¬ p4717))
    : (¬ p2926) ∨ (¬ p2417) ∨ (¬ p3741) ∨ p3631 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2926 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4717 := h105424;
    (Or.elim h85803 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121225 (p2187 p2254 p2284 p2493 p2553 p2946 p3379 : Prop)
    (h105366 : p2254)
    (h85804 : (¬ p2553) ∨ p2946 ∨ (¬ p2254) ∨ p2284 ∨ p2187 ∨ (¬ p3379) ∨ (¬ p2493))
    : p2284 ∨ p2946 ∨ (¬ p2553) ∨ p2187 ∨ (¬ p2493) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    (Or.elim h85804 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step121226 (p2406 p2427 p2493 p4203 p4555 : Prop)
    (h105542 : p4555)
    (h85808 : p2427 ∨ (¬ p4555) ∨ (¬ p2493) ∨ (¬ p4203) ∨ p2406)
    : p2406 ∨ p2427 ∨ (¬ p2493) ∨ (¬ p4203) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    (Or.elim h85808 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step121227 (p2274 p2312 p2493 p2922 p3958 p4279 : Prop)
    (h105378 : p3958)
    (h85810 : (¬ p2312) ∨ (¬ p2274) ∨ (¬ p3958) ∨ (¬ p2493) ∨ p2922 ∨ (¬ p4279))
    : p2922 ∨ (¬ p4279) ∨ (¬ p2312) ∨ (¬ p2274) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3958 := h105378;
    (Or.elim h85810 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step121234 (p2245 p2608 p2744 p2946 p2992 : Prop)
    (h106503 : p2744)
    (h85846 : (¬ p2992) ∨ p2946 ∨ (¬ p2744) ∨ (¬ p2245) ∨ (¬ p2608))
    : p2946 ∨ (¬ p2992) ∨ (¬ p2608) ∨ (¬ p2245) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2744 := h106503;
    (Or.elim h85846 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121235 (p2727 p2807 p2946 p2992 p4652 : Prop)
    (h105413 : p4652)
    (h85850 : p2727 ∨ (¬ p2992) ∨ p2946 ∨ (¬ p2807) ∨ (¬ p4652))
    : p2946 ∨ (¬ p2992) ∨ p2727 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4652 := h105413;
    (Or.elim h85850 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121237 (p2727 p2850 p2992 p4241 p4750 : Prop)
    (h105433 : p4750)
    (h85860 : p2727 ∨ (¬ p2992) ∨ p2850 ∨ (¬ p4241) ∨ (¬ p4750))
    : p2850 ∨ (¬ p2992) ∨ p2727 ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    (Or.elim h85860 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121238 (p2440 p2493 p2727 p2992 p4715 : Prop)
    (h105423 : p4715)
    (h85863 : (¬ p2992) ∨ p2727 ∨ p2493 ∨ (¬ p4715) ∨ p2440)
    : p2493 ∨ (¬ p2992) ∨ p2440 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    (Or.elim h85863 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step121239 (p2727 p2992 p3016 p4241 p4715 : Prop)
    (h105423 : p4715)
    (h85864 : p2727 ∨ (¬ p2992) ∨ p3016 ∨ (¬ p4241) ∨ (¬ p4715))
    : p3016 ∨ (¬ p2992) ∨ p2727 ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    (Or.elim h85864 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121245 (p2437 p2727 p2992 p4241 p4644 : Prop)
    (h105411 : p4644)
    (h85890 : p2727 ∨ (¬ p2992) ∨ (¬ p4241) ∨ (¬ p4644) ∨ p2437)
    : p2727 ∨ p2437 ∨ (¬ p2992) ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4644 := h105411;
    (Or.elim h85890 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step121246 (p2727 p2992 p3083 p4241 p4608 : Prop)
    (h105540 : p4608)
    (h85892 : p2727 ∨ (¬ p2992) ∨ (¬ p4608) ∨ (¬ p4241) ∨ p3083)
    : p3083 ∨ (¬ p2992) ∨ p2727 ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4608 := h105540;
    (Or.elim h85892 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step121248 (p2241 p2352 p2363 p2573 p2992 p3115 p4450 p5193 : Prop)
    (h105488 : p5193)
    (h85903 : (¬ p3115) ∨ (¬ p2992) ∨ (¬ p2241) ∨ (¬ p5193) ∨ p2363 ∨ (¬ p4450) ∨ p2352 ∨ p2573)
    : (¬ p2992) ∨ (¬ p2241) ∨ p2352 ∨ (¬ p4450) ∨ p2573 ∨ (¬ p3115) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h85903 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step121249 (p2563 p2641 p2992 p4702 : Prop)
    (h106079 : p4702)
    (h85906 : p2641 ∨ (¬ p2992) ∨ (¬ p4702) ∨ (¬ p2563))
    : (¬ p2992) ∨ p2641 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4702 := h106079;
    (Or.elim h85906 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step121257 (p2641 p2992 p3156 p3745 p4509 : Prop)
    (h105392 : p4509)
    (h85939 : p2641 ∨ (¬ p2992) ∨ (¬ p4509) ∨ (¬ p3745) ∨ (¬ p3156))
    : (¬ p3745) ∨ p2641 ∨ (¬ p3156) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3745 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4509 := h105392;
    (Or.elim h85939 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121259 (p2641 p2901 p2992 p3745 p4558 : Prop)
    (h105400 : p4558)
    (h85941 : p2641 ∨ (¬ p2992) ∨ (¬ p2901) ∨ (¬ p4558) ∨ (¬ p3745))
    : p2641 ∨ (¬ p2992) ∨ (¬ p2901) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h85941 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121260 (p2742 p2797 p2901 p2992 p3745 p4558 : Prop)
    (h105400 : p4558)
    (h85943 : p2797 ∨ (¬ p2742) ∨ (¬ p4558) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3745))
    : p2797 ∨ (¬ p2742) ∨ (¬ p2901) ∨ (¬ p3745) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    (Or.elim h85943 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step121261 (p2960 p2992 p2996 p3051 p3699 : Prop)
    (h105377 : p2960)
    (h52228 : (¬ p2960) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3051) ∨ (¬ p3699))
    : (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3699) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2960 := h105377;
    (Or.elim h52228 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121262 (p2427 p2992 p2996 p3699 p4702 : Prop)
    (h106079 : p4702)
    (h51727 : (¬ p2427) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3699) ∨ (¬ p4702))
    : (¬ p2992) ∨ (¬ p2996) ∨ (¬ p2427) ∨ (¬ p3699) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4702 := h106079;
    (Or.elim h51727 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121266 (p2284 p2992 p2996 p3699 p4555 : Prop)
    (h105542 : p4555)
    (h54097 : (¬ p2284) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3699) ∨ (¬ p4555))
    : (¬ p2992) ∨ (¬ p3699) ∨ (¬ p2996) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    (Or.elim h54097 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121268 (p2177 p2241 p2553 p2573 p2992 p3156 p4902 p5193 : Prop)
    (h105456 : p4902)
    (h105488 : p5193)
    (h85962 : (¬ p3156) ∨ (¬ p2992) ∨ (¬ p5193) ∨ p2573 ∨ p2177 ∨ (¬ p2241) ∨ (¬ p4902) ∨ p2553)
    : (¬ p3156) ∨ (¬ p2992) ∨ p2573 ∨ (¬ p2241) ∨ p2553 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4902 := h105456;
    let u7 : p5193 := h105488;
    (Or.elim h85962 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step121270 (p2122 p2177 p2245 p2774 p2946 p2992 p3189 p4041 p4733 : Prop)
    (h105430 : p4733)
    (h85972 : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p2245) ∨ p3189 ∨ (¬ p4041) ∨ (¬ p2992) ∨ (¬ p2177) ∨ (¬ p4733) ∨ p2946)
    : p3189 ∨ (¬ p2245) ∨ p2946 ∨ (¬ p2992) ∨ (¬ p2177) ∨ (¬ p2774) ∨ (¬ p2122) ∨ (¬ p4041) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4733 := h105430;
    (Or.elim h85972 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (u2 r7)))))))))))))))))))

theorem step121272 (p2156 p2249 p2284 p2950 p2992 : Prop)
    (h106513 : p2249)
    (h85979 : (¬ p2992) ∨ (¬ p2950) ∨ (¬ p2249) ∨ (¬ p2284) ∨ p2156)
    : p2156 ∨ (¬ p2950) ∨ (¬ p2992) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2249 := h106513;
    (Or.elim h85979 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step121274 (p2245 p2331 p2608 p2641 p2744 : Prop)
    (h106503 : p2744)
    (h86002 : (¬ p2641) ∨ p2331 ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2245))
    : p2331 ∨ (¬ p2245) ∨ (¬ p2641) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2744 := h106503;
    (Or.elim h86002 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121276 (p2230 p2241 p2295 p2563 p2641 p3125 p4620 p5193 : Prop)
    (h105488 : p5193)
    (h86006 : (¬ p2641) ∨ (¬ p2295) ∨ p2563 ∨ p2230 ∨ (¬ p5193) ∨ (¬ p4620) ∨ p3125 ∨ (¬ p2241))
    : p2230 ∨ (¬ p2295) ∨ p3125 ∨ p2563 ∨ (¬ p2641) ∨ (¬ p2241) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2230) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h86006 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step121277 (p2177 p2249 p2295 p2373 p2406 p2641 p2651 p3487 p4905 : Prop)
    (h106513 : p2249)
    (h105995 : p4905)
    (h86007 : (¬ p2295) ∨ (¬ p2177) ∨ (¬ p2641) ∨ (¬ p3487) ∨ p2373 ∨ p2651 ∨ (¬ p4905) ∨ (¬ p2249) ∨ p2406)
    : (¬ p3487) ∨ p2651 ∨ p2406 ∨ (¬ p2295) ∨ (¬ p2641) ∨ p2373 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3487 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2249 := h106513;
    let u8 : p4905 := h105995;
    (Or.elim h86007 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u2 r7)))))))))))))))))))

theorem step121280 (p2641 p2992 p3115 p3986 p5043 : Prop)
    (h105471 : p5043)
    (h86016 : p2992 ∨ p3115 ∨ (¬ p2641) ∨ (¬ p5043) ∨ (¬ p3986))
    : p3115 ∨ p2992 ∨ (¬ p2641) ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5043 := h105471;
    (Or.elim h86016 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121281 (p2156 p2641 p2954 p2992 p3986 : Prop)
    (h106494 : p2954)
    (h86027 : (¬ p3986) ∨ p2992 ∨ p2156 ∨ (¬ p2954) ∨ (¬ p2641))
    : p2992 ∨ p2156 ∨ (¬ p2641) ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2954 := h106494;
    (Or.elim h86027 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121283 (p2241 p2341 p2417 p2641 p2911 p3323 p4621 p5193 p5197 : Prop)
    (h105488 : p5193)
    (h105407 : p4621)
    (h86030 : p2417 ∨ p2341 ∨ (¬ p2911) ∨ (¬ p5197) ∨ (¬ p2641) ∨ (¬ p5193) ∨ (¬ p4621) ∨ (¬ p3323) ∨ (¬ p2241))
    : p2417 ∨ (¬ p2911) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p5197) ∨ p2341 ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    let u8 : p4621 := h105407;
    (Or.elim h86030 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step121284 (p2230 p2241 p2274 p2563 p2641 p2668 p4405 p5193 : Prop)
    (h105512 : p4405)
    (h105488 : p5193)
    (h86031 : (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2241) ∨ (¬ p4405) ∨ p2274 ∨ p2563 ∨ p2230 ∨ (¬ p5193))
    : (¬ p2641) ∨ (¬ p2668) ∨ p2563 ∨ p2230 ∨ (¬ p2241) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4405 := h105512;
    let u7 : p5193 := h105488;
    (Or.elim h86031 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121285 (p2641 p2656 p2891 p3051 p3368 p4399 p4975 : Prop)
    (h105464 : p4975)
    (h86038 : (¬ p3051) ∨ (¬ p3368) ∨ (¬ p2656) ∨ (¬ p4975) ∨ (¬ p2641) ∨ p2891 ∨ (¬ p4399))
    : (¬ p3368) ∨ (¬ p3051) ∨ (¬ p4399) ∨ p2891 ∨ (¬ p2656) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3368 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4975 := h105464;
    (Or.elim h86038 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step121286 (p2341 p2459 p2641 p2696 p2707 p2742 p3323 p3959 p4330 : Prop)
    (h106329 : p4330)
    (h86043 : (¬ p3323) ∨ (¬ p2742) ∨ p2707 ∨ (¬ p3959) ∨ (¬ p4330) ∨ p2341 ∨ (¬ p2641) ∨ (¬ p2696) ∨ p2459)
    : (¬ p3959) ∨ p2707 ∨ p2459 ∨ (¬ p2641) ∨ p2341 ∨ (¬ p3323) ∨ (¬ p2742) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3959 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4330 := h106329;
    (Or.elim h86043 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u2 r7)))))))))))))))))))

theorem step121287 (p2641 p2957 p2992 p3051 p3986 p4555 : Prop)
    (h105542 : p4555)
    (h86048 : (¬ p2641) ∨ p2992 ∨ p3051 ∨ (¬ p3986) ∨ (¬ p2957) ∨ (¬ p4555))
    : (¬ p2957) ∨ p3051 ∨ p2992 ∨ (¬ p3986) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4555 := h105542;
    (Or.elim h86048 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121288 (p2563 p2641 p2992 p3986 p4705 : Prop)
    (h106238 : p4705)
    (h86050 : (¬ p2641) ∨ p2992 ∨ (¬ p4705) ∨ (¬ p3986) ∨ p2563)
    : p2992 ∨ (¬ p3986) ∨ p2563 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4705 := h106238;
    (Or.elim h86050 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step121289 (p2241 p2459 p2641 p2911 p3323 p3389 p4330 p5193 : Prop)
    (h105488 : p5193)
    (h106329 : p4330)
    (h86058 : (¬ p2641) ∨ p2911 ∨ (¬ p5193) ∨ p2459 ∨ (¬ p3323) ∨ p3389 ∨ (¬ p2241) ∨ (¬ p4330))
    : p2911 ∨ (¬ p2241) ∨ (¬ p2641) ∨ p3389 ∨ p2459 ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5193 := h105488;
    let u7 : p4330 := h106329;
    (Or.elim h86058 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121291 (p2245 p2331 p2459 p2470 p2528 p2641 p3189 p4041 p5190 : Prop)
    (h105487 : p5190)
    (h86069 : (¬ p2245) ∨ p3189 ∨ p2459 ∨ (¬ p5190) ∨ p2331 ∨ (¬ p2470) ∨ (¬ p2641) ∨ (¬ p4041) ∨ (¬ p2528))
    : p2331 ∨ p3189 ∨ (¬ p4041) ∨ (¬ p2245) ∨ p2459 ∨ (¬ p2641) ∨ (¬ p2528) ∨ (¬ p2470) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5190 := h105487;
    (Or.elim h86069 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step121292 (p2641 p2651 p3166 p3189 p4975 : Prop)
    (h105464 : p4975)
    (h86071 : (¬ p2641) ∨ (¬ p3166) ∨ p3189 ∨ (¬ p4975) ∨ p2651)
    : p3189 ∨ p2651 ∨ (¬ p2641) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4975 := h105464;
    (Or.elim h86071 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step121293 (p2563 p2641 p2992 p3567 p4356 p4705 : Prop)
    (h106238 : p4705)
    (h86072 : p2992 ∨ (¬ p3567) ∨ (¬ p2641) ∨ (¬ p4356) ∨ p2563 ∨ (¬ p4705))
    : (¬ p3567) ∨ p2992 ∨ (¬ p2641) ∨ p2563 ∨ (¬ p4356) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    (Or.elim h86072 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121294 (p2249 p2307 p2396 p2509 p2528 p2641 p2651 p3487 p3567 p3950 : Prop)
    (h106513 : p2249)
    (h86073 : (¬ p2307) ∨ (¬ p3567) ∨ (¬ p2396) ∨ (¬ p3950) ∨ (¬ p3487) ∨ p2651 ∨ (¬ p2641) ∨ (¬ p2509) ∨ (¬ p2249) ∨ p2528)
    : (¬ p2509) ∨ (¬ p3567) ∨ (¬ p3487) ∨ (¬ p2396) ∨ (¬ p2641) ∨ p2528 ∨ (¬ p2307) ∨ p2651 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2249 := h106513;
    (Or.elim h86073 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u5 r8)))))))))))))))))))))

theorem step121297 (p2230 p2406 p2641 p2656 p3402 p4975 : Prop)
    (h105464 : p4975)
    (h86077 : p2406 ∨ (¬ p3402) ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2641) ∨ (¬ p4975))
    : (¬ p2656) ∨ (¬ p2230) ∨ p2406 ∨ (¬ p3402) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2656 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4975 := h105464;
    (Or.elim h86077 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121298 (p2241 p2641 p3266 p3276 p3323 p3346 p4330 p5193 : Prop)
    (h105488 : p5193)
    (h106329 : p4330)
    (h86078 : p3276 ∨ (¬ p3323) ∨ (¬ p2641) ∨ (¬ p2241) ∨ (¬ p5193) ∨ (¬ p3266) ∨ (¬ p4330) ∨ (¬ p3346))
    : (¬ p3346) ∨ (¬ p3323) ∨ (¬ p2241) ∨ (¬ p3266) ∨ (¬ p2641) ∨ p3276 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3346 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5193 := h105488;
    let u7 : p4330 := h106329;
    (Or.elim h86078 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step121299 (p2641 p2651 p2807 p2996 p4975 : Prop)
    (h105464 : p4975)
    (h86080 : (¬ p2996) ∨ (¬ p2641) ∨ (¬ p4975) ∨ (¬ p2807) ∨ p2651)
    : (¬ p2641) ∨ (¬ p2996) ∨ p2651 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4975 := h105464;
    (Or.elim h86080 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step121303 (p2187 p2641 p3189 p4564 p4769 : Prop)
    (h105401 : p4564)
    (h86090 : (¬ p2641) ∨ p3189 ∨ (¬ p4769) ∨ (¬ p4564) ∨ (¬ p2187))
    : p3189 ∨ (¬ p2187) ∨ (¬ p4769) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4564 := h105401;
    (Or.elim h86090 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121304 (p2187 p2641 p3189 p3958 p3984 p4769 : Prop)
    (h105378 : p3958)
    (h86091 : (¬ p2641) ∨ p3189 ∨ (¬ p3984) ∨ (¬ p3958) ∨ (¬ p4769) ∨ (¬ p2187))
    : p3189 ∨ (¬ p2187) ∨ (¬ p3984) ∨ (¬ p4769) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3958 := h105378;
    (Or.elim h86091 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step121306 (p2241 p2373 p2427 p2641 p2668 p3051 p4134 : Prop)
    (h105379 : p4134)
    (h86099 : (¬ p2641) ∨ p2373 ∨ (¬ p4134) ∨ (¬ p2668) ∨ p3051 ∨ (¬ p2427) ∨ (¬ p2241))
    : p3051 ∨ p2373 ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2241) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4134 := h105379;
    (Or.elim h86099 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step121307 (p2249 p2383 p2641 p2668 p3983 : Prop)
    (h106513 : p2249)
    (h86100 : (¬ p3983) ∨ (¬ p2668) ∨ p2383 ∨ (¬ p2249) ∨ (¬ p2641))
    : (¬ p3983) ∨ p2383 ∨ (¬ p2641) ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3983 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2249 := h106513;
    (Or.elim h86100 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121308 (p2298 p2553 p2641 p2996 p4973 : Prop)
    (h105835 : p4973)
    (h49721 : (¬ p2298) ∨ (¬ p2553) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p4973))
    : (¬ p2641) ∨ (¬ p2996) ∨ (¬ p2298) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4973 := h105835;
    (Or.elim h49721 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121309 (p2298 p2641 p2996 p3323 p4624 : Prop)
    (h105408 : p4624)
    (h50118 : (¬ p2298) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3323) ∨ (¬ p4624))
    : (¬ p2641) ∨ (¬ p2996) ∨ (¬ p2298) ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    (Or.elim h50118 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121310 (p2274 p2298 p2641 p2996 p3958 p3984 : Prop)
    (h105378 : p3958)
    (h51731 : (¬ p2274) ∨ (¬ p2298) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3958) ∨ (¬ p3984))
    : (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3984) ∨ (¬ p2298) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3958 := h105378;
    (Or.elim h51731 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step121311 (p2298 p2307 p2641 p2996 p4584 : Prop)
    (h105406 : p4584)
    (h49286 : (¬ p2298) ∨ (¬ p2307) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p4584))
    : (¬ p2641) ∨ (¬ p2996) ∨ (¬ p2298) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4584 := h105406;
    (Or.elim h49286 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121312 (p2298 p2641 p2668 p2996 p4405 : Prop)
    (h105512 : p4405)
    (h42571 : (¬ p2298) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2996) ∨ (¬ p4405))
    : (¬ p2641) ∨ (¬ p2996) ∨ (¬ p2298) ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    (Or.elim h42571 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121314 (p2253 p2274 p2553 p2573 p2641 p2807 p2996 p4564 p5193 : Prop)
    (h105488 : p5193)
    (h105401 : p4564)
    (h86114 : (¬ p2641) ∨ (¬ p2274) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p5193) ∨ (¬ p2253) ∨ p2553 ∨ p2573 ∨ (¬ p4564))
    : (¬ p2996) ∨ (¬ p2641) ∨ (¬ p2807) ∨ p2553 ∨ (¬ p2274) ∨ p2573 ∨ (¬ p2253) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    let u8 : p4564 := h105401;
    (Or.elim h86114 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step121315 (p2641 p3125 p3848 p4190 p4564 : Prop)
    (h105401 : p4564)
    (h54909 : (¬ p2641) ∨ (¬ p3125) ∨ (¬ p3848) ∨ (¬ p4190) ∨ (¬ p4564))
    : (¬ p3848) ∨ (¬ p4190) ∨ (¬ p2641) ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3848 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4564 := h105401;
    (Or.elim h54909 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121316 (p2122 p2307 p2641 p2751 p3567 p4841 : Prop)
    (h106343 : p2751)
    (h86118 : (¬ p4841) ∨ p2122 ∨ (¬ p2307) ∨ (¬ p2751) ∨ (¬ p2641) ∨ (¬ p3567))
    : (¬ p3567) ∨ (¬ p4841) ∨ p2122 ∨ (¬ p2307) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    (Or.elim h86118 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step121319 (p2641 p2656 p2972 p3212 p3368 p4399 p4975 : Prop)
    (h105464 : p4975)
    (h86126 : (¬ p3368) ∨ (¬ p3212) ∨ (¬ p4399) ∨ (¬ p4975) ∨ (¬ p2656) ∨ (¬ p2641) ∨ p2972)
    : (¬ p3368) ∨ (¬ p3212) ∨ (¬ p2641) ∨ p2972 ∨ (¬ p4399) ∨ (¬ p2656) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3368 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4975 := h105464;
    (Or.elim h86126 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (u3 r5)))))))))))))))

theorem step121322 (p2241 p2295 p2427 p2598 p2641 p2850 p4559 p4736 : Prop)
    (h105431 : p4736)
    (h105701 : p4559)
    (h86146 : (¬ p2295) ∨ p2427 ∨ (¬ p4736) ∨ (¬ p2241) ∨ p2598 ∨ (¬ p4559) ∨ (¬ p2641) ∨ p2850)
    : p2598 ∨ p2850 ∨ (¬ p2295) ∨ p2427 ∨ (¬ p2641) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2598) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4559 := h105701;
    (Or.elim h86146 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step121324 (p2363 p2449 p2696 p2748 p2819 p2829 p2996 p4669 : Prop)
    (h105415 : p4669)
    (h86171 : (¬ p2829) ∨ (¬ p2819) ∨ (¬ p4669) ∨ p2696 ∨ (¬ p2996) ∨ (¬ p2748) ∨ p2449 ∨ (¬ p2363))
    : (¬ p2748) ∨ (¬ p2819) ∨ p2696 ∨ (¬ p2996) ∨ (¬ p2829) ∨ (¬ p2363) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2748 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4669 := h105415;
    (Or.elim h86171 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step121326 (p2122 p2318 p2819 p3516 p3550 p4666 : Prop)
    (h105658 : p4666)
    (h86173 : (¬ p2819) ∨ p3516 ∨ (¬ p2318) ∨ (¬ p4666) ∨ (¬ p3550) ∨ p2122)
    : (¬ p2819) ∨ (¬ p2318) ∨ p3516 ∨ p2122 ∨ (¬ p3550) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4666 := h105658;
    (Or.elim h86173 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step121330 (p2122 p2383 p2406 p2427 p2819 p3379 p4556 p5021 : Prop)
    (h105399 : p4556)
    (h86192 : p2122 ∨ (¬ p2819) ∨ (¬ p5021) ∨ p2383 ∨ (¬ p4556) ∨ (¬ p2427) ∨ (¬ p2406) ∨ (¬ p3379))
    : (¬ p2819) ∨ (¬ p2406) ∨ p2122 ∨ (¬ p3379) ∨ (¬ p2427) ∨ p2383 ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4556 := h105399;
    (Or.elim h86192 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step121331 (p2122 p2307 p2373 p2406 p2819 p3379 p4134 p5017 : Prop)
    (h105379 : p4134)
    (h86202 : p3379 ∨ p2373 ∨ (¬ p2819) ∨ (¬ p2307) ∨ p2406 ∨ (¬ p5017) ∨ (¬ p4134) ∨ p2122)
    : p2406 ∨ (¬ p2307) ∨ (¬ p5017) ∨ p2373 ∨ (¬ p2819) ∨ p2122 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4134 := h105379;
    (Or.elim h86202 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u5 r6)))))))))))))))))

theorem step121335 (p2254 p2608 p2819 p2829 p3146 p3166 p3256 p4134 : Prop)
    (h105366 : p2254)
    (h105379 : p4134)
    (h86207 : (¬ p2819) ∨ (¬ p2829) ∨ (¬ p4134) ∨ p3166 ∨ (¬ p2608) ∨ (¬ p2254) ∨ p3256 ∨ (¬ p3146))
    : (¬ p2819) ∨ (¬ p3146) ∨ (¬ p2608) ∨ p3166 ∨ (¬ p2829) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4134 := h105379;
    (Or.elim h86207 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step121336 (p2252 p2459 p2608 p2750 p2807 p2819 p3093 p3256 p3919 p4024 p4133 : Prop)
    (h106345 : p2750)
    (h105712 : p4133)
    (h86219 : (¬ p2819) ∨ p2608 ∨ (¬ p3093) ∨ (¬ p4133) ∨ (¬ p4024) ∨ p2807 ∨ (¬ p2750) ∨ (¬ p3919) ∨ (¬ p2459) ∨ p3256 ∨ (¬ p2252))
    : (¬ p4024) ∨ (¬ p2252) ∨ (¬ p2819) ∨ p3256 ∨ (¬ p2459) ∨ p2608 ∨ p2807 ∨ (¬ p3093) ∨ (¬ p3919) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4024 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2750 := h106345;
    let u10 : p4133 := h105712;
    (Or.elim h86219 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u3 q9))) (fun r9 => (False.elim (r9 u1)))))))))))))))))))))))

theorem step121337 (p2254 p2459 p2608 p2819 p2829 p3166 p3256 p4133 : Prop)
    (h105366 : p2254)
    (h105712 : p4133)
    (h86220 : (¬ p2829) ∨ (¬ p2819) ∨ (¬ p2254) ∨ (¬ p4133) ∨ (¬ p2608) ∨ (¬ p2459) ∨ p3256 ∨ p3166)
    : p3166 ∨ (¬ p2819) ∨ (¬ p2608) ∨ (¬ p2829) ∨ p3256 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4133 := h105712;
    (Or.elim h86220 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step121339 (p2383 p2641 p2667 p2745 p2819 p4426 : Prop)
    (h105523 : p2745)
    (h86224 : p2641 ∨ (¬ p2819) ∨ (¬ p4426) ∨ (¬ p2745) ∨ (¬ p2667) ∨ p2383)
    : (¬ p2819) ∨ (¬ p4426) ∨ p2641 ∨ (¬ p2667) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2745 := h105523;
    (Or.elim h86224 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u4 r4)))))))))))))

theorem step121342 (p2363 p2528 p2819 p3573 p5225 : Prop)
    (h105495 : p5225)
    (h86229 : (¬ p2819) ∨ p2528 ∨ (¬ p2363) ∨ (¬ p5225) ∨ (¬ p3573))
    : p2528 ∨ (¬ p2819) ∨ (¬ p2363) ∨ (¬ p3573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5225 := h105495;
    (Or.elim h86229 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121344 (p2252 p2437 p2651 p2750 p2753 p2786 p2819 p2911 p3654 p3917 p4133 : Prop)
    (h106345 : p2750)
    (h105712 : p4133)
    (h86231 : (¬ p3917) ∨ (¬ p2819) ∨ (¬ p3654) ∨ (¬ p2750) ∨ (¬ p2786) ∨ p2437 ∨ p2911 ∨ (¬ p2753) ∨ (¬ p2252) ∨ p2651 ∨ (¬ p4133))
    : (¬ p3917) ∨ (¬ p2753) ∨ p2651 ∨ (¬ p2819) ∨ p2911 ∨ p2437 ∨ (¬ p3654) ∨ (¬ p2252) ∨ (¬ p2786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3917 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2750 := h106345;
    let u10 : p4133 := h105712;
    (Or.elim h86231 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u2 q9))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step121346 (p2230 p2274 p2563 p2608 p2819 p2829 p4405 p5193 : Prop)
    (h105512 : p4405)
    (h105488 : p5193)
    (h86234 : (¬ p2819) ∨ (¬ p2829) ∨ p2274 ∨ p2563 ∨ (¬ p2608) ∨ p2230 ∨ (¬ p4405) ∨ (¬ p5193))
    : p2230 ∨ (¬ p2829) ∨ p2274 ∨ p2563 ∨ (¬ p2608) ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2230) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4405 := h105512;
    let u7 : p5193 := h105488;
    (Or.elim h86234 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121351 (p2383 p2386 p2819 p3016 p4375 p4753 : Prop)
    (h105514 : p4753)
    (h86248 : p3016 ∨ (¬ p2819) ∨ (¬ p4753) ∨ (¬ p4375) ∨ (¬ p2386) ∨ p2383)
    : (¬ p4375) ∨ (¬ p2819) ∨ p3016 ∨ p2383 ∨ (¬ p2386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4375 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4753 := h105514;
    (Or.elim h86248 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step121353 (p2122 p2252 p2307 p2528 p2651 p2750 p2753 p2786 p2819 p3083 p3550 p3941 : Prop)
    (h106345 : p2750)
    (h86250 : (¬ p2753) ∨ (¬ p2819) ∨ (¬ p3550) ∨ (¬ p2307) ∨ p2122 ∨ (¬ p3941) ∨ (¬ p2786) ∨ p3083 ∨ (¬ p2750) ∨ (¬ p2252) ∨ p2651 ∨ p2528)
    : (¬ p3941) ∨ p2651 ∨ p2528 ∨ (¬ p2307) ∨ (¬ p2786) ∨ p2122 ∨ p3083 ∨ (¬ p2819) ∨ (¬ p2753) ∨ (¬ p3550) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2750 := h106345;
    (Or.elim h86250 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u1 q10))) (fun r10 => (False.elim (u2 r10)))))))))))))))))))))))))

theorem step121358 (p2122 p2230 p2307 p2440 p2655 p2786 p2819 p3083 p4384 p4789 : Prop)
    (h106167 : p4384)
    (h105646 : p4789)
    (h86261 : (¬ p2307) ∨ (¬ p2819) ∨ (¬ p2786) ∨ (¬ p4789) ∨ p3083 ∨ (¬ p2655) ∨ p2122 ∨ p2230 ∨ (¬ p4384) ∨ p2440)
    : p3083 ∨ (¬ p2655) ∨ (¬ p2819) ∨ p2122 ∨ (¬ p2786) ∨ p2440 ∨ p2230 ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4384 := h106167;
    let u9 : p4789 := h105646;
    (Or.elim h86261 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (u5 r8)))))))))))))))))))))

theorem step121361 (p2819 p3573 p3979 p4149 p5225 : Prop)
    (h105495 : p5225)
    (h86269 : p4149 ∨ (¬ p2819) ∨ (¬ p5225) ∨ (¬ p3573) ∨ (¬ p3979))
    : (¬ p3979) ∨ (¬ p2819) ∨ p4149 ∨ (¬ p3573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4149) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5225 := h105495;
    (Or.elim h86269 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step121364 (p2509 p2528 p2774 p2819 p3379 p3979 p4733 p5122 : Prop)
    (h105430 : p4733)
    (h105483 : p5122)
    (h86275 : (¬ p2819) ∨ (¬ p2509) ∨ (¬ p3979) ∨ (¬ p4733) ∨ (¬ p2774) ∨ p3379 ∨ p2528 ∨ (¬ p5122))
    : (¬ p3979) ∨ (¬ p2509) ∨ p3379 ∨ (¬ p2819) ∨ p2528 ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4733 := h105430;
    let u7 : p5122 := h105483;
    (Or.elim h86275 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121369 (p2819 p3367 p3923 p3953 p5221 : Prop)
    (h105796 : p5221)
    (h41149 : (¬ p2819) ∨ (¬ p3367) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p5221))
    : (¬ p3953) ∨ (¬ p3367) ∨ (¬ p2819) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3953 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5221 := h105796;
    (Or.elim h41149 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121370 (p2187 p2274 p2911 p3550 p4276 : Prop)
    (h105516 : p4276)
    (h86290 : p2274 ∨ p2911 ∨ (¬ p2187) ∨ (¬ p3550) ∨ (¬ p4276))
    : p2911 ∨ (¬ p2187) ∨ p2274 ∨ (¬ p3550) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4276 := h105516;
    (Or.elim h86290 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121373 (p2122 p2177 p2373 p2406 p2774 p3379 p4736 p4902 : Prop)
    (h105431 : p4736)
    (h105456 : p4902)
    (h86322 : p2774 ∨ p2122 ∨ (¬ p3379) ∨ (¬ p4902) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p4736) ∨ p2177)
    : (¬ p2406) ∨ (¬ p2373) ∨ (¬ p3379) ∨ p2177 ∨ p2122 ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4902 := h105456;
    (Or.elim h86322 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step121374 (p2598 p2774 p3016 p4342 p4750 : Prop)
    (h105433 : p4750)
    (h86324 : p2774 ∨ (¬ p4342) ∨ (¬ p2598) ∨ (¬ p3016) ∨ (¬ p4750))
    : (¬ p4342) ∨ p2774 ∨ (¬ p3016) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4342 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    (Or.elim h86324 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121375 (p2493 p2598 p2774 p4342 p5217 : Prop)
    (h105493 : p5217)
    (h86334 : p2774 ∨ (¬ p4342) ∨ (¬ p2598) ∨ (¬ p5217) ∨ (¬ p2493))
    : p2774 ∨ (¬ p2598) ∨ (¬ p2493) ∨ (¬ p4342) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5217 := h105493;
    (Or.elim h86334 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121377 (p2122 p2246 p2396 p2744 p2774 p2946 p3146 p3156 p3366 p4669 : Prop)
    (h106503 : p2744)
    (h105415 : p4669)
    (h86338 : p2774 ∨ p2396 ∨ (¬ p3156) ∨ (¬ p4669) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2946) ∨ p2122 ∨ (¬ p3146))
    : (¬ p2946) ∨ (¬ p3366) ∨ p2122 ∨ p2396 ∨ (¬ p2246) ∨ p2774 ∨ (¬ p3146) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4669 := h105415;
    (Or.elim h86338 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u2 q8))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step121379 (p2122 p2396 p2774 p2911 p2922 p3379 p4666 p4736 : Prop)
    (h105431 : p4736)
    (h105658 : p4666)
    (h86350 : (¬ p2911) ∨ p2396 ∨ (¬ p2922) ∨ p2122 ∨ (¬ p4666) ∨ (¬ p3379) ∨ p2774 ∨ (¬ p4736))
    : p2774 ∨ p2122 ∨ p2396 ∨ (¬ p3379) ∨ (¬ p2922) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4666 := h105658;
    (Or.elim h86350 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step121381 (p2122 p2177 p2253 p2774 p2946 p2992 p3189 p4311 p4736 p4902 : Prop)
    (h105431 : p4736)
    (h105456 : p4902)
    (h86364 : (¬ p3189) ∨ p2774 ∨ (¬ p2946) ∨ (¬ p4736) ∨ p2177 ∨ p2122 ∨ p2992 ∨ (¬ p4902) ∨ (¬ p2253) ∨ (¬ p4311))
    : (¬ p2946) ∨ p2992 ∨ p2122 ∨ p2177 ∨ (¬ p3189) ∨ (¬ p4311) ∨ (¬ p2253) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    let u9 : p4902 := h105456;
    (Or.elim h86364 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step121383 (p2246 p2744 p2774 p2946 p3156 p3366 p3461 p3917 p3969 p5119 : Prop)
    (h106503 : p2744)
    (h86368 : (¬ p3969) ∨ p3461 ∨ (¬ p3917) ∨ (¬ p5119) ∨ (¬ p2744) ∨ p2774 ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2946) ∨ (¬ p3156))
    : (¬ p3969) ∨ (¬ p3156) ∨ (¬ p5119) ∨ (¬ p2946) ∨ (¬ p3366) ∨ p2774 ∨ (¬ p2246) ∨ (¬ p3917) ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    (Or.elim h86368 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step121384 (p2363 p2417 p2774 p2819 p2922 p3379 p3950 p4736 : Prop)
    (h105431 : p4736)
    (h86370 : p2363 ∨ (¬ p4736) ∨ (¬ p3379) ∨ (¬ p2922) ∨ p2819 ∨ p2774 ∨ (¬ p3950) ∨ (¬ p2417))
    : p2774 ∨ (¬ p3950) ∨ (¬ p3379) ∨ p2819 ∨ p2363 ∨ (¬ p2417) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h86370 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step121387 (p2230 p2774 p2850 p3362 p5221 : Prop)
    (h105796 : p5221)
    (h86377 : p2850 ∨ (¬ p2230) ∨ (¬ p3362) ∨ (¬ p5221) ∨ p2774)
    : p2850 ∨ (¬ p2230) ∨ (¬ p3362) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5221 := h105796;
    (Or.elim h86377 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step121389 (p2122 p2230 p2373 p2396 p2774 p3146 p4419 p4669 : Prop)
    (h105415 : p4669)
    (h86382 : p2774 ∨ p2396 ∨ (¬ p4669) ∨ (¬ p4419) ∨ (¬ p2373) ∨ p2122 ∨ (¬ p2230) ∨ (¬ p3146))
    : (¬ p2373) ∨ (¬ p2230) ∨ (¬ p3146) ∨ (¬ p4419) ∨ p2774 ∨ p2122 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4669 := h105415;
    (Or.elim h86382 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step121390 (p2341 p2417 p2696 p2774 p2911 p3759 p3917 p4625 p4749 p5201 : Prop)
    (h105432 : p4749)
    (h106455 : p4625)
    (h86383 : p2774 ∨ (¬ p3917) ∨ (¬ p4749) ∨ (¬ p5201) ∨ (¬ p2696) ∨ (¬ p3759) ∨ (¬ p2341) ∨ (¬ p2417) ∨ p2911 ∨ (¬ p4625))
    : (¬ p2341) ∨ (¬ p3917) ∨ (¬ p2417) ∨ p2774 ∨ p2911 ∨ (¬ p2696) ∨ (¬ p5201) ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4749 := h105432;
    let u9 : p4625 := h106455;
    (Or.elim h86383 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step121396 (p2553 p2774 p3425 p4475 p5225 : Prop)
    (h105495 : p5225)
    (h86400 : (¬ p4475) ∨ p2774 ∨ p2553 ∨ (¬ p5225) ∨ p3425)
    : p3425 ∨ p2774 ∨ p2553 ∨ (¬ p4475) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5225 := h105495;
    (Or.elim h86400 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step121401 (p2246 p2363 p2417 p2437 p2651 p2744 p2774 p2819 p3366 p3950 : Prop)
    (h106503 : p2744)
    (h86419 : p2363 ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2417) ∨ (¬ p3950) ∨ (¬ p2437) ∨ p2774 ∨ p2819)
    : p2774 ∨ (¬ p2246) ∨ p2363 ∨ (¬ p3950) ∨ (¬ p2437) ∨ (¬ p2417) ∨ (¬ p2651) ∨ p2819 ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    (Or.elim h86419 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u0 q8))) (fun r8 => (False.elim (u7 r8)))))))))))))))))))))

theorem step121403 (p2122 p2396 p2440 p2651 p2774 p2982 p4395 p4786 : Prop)
    (h106425 : p4786)
    (h86435 : p2774 ∨ p2122 ∨ (¬ p2651) ∨ p2396 ∨ (¬ p2982) ∨ (¬ p4395) ∨ p2440 ∨ (¬ p4786))
    : p2774 ∨ (¬ p2651) ∨ (¬ p4395) ∨ (¬ p2982) ∨ p2440 ∨ p2122 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    (Or.elim h86435 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121404 (p2122 p2177 p2241 p2744 p2774 p3037 p3366 p3399 p3931 p5564 : Prop)
    (h106503 : p2744)
    (h86437 : (¬ p3399) ∨ p2241 ∨ (¬ p2744) ∨ (¬ p5564) ∨ p2177 ∨ p2122 ∨ (¬ p3931) ∨ (¬ p3037) ∨ (¬ p3366) ∨ p2774)
    : (¬ p3931) ∨ (¬ p5564) ∨ (¬ p3399) ∨ p2241 ∨ p2774 ∨ (¬ p3366) ∨ (¬ p3037) ∨ p2122 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    (Or.elim h86437 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (u4 r8)))))))))))))))))))))

theorem step121408 (p2122 p2253 p2274 p2641 p2774 p3166 p3189 p4564 p4736 : Prop)
    (h105431 : p4736)
    (h105401 : p4564)
    (h86455 : (¬ p2641) ∨ p2774 ∨ (¬ p4736) ∨ (¬ p3166) ∨ p3189 ∨ p2122 ∨ (¬ p4564) ∨ (¬ p2253) ∨ (¬ p2274))
    : p3189 ∨ p2774 ∨ (¬ p2274) ∨ (¬ p2641) ∨ p2122 ∨ (¬ p3166) ∨ (¬ p2253) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4564 := h105401;
    (Or.elim h86455 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step121411 (p2122 p2177 p2774 p3146 p3166 p3256 p4786 p4902 : Prop)
    (h105456 : p4902)
    (h106425 : p4786)
    (h86469 : (¬ p3166) ∨ p3146 ∨ (¬ p3256) ∨ p2177 ∨ (¬ p4786) ∨ p2774 ∨ p2122 ∨ (¬ p4902))
    : p2122 ∨ p2774 ∨ p3146 ∨ p2177 ∨ (¬ p3166) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4902 := h105456;
    let u7 : p4786 := h106425;
    (Or.elim h86469 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step121413 (p2122 p2774 p3166 p3256 p3266 p4260 p4786 p4831 : Prop)
    (h106425 : p4786)
    (h105445 : p4831)
    (h86473 : (¬ p4260) ∨ (¬ p3266) ∨ (¬ p4831) ∨ (¬ p4786) ∨ p2774 ∨ p2122 ∨ (¬ p3166) ∨ (¬ p3256))
    : (¬ p4260) ∨ (¬ p3166) ∨ p2122 ∨ (¬ p3266) ∨ (¬ p3256) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4786 := h106425;
    let u7 : p4831 := h105445;
    (Or.elim h86473 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step121415 (p2264 p2449 p2528 p4420 p4443 : Prop)
    (h105707 : p4420)
    (h86496 : (¬ p2449) ∨ p2528 ∨ (¬ p4443) ∨ (¬ p4420) ∨ p2264)
    : p2528 ∨ (¬ p2449) ∨ p2264 ∨ (¬ p4443) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4420 := h105707;
    (Or.elim h86496 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step121416 (p2252 p2449 p2685 p2745 p3516 p4849 : Prop)
    (h105523 : p2745)
    (h86506 : (¬ p4849) ∨ (¬ p2449) ∨ (¬ p2252) ∨ p3516 ∨ (¬ p2745) ∨ (¬ p2685))
    : (¬ p2449) ∨ (¬ p2685) ∨ (¬ p4849) ∨ (¬ p2252) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4849 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2745 := h105523;
    (Or.elim h86506 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step121418 (p2341 p2396 p2449 p2881 p4155 p4559 : Prop)
    (h105701 : p4559)
    (h86520 : p2341 ∨ p2396 ∨ (¬ p4559) ∨ (¬ p2881) ∨ (¬ p4155) ∨ (¬ p2449))
    : (¬ p4155) ∨ (¬ p2881) ∨ (¬ p2449) ∨ p2396 ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4155 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4559 := h105701;
    (Or.elim h86520 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step121419 (p2264 p2417 p2449 p2881 p4277 : Prop)
    (h105380 : p4277)
    (h86525 : (¬ p2449) ∨ p2417 ∨ (¬ p2881) ∨ p2264 ∨ (¬ p4277))
    : (¬ p2881) ∨ p2417 ∨ (¬ p2449) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4277 := h105380;
    (Or.elim h86525 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121423 (p2132 p2187 p2264 p2449 p2860 p3516 p4133 p5260 : Prop)
    (h105712 : p4133)
    (h86541 : (¬ p2449) ∨ (¬ p2860) ∨ (¬ p2187) ∨ p3516 ∨ (¬ p2132) ∨ (¬ p5260) ∨ (¬ p4133) ∨ p2264)
    : p3516 ∨ (¬ p2449) ∨ (¬ p5260) ∨ (¬ p2132) ∨ p2264 ∨ (¬ p2187) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4133 := h105712;
    (Or.elim h86541 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step121424 (p2417 p2440 p2449 p3580 p4646 : Prop)
    (h105534 : p4646)
    (h86542 : p2417 ∨ (¬ p2449) ∨ (¬ p2440) ∨ (¬ p4646) ∨ (¬ p3580))
    : (¬ p2440) ∨ (¬ p2449) ∨ (¬ p3580) ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4646 := h105534;
    (Or.elim h86542 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121425 (p2427 p2449 p2995 p3246 p4705 : Prop)
    (h106238 : p4705)
    (h86545 : p3246 ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p4705) ∨ p2427)
    : (¬ p2449) ∨ p2427 ∨ p3246 ∨ (¬ p2995) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4705 := h106238;
    (Or.elim h86545 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step121426 (p2417 p2441 p2449 p3083 p3580 p4608 : Prop)
    (h105540 : p4608)
    (h86547 : p2417 ∨ (¬ p2449) ∨ p3083 ∨ (¬ p2441) ∨ (¬ p4608) ∨ (¬ p3580))
    : p3083 ∨ (¬ p2449) ∨ (¬ p2441) ∨ p2417 ∨ (¬ p3580) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4608 := h105540;
    (Or.elim h86547 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step121427 (p2417 p2441 p2449 p3016 p3580 p4715 : Prop)
    (h105423 : p4715)
    (h86548 : p2417 ∨ (¬ p2449) ∨ (¬ p2441) ∨ p3016 ∨ (¬ p3580) ∨ (¬ p4715))
    : p3016 ∨ (¬ p2449) ∨ (¬ p2441) ∨ p2417 ∨ (¬ p3580) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4715 := h105423;
    (Or.elim h86548 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121431 (p2210 p2870 p3399 p3571 p4878 : Prop)
    (h105452 : p4878)
    (h86570 : (¬ p3399) ∨ p2210 ∨ (¬ p4878) ∨ p2870 ∨ (¬ p3571))
    : p2210 ∨ p2870 ∨ (¬ p3399) ∨ (¬ p3571) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4878 := h105452;
    (Or.elim h86570 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121433 (p2248 p2264 p2608 p2807 p2839 p2870 p2911 p4277 : Prop)
    (h105365 : p2248)
    (h105380 : p4277)
    (h86584 : p2911 ∨ (¬ p2264) ∨ p2839 ∨ p2608 ∨ (¬ p2807) ∨ (¬ p2248) ∨ p2870 ∨ (¬ p4277))
    : p2839 ∨ p2608 ∨ p2870 ∨ (¬ p2807) ∨ (¬ p2264) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4277 := h105380;
    (Or.elim h86584 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121434 (p2248 p2396 p2449 p2608 p2807 p2839 p2870 p4559 : Prop)
    (h105365 : p2248)
    (h105701 : p4559)
    (h86588 : (¬ p2449) ∨ p2870 ∨ (¬ p4559) ∨ (¬ p2807) ∨ p2396 ∨ (¬ p2248) ∨ p2608 ∨ p2839)
    : p2396 ∨ p2839 ∨ p2870 ∨ (¬ p2807) ∨ (¬ p2449) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4559 := h105701;
    (Or.elim h86588 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step121440 (p2132 p2241 p2264 p2870 p2996 p3246 p4666 p4736 : Prop)
    (h105431 : p4736)
    (h105658 : p4666)
    (h86597 : p3246 ∨ (¬ p2264) ∨ (¬ p4736) ∨ (¬ p4666) ∨ (¬ p2241) ∨ p2132 ∨ p2996 ∨ p2870)
    : p2870 ∨ p2132 ∨ p3246 ∨ (¬ p2241) ∨ (¬ p2264) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4666 := h105658;
    (Or.elim h86597 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step121441 (p2132 p2363 p2870 p3063 p3093 p3246 p4669 p4736 : Prop)
    (h105431 : p4736)
    (h105415 : p4669)
    (h86601 : (¬ p3063) ∨ p3246 ∨ p2870 ∨ (¬ p4736) ∨ (¬ p3093) ∨ p2132 ∨ (¬ p4669) ∨ (¬ p2363))
    : p2870 ∨ (¬ p3093) ∨ p3246 ∨ (¬ p2363) ∨ (¬ p3063) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4669 := h105415;
    (Or.elim h86601 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step121442 (p2132 p2177 p2870 p3093 p3246 p3309 p4666 p4736 : Prop)
    (h105431 : p4736)
    (h105658 : p4666)
    (h86603 : (¬ p3309) ∨ p3246 ∨ (¬ p2177) ∨ (¬ p4666) ∨ (¬ p3093) ∨ p2132 ∨ (¬ p4736) ∨ p2870)
    : p2132 ∨ p2870 ∨ (¬ p3309) ∨ p3246 ∨ (¬ p3093) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4666 := h105658;
    (Or.elim h86603 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step121443 (p2132 p2352 p2363 p2573 p2870 p3246 p4419 p4669 : Prop)
    (h105415 : p4669)
    (h86605 : (¬ p2352) ∨ p2870 ∨ (¬ p4669) ∨ p3246 ∨ (¬ p2573) ∨ (¬ p4419) ∨ (¬ p2363) ∨ p2132)
    : (¬ p2573) ∨ (¬ p2352) ∨ (¬ p4419) ∨ p2132 ∨ p3246 ∨ (¬ p2363) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4669 := h105415;
    (Or.elim h86605 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step121445 (p2132 p2241 p2727 p2870 p2881 p3083 p4420 p4736 : Prop)
    (h105431 : p4736)
    (h105707 : p4420)
    (h86619 : p2132 ∨ p2870 ∨ (¬ p4736) ∨ (¬ p4420) ∨ (¬ p2727) ∨ p2881 ∨ (¬ p2241) ∨ (¬ p3083))
    : p2870 ∨ (¬ p3083) ∨ (¬ p2727) ∨ (¬ p2241) ∨ p2881 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4420 := h105707;
    (Or.elim h86619 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step121446 (p2132 p2528 p2651 p2870 p3083 p3246 p4669 p4786 : Prop)
    (h105415 : p4669)
    (h106425 : p4786)
    (h86621 : p3246 ∨ p2132 ∨ p2870 ∨ (¬ p4669) ∨ (¬ p2528) ∨ (¬ p3083) ∨ (¬ p2651) ∨ (¬ p4786))
    : p2870 ∨ (¬ p2651) ∨ (¬ p2528) ∨ (¬ p3083) ∨ p2132 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4669 := h105415;
    let u7 : p4786 := h106425;
    (Or.elim h86621 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121447 (p2136 p2220 p2553 p2619 p2651 p2870 p3016 p4559 p4786 : Prop)
    (h105701 : p4559)
    (h106425 : p4786)
    (h86636 : (¬ p2553) ∨ p2220 ∨ (¬ p2651) ∨ (¬ p2136) ∨ (¬ p4559) ∨ p2870 ∨ (¬ p2619) ∨ (¬ p4786) ∨ (¬ p3016))
    : (¬ p2136) ∨ p2870 ∨ p2220 ∨ (¬ p2619) ∨ (¬ p2651) ∨ (¬ p2553) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4559 := h105701;
    let u8 : p4786 := h106425;
    (Or.elim h86636 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step121449 (p2341 p2870 p3527 p4283 p4431 p4878 : Prop)
    (h105452 : p4878)
    (h86639 : (¬ p3527) ∨ (¬ p4878) ∨ (¬ p4431) ∨ (¬ p4283) ∨ p2341 ∨ p2870)
    : p2870 ∨ (¬ p4283) ∨ (¬ p4431) ∨ p2341 ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4878 := h105452;
    (Or.elim h86639 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step121452 (p2144 p2241 p2619 p2750 p2753 p2870 p3051 p3093 p3923 p4433 : Prop)
    (h106345 : p2750)
    (h106150 : p4433)
    (h86649 : p2870 ∨ (¬ p2619) ∨ p3093 ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p3923) ∨ (¬ p4433) ∨ (¬ p2241) ∨ (¬ p3051) ∨ (¬ p2144))
    : p3093 ∨ (¬ p2144) ∨ (¬ p2241) ∨ p2870 ∨ (¬ p2753) ∨ (¬ p3051) ∨ (¬ p2619) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    let u9 : p4433 := h106150;
    (Or.elim h86649 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step121455 (p2352 p2493 p2619 p2870 p3051 p3379 p4433 p4521 : Prop)
    (h106150 : p4433)
    (h86652 : p2493 ∨ (¬ p3051) ∨ p2352 ∨ (¬ p2619) ∨ p2870 ∨ (¬ p4521) ∨ p3379 ∨ (¬ p4433))
    : (¬ p2619) ∨ p2870 ∨ p2352 ∨ (¬ p3051) ∨ p3379 ∨ p2493 ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4433 := h106150;
    (Or.elim h86652 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121456 (p2449 p2870 p2995 p3246 p4906 : Prop)
    (h105632 : p4906)
    (h86654 : p3246 ∨ (¬ p2449) ∨ (¬ p4906) ∨ (¬ p2995) ∨ p2870)
    : (¬ p2449) ∨ (¬ p2995) ∨ p3246 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4906 := h105632;
    (Or.elim h86654 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step121457 (p2619 p2870 p3246 p4042 p4666 : Prop)
    (h105658 : p4666)
    (h86655 : (¬ p2619) ∨ p2870 ∨ (¬ p4666) ∨ p3246 ∨ (¬ p4042))
    : p2870 ∨ (¬ p2619) ∨ (¬ p4042) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4666 := h105658;
    (Or.elim h86655 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121460 (p2373 p2619 p2870 p3051 p4539 : Prop)
    (h105395 : p4539)
    (h86661 : p2870 ∨ (¬ p2619) ∨ p2373 ∨ (¬ p3051) ∨ (¬ p4539))
    : p2870 ∨ (¬ p2619) ∨ p2373 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4539 := h105395;
    (Or.elim h86661 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121461 (p2132 p2241 p2870 p3189 p3246 p3256 p4669 p4736 : Prop)
    (h105431 : p4736)
    (h105415 : p4669)
    (h86664 : (¬ p3189) ∨ p2870 ∨ (¬ p4669) ∨ p2132 ∨ (¬ p2241) ∨ (¬ p4736) ∨ p3246 ∨ (¬ p3256))
    : p2132 ∨ p2870 ∨ (¬ p3189) ∨ (¬ p2241) ∨ p3246 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4669 := h105415;
    (Or.elim h86664 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step121462 (p2132 p2573 p2870 p2881 p3016 p3083 p4419 p4420 : Prop)
    (h105707 : p4420)
    (h86668 : p2870 ∨ p3016 ∨ (¬ p4419) ∨ p2881 ∨ (¬ p2573) ∨ (¬ p4420) ∨ (¬ p3083) ∨ p2132)
    : p2132 ∨ p2870 ∨ (¬ p4419) ∨ p3016 ∨ (¬ p2573) ∨ p2881 ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4420 := h105707;
    (Or.elim h86668 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step121463 (p2132 p2363 p2510 p2528 p2573 p2870 p2881 p4079 p4133 p4736 : Prop)
    (h105431 : p4736)
    (h105712 : p4133)
    (h86669 : p2363 ∨ (¬ p2528) ∨ (¬ p4079) ∨ (¬ p2510) ∨ (¬ p4736) ∨ p2881 ∨ (¬ p4133) ∨ (¬ p2573) ∨ p2870 ∨ p2132)
    : p2132 ∨ p2870 ∨ (¬ p4079) ∨ p2363 ∨ (¬ p2510) ∨ p2881 ∨ (¬ p2528) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    let u9 : p4133 := h105712;
    (Or.elim h86669 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (False.elim (u0 r8)))))))))))))))))))))

theorem step121464 (p2132 p2493 p2870 p3246 p3379 p3564 p4621 p4736 : Prop)
    (h105431 : p4736)
    (h105407 : p4621)
    (h86671 : (¬ p3564) ∨ p2132 ∨ (¬ p3379) ∨ (¬ p2493) ∨ p3246 ∨ (¬ p4621) ∨ p2870 ∨ (¬ p4736))
    : p2870 ∨ p2132 ∨ (¬ p3379) ∨ (¬ p2493) ∨ (¬ p3564) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4621 := h105407;
    (Or.elim h86671 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step121465 (p2132 p2518 p2528 p2870 p3246 p3379 p4669 p4736 : Prop)
    (h105431 : p4736)
    (h105415 : p4669)
    (h86674 : (¬ p2518) ∨ (¬ p2528) ∨ p2132 ∨ (¬ p4736) ∨ p3246 ∨ p2870 ∨ (¬ p4669) ∨ (¬ p3379))
    : p2870 ∨ (¬ p2518) ∨ p2132 ∨ (¬ p3379) ∨ (¬ p2528) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4669 := h105415;
    (Or.elim h86674 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step121468 (p2177 p2619 p2870 p4042 p4559 : Prop)
    (h105701 : p4559)
    (h86687 : (¬ p4042) ∨ (¬ p2619) ∨ p2177 ∨ p2870 ∨ (¬ p4559))
    : (¬ p2619) ∨ p2870 ∨ (¬ p4042) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4559 := h105701;
    (Or.elim h86687 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121470 (p2132 p2417 p2870 p2881 p2922 p3379 p4668 p4736 : Prop)
    (h105431 : p4736)
    (h105414 : p4668)
    (h86694 : (¬ p2417) ∨ p2132 ∨ (¬ p3379) ∨ (¬ p4668) ∨ (¬ p2922) ∨ p2870 ∨ p2881 ∨ (¬ p4736))
    : p2870 ∨ (¬ p2417) ∨ p2881 ∨ p2132 ∨ (¬ p2922) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4668 := h105414;
    (Or.elim h86694 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step121473 (p2132 p2241 p2744 p2870 p3073 p3246 p3366 p3449 p4669 : Prop)
    (h106503 : p2744)
    (h105415 : p4669)
    (h86701 : (¬ p3449) ∨ p2241 ∨ (¬ p4669) ∨ p2870 ∨ (¬ p3073) ∨ p3246 ∨ (¬ p2744) ∨ (¬ p3366) ∨ p2132)
    : p2870 ∨ p2132 ∨ p2241 ∨ p3246 ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2744 := h106503;
    let u8 : p4669 := h105415;
    (Or.elim h86701 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u1 r7)))))))))))))))))))

theorem step121476 (p2132 p2573 p2870 p3246 p3367 p3564 p3759 p4621 : Prop)
    (h105407 : p4621)
    (h86706 : (¬ p3564) ∨ (¬ p3759) ∨ (¬ p4621) ∨ p2132 ∨ p2870 ∨ (¬ p3367) ∨ (¬ p2573) ∨ p3246)
    : p2132 ∨ (¬ p3367) ∨ (¬ p3759) ∨ p3246 ∨ (¬ p3564) ∨ p2870 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4621 := h105407;
    (Or.elim h86706 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step121477 (p2132 p2573 p2870 p3016 p3246 p3343 p4419 p4638 : Prop)
    (h105409 : p4638)
    (h86707 : (¬ p3343) ∨ (¬ p4638) ∨ p2870 ∨ p3246 ∨ p2132 ∨ (¬ p4419) ∨ p3016 ∨ (¬ p2573))
    : p2870 ∨ p2132 ∨ p3016 ∨ (¬ p3343) ∨ (¬ p2573) ∨ p3246 ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4638 := h105409;
    (Or.elim h86707 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step121478 (p2136 p2156 p2341 p2860 p2870 p2911 p3366 p3379 p3545 p4277 p4376 : Prop)
    (h106320 : p4376)
    (h105380 : p4277)
    (h86708 : (¬ p2341) ∨ p2870 ∨ (¬ p4277) ∨ p2911 ∨ (¬ p3366) ∨ (¬ p3545) ∨ (¬ p2136) ∨ (¬ p2860) ∨ p3379 ∨ p2156 ∨ (¬ p4376))
    : (¬ p2136) ∨ p2870 ∨ (¬ p2341) ∨ p2156 ∨ (¬ p2860) ∨ p3379 ∨ (¬ p3366) ∨ p2911 ∨ (¬ p3545) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3545 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    let u10 : p4277 := h105380;
    (Or.elim h86708 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u3 q9))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step121481 (p2132 p2246 p2331 p2363 p2668 p2744 p2870 p3246 p3366 p4669 : Prop)
    (h106503 : p2744)
    (h105415 : p4669)
    (h86715 : (¬ p2668) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p3366) ∨ p2870 ∨ (¬ p4669) ∨ (¬ p2331) ∨ p2132 ∨ p3246 ∨ (¬ p2744))
    : p2870 ∨ p2132 ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ p3246 ∨ (¬ p3366) ∨ (¬ p2246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4669 := h105415;
    (Or.elim h86715 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step121482 (p2427 p2440 p2870 p4750 : Prop)
    (h105433 : p4750)
    (h86716 : p2870 ∨ p2440 ∨ (¬ p4750) ∨ (¬ p2427))
    : p2440 ∨ p2870 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4750 := h105433;
    (Or.elim h86716 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step121486 (p2132 p2241 p2641 p2668 p2870 p2881 p4133 p4736 : Prop)
    (h105431 : p4736)
    (h105712 : p4133)
    (h86735 : (¬ p2668) ∨ (¬ p2641) ∨ p2132 ∨ (¬ p4133) ∨ p2870 ∨ (¬ p2241) ∨ (¬ p4736) ∨ p2881)
    : p2870 ∨ p2132 ∨ (¬ p2668) ∨ (¬ p2641) ∨ p2881 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4133 := h105712;
    (Or.elim h86735 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step121488 (p2156 p2253 p2651 p2727 p2860 p2870 p2996 p4280 : Prop)
    (h105599 : p4280)
    (h86738 : (¬ p2253) ∨ p2727 ∨ p2156 ∨ (¬ p2860) ∨ p2996 ∨ (¬ p2651) ∨ p2870 ∨ (¬ p4280))
    : (¬ p2860) ∨ p2870 ∨ (¬ p2651) ∨ p2727 ∨ p2996 ∨ (¬ p2253) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4280 := h105599;
    (Or.elim h86738 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121489 (p2751 p2870 p2951 p2992 p3051 p4392 : Prop)
    (h106343 : p2751)
    (h86742 : p2870 ∨ (¬ p2951) ∨ (¬ p4392) ∨ (¬ p2992) ∨ (¬ p2751) ∨ (¬ p3051))
    : (¬ p4392) ∨ p2870 ∨ (¬ p3051) ∨ (¬ p2992) ∨ (¬ p2951) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4392 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    (Or.elim h86742 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step121491 (p2493 p2509 p2573 p2619 p2870 p3051 p4108 p4434 p4521 : Prop)
    (h106144 : p4434)
    (h86747 : p2870 ∨ (¬ p2619) ∨ (¬ p2509) ∨ (¬ p3051) ∨ (¬ p2493) ∨ p2573 ∨ (¬ p4521) ∨ (¬ p4434) ∨ (¬ p4108))
    : (¬ p2509) ∨ (¬ p4108) ∨ (¬ p3051) ∨ (¬ p2619) ∨ (¬ p2493) ∨ p2573 ∨ p2870 ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4434 := h106144;
    (Or.elim h86747 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step121492 (p2144 p2252 p2363 p2619 p2750 p2753 p2870 p3051 p3166 p3256 p4433 : Prop)
    (h106345 : p2750)
    (h106150 : p4433)
    (h86748 : p2870 ∨ p3256 ∨ (¬ p3051) ∨ (¬ p2252) ∨ (¬ p2144) ∨ p3166 ∨ (¬ p2750) ∨ (¬ p2363) ∨ (¬ p2753) ∨ (¬ p2619) ∨ (¬ p4433))
    : (¬ p2619) ∨ (¬ p2144) ∨ p3256 ∨ p2870 ∨ (¬ p2363) ∨ (¬ p3051) ∨ (¬ p2753) ∨ p3166 ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2750 := h106345;
    let u10 : p4433 := h106150;
    (Or.elim h86748 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step121493 (p2144 p2363 p2619 p2870 p3051 p3073 p3093 p4371 p4433 p4733 : Prop)
    (h105430 : p4733)
    (h106150 : p4433)
    (h86751 : (¬ p2619) ∨ p2870 ∨ (¬ p4433) ∨ (¬ p3051) ∨ (¬ p2363) ∨ (¬ p4371) ∨ (¬ p4733) ∨ p3073 ∨ p3093 ∨ (¬ p2144))
    : p3073 ∨ p3093 ∨ (¬ p2363) ∨ (¬ p3051) ∨ p2870 ∨ (¬ p2619) ∨ (¬ p2144) ∨ (¬ p4371) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4733 := h105430;
    let u9 : p4433 := h106150;
    (Or.elim h86751 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step121494 (p2132 p2246 p2470 p2663 p2744 p2870 p3083 p3246 p3343 p3366 p4638 : Prop)
    (h106503 : p2744)
    (h105409 : p4638)
    (h86753 : (¬ p2470) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2663) ∨ p2870 ∨ p2132 ∨ (¬ p2744) ∨ (¬ p4638) ∨ p3246 ∨ p3083)
    : p2870 ∨ p3083 ∨ p3246 ∨ (¬ p2470) ∨ (¬ p3366) ∨ (¬ p2663) ∨ (¬ p2246) ∨ p2132 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    let u10 : p4638 := h105409;
    (Or.elim h86753 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u2 q9))) (fun r9 => (False.elim (u1 r9)))))))))))))))))))))))

theorem step121495 (p2132 p2493 p2518 p2573 p2870 p2881 p4079 p4133 p4157 p4736 : Prop)
    (h105431 : p4736)
    (h105712 : p4133)
    (h86756 : (¬ p4157) ∨ (¬ p2518) ∨ p2881 ∨ (¬ p4133) ∨ (¬ p4736) ∨ (¬ p2573) ∨ p2132 ∨ p2870 ∨ (¬ p4079) ∨ p2493)
    : (¬ p2573) ∨ (¬ p4157) ∨ (¬ p4079) ∨ (¬ p2518) ∨ p2870 ∨ p2493 ∨ p2881 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    let u9 : p4133 := h105712;
    (Or.elim h86756 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (u5 r8)))))))))))))))))))))

theorem step121496 (p2252 p2528 p2651 p2750 p2870 p3051 p3083 p3105 p3370 p3371 p4450 : Prop)
    (h106345 : p2750)
    (h86758 : p2528 ∨ (¬ p3370) ∨ (¬ p3105) ∨ (¬ p4450) ∨ p3083 ∨ (¬ p3051) ∨ (¬ p2252) ∨ (¬ p3371) ∨ (¬ p2750) ∨ p2651 ∨ p2870)
    : (¬ p3105) ∨ p2870 ∨ p2528 ∨ (¬ p4450) ∨ (¬ p3051) ∨ p2651 ∨ p3083 ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2750 := h106345;
    (Or.elim h86758 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u5 q9))) (fun r9 => (False.elim (u1 r9)))))))))))))))))))))))

theorem step121499 (p2144 p2252 p2331 p2363 p2668 p2750 p2753 p2870 p3051 p3105 p4450 : Prop)
    (h106345 : p2750)
    (h86763 : p2870 ∨ p2363 ∨ (¬ p3105) ∨ (¬ p4450) ∨ p2668 ∨ (¬ p2753) ∨ (¬ p2144) ∨ p2331 ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p3051))
    : (¬ p3105) ∨ p2870 ∨ p2363 ∨ (¬ p3051) ∨ (¬ p4450) ∨ p2331 ∨ p2668 ∨ (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2750 := h106345;
    (Or.elim h86763 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step121500 (p2144 p2696 p2870 p3051 p5052 : Prop)
    (h105473 : p5052)
    (h86765 : p2870 ∨ (¬ p5052) ∨ (¬ p3051) ∨ p2696 ∨ (¬ p2144))
    : p2696 ∨ (¬ p2144) ∨ p2870 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5052 := h105473;
    (Or.elim h86765 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121501 (p2132 p2870 p2911 p2922 p3246 p3379 p4666 p4736 : Prop)
    (h105431 : p4736)
    (h105658 : p4666)
    (h86772 : p3246 ∨ p2132 ∨ (¬ p2911) ∨ (¬ p3379) ∨ p2870 ∨ (¬ p2922) ∨ (¬ p4666) ∨ (¬ p4736))
    : p2870 ∨ p2132 ∨ (¬ p2911) ∨ (¬ p3379) ∨ (¬ p2922) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4666 := h105658;
    (Or.elim h86772 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step121502 (p2132 p2870 p2911 p3246 p3367 p3389 p3759 p4666 : Prop)
    (h105658 : p4666)
    (h86775 : p2132 ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p4666) ∨ (¬ p3759) ∨ p3246 ∨ p2870 ∨ (¬ p3367))
    : p2132 ∨ (¬ p3367) ∨ p3246 ∨ p2870 ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4666 := h105658;
    (Or.elim h86775 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step121505 (p2156 p2563 p2870 p3051 p4882 : Prop)
    (h105453 : p4882)
    (h86783 : p2870 ∨ (¬ p3051) ∨ (¬ p4882) ∨ (¬ p2563) ∨ p2156)
    : (¬ p3051) ∨ p2156 ∨ p2870 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4882 := h105453;
    (Or.elim h86783 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step121507 (p2341 p2870 p2911 p3741 p4283 p4882 : Prop)
    (h105453 : p4882)
    (h86786 : (¬ p2911) ∨ p2341 ∨ (¬ p4882) ∨ (¬ p3741) ∨ (¬ p4283) ∨ p2870)
    : p2870 ∨ (¬ p2911) ∨ p2341 ∨ (¬ p4283) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4882 := h105453;
    (Or.elim h86786 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step121508 (p2417 p2870 p3516 p3741 p4283 p4882 : Prop)
    (h105453 : p4882)
    (h86787 : p3516 ∨ (¬ p2417) ∨ (¬ p3741) ∨ (¬ p4283) ∨ p2870 ∨ (¬ p4882))
    : (¬ p4283) ∨ p2870 ∨ (¬ p2417) ∨ (¬ p3741) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4283 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4882 := h105453;
    (Or.elim h86787 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121509 (p2132 p2248 p2331 p2363 p2668 p2870 p3246 p3873 p4669 : Prop)
    (h105365 : p2248)
    (h105415 : p4669)
    (h86790 : (¬ p2668) ∨ (¬ p3873) ∨ p2870 ∨ (¬ p4669) ∨ (¬ p2331) ∨ (¬ p2248) ∨ p2132 ∨ (¬ p2363) ∨ p3246)
    : (¬ p2331) ∨ (¬ p2363) ∨ p2870 ∨ p3246 ∨ (¬ p2668) ∨ p2132 ∨ (¬ p3873) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    let u8 : p4669 := h105415;
    (Or.elim h86790 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (u3 r7)))))))))))))))))))

theorem step121512 (p2144 p2493 p2619 p2753 p2870 p3016 p3051 p3083 p4434 : Prop)
    (h106144 : p4434)
    (h86796 : p2870 ∨ (¬ p2619) ∨ p3083 ∨ (¬ p4434) ∨ (¬ p3016) ∨ (¬ p3051) ∨ p2493 ∨ (¬ p2753) ∨ (¬ p2144))
    : (¬ p2144) ∨ (¬ p2619) ∨ (¬ p2753) ∨ p2870 ∨ (¬ p3016) ∨ p3083 ∨ (¬ p3051) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4434 := h106144;
    (Or.elim h86796 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step121515 (p2132 p2246 p2528 p2651 p2744 p2870 p3083 p3246 p3366 p4669 : Prop)
    (h106503 : p2744)
    (h105415 : p4669)
    (h86800 : p2132 ∨ (¬ p2246) ∨ (¬ p2528) ∨ p3246 ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p4669) ∨ p2870 ∨ (¬ p3366) ∨ (¬ p2651))
    : p2132 ∨ p2870 ∨ (¬ p3083) ∨ p3246 ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3366) ∨ (¬ p2246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4669 := h105415;
    (Or.elim h86800 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step121516 (p2132 p2241 p2744 p2870 p3246 p3366 p3399 p3527 p4666 : Prop)
    (h106503 : p2744)
    (h105658 : p4666)
    (h86801 : (¬ p3527) ∨ p2241 ∨ p3246 ∨ (¬ p2744) ∨ p2132 ∨ (¬ p4666) ∨ p2870 ∨ (¬ p3366) ∨ (¬ p3399))
    : p2870 ∨ p2132 ∨ p2241 ∨ (¬ p3399) ∨ p3246 ∨ (¬ p3527) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2744 := h106503;
    let u8 : p4666 := h105658;
    (Or.elim h86801 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step121517 (p2241 p2619 p2727 p2870 p3051 p3083 p4434 p4521 : Prop)
    (h106144 : p4434)
    (h86802 : p2870 ∨ (¬ p2619) ∨ (¬ p4521) ∨ p2727 ∨ p2241 ∨ (¬ p4434) ∨ p3083 ∨ (¬ p3051))
    : p3083 ∨ p2870 ∨ (¬ p3051) ∨ (¬ p4521) ∨ (¬ p2619) ∨ p2241 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4434 := h106144;
    (Or.elim h86802 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step121518 (p2144 p2598 p2870 p3051 p4884 : Prop)
    (h105454 : p4884)
    (h86806 : p2870 ∨ (¬ p3051) ∨ p2598 ∨ (¬ p4884) ∨ (¬ p2144))
    : p2598 ∨ (¬ p2144) ∨ (¬ p3051) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2598) := (fun h => hn (Or.inl h));
    let u1 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4884 := h105454;
    (Or.elim h86806 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121528 (p2177 p2341 p2417 p3516 p4276 : Prop)
    (h105516 : p4276)
    (h86838 : p2417 ∨ (¬ p3516) ∨ (¬ p2177) ∨ p2341 ∨ (¬ p4276))
    : (¬ p3516) ∨ p2341 ∨ p2417 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4276 := h105516;
    (Or.elim h86838 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121532 (p2341 p2417 p2881 p3516 p4277 : Prop)
    (h105380 : p4277)
    (h86849 : (¬ p3516) ∨ p2417 ∨ (¬ p4277) ∨ p2341 ∨ (¬ p2881))
    : (¬ p3516) ∨ p2417 ∨ (¬ p2881) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4277 := h105380;
    (Or.elim h86849 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121535 (p2417 p2922 p3516 p5194 p5201 : Prop)
    (h105489 : p5194)
    (h86870 : p2417 ∨ (¬ p3516) ∨ p2922 ∨ (¬ p5194) ∨ (¬ p5201))
    : (¬ p5201) ∨ (¬ p3516) ∨ p2922 ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5194 := h105489;
    (Or.elim h86870 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step121536 (p2177 p2341 p3246 p3516 p4556 : Prop)
    (h105399 : p4556)
    (h86881 : (¬ p3516) ∨ (¬ p4556) ∨ p3246 ∨ (¬ p2177) ∨ p2341)
    : (¬ p3516) ∨ p2341 ∨ (¬ p2177) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4556 := h105399;
    (Or.elim h86881 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step121538 (p2341 p3146 p3516 p4443 p4902 : Prop)
    (h105456 : p4902)
    (h86885 : (¬ p3516) ∨ p3146 ∨ (¬ p4443) ∨ p2341 ∨ (¬ p4902))
    : (¬ p3516) ∨ p2341 ∨ (¬ p4443) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4902 := h105456;
    (Or.elim h86885 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121540 (p2319 p2396 p3309 p3516 p5022 : Prop)
    (h105470 : p5022)
    (h86887 : (¬ p3516) ∨ p2396 ∨ (¬ p2319) ∨ (¬ p5022) ∨ p3309)
    : (¬ p3516) ∨ (¬ p2319) ∨ p2396 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5022 := h105470;
    (Or.elim h86887 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step121542 (p2341 p2528 p3516 p4420 p4443 : Prop)
    (h105707 : p4420)
    (h86895 : (¬ p3516) ∨ p2528 ∨ (¬ p4443) ∨ p2341 ∨ (¬ p4420))
    : (¬ p3516) ∨ p2341 ∨ p2528 ∨ (¬ p4443) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4420 := h105707;
    (Or.elim h86895 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121545 (p2427 p2995 p3246 p3516 p4066 p4705 : Prop)
    (h106238 : p4705)
    (h86905 : (¬ p3516) ∨ p3246 ∨ (¬ p4066) ∨ (¬ p2995) ∨ (¬ p4705) ∨ p2427)
    : (¬ p3516) ∨ (¬ p4066) ∨ (¬ p2995) ∨ p3246 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    (Or.elim h86905 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u4 r4)))))))))))))

theorem step121546 (p2427 p3246 p3516 p4539 p4988 : Prop)
    (h105395 : p4539)
    (h86906 : (¬ p3516) ∨ p3246 ∨ p2427 ∨ (¬ p4539) ∨ (¬ p4988))
    : (¬ p3516) ∨ (¬ p4988) ∨ p3246 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4539 := h105395;
    (Or.elim h86906 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121553 (p2143 p2751 p2901 p2992 p3051 p4392 : Prop)
    (h106343 : p2751)
    (h86925 : (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4392) ∨ p3051 ∨ (¬ p2143) ∨ (¬ p2751))
    : p3051 ∨ (¬ p2143) ∨ (¬ p4392) ∨ (¬ p2901) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    (Or.elim h86925 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121554 (p2166 p2619 p3367 p3371 p4392 p4749 : Prop)
    (h105432 : p4749)
    (h86927 : (¬ p3371) ∨ p2619 ∨ (¬ p4749) ∨ (¬ p4392) ∨ p3367 ∨ (¬ p2166))
    : (¬ p3371) ∨ p2619 ∨ (¬ p4392) ∨ p3367 ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3371 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4749 := h105432;
    (Or.elim h86927 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step121556 (p2192 p2860 p3367 p3371 p4392 p4749 : Prop)
    (h105432 : p4749)
    (h86929 : p2860 ∨ (¬ p3371) ∨ p3367 ∨ (¬ p2192) ∨ (¬ p4749) ∨ (¬ p4392))
    : p2860 ∨ (¬ p3371) ∨ p3367 ∨ (¬ p4392) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4749 := h105432;
    (Or.elim h86929 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step121557 (p2177 p2437 p2630 p2696 p3399 p3527 p4276 p4733 : Prop)
    (h105430 : p4733)
    (h105516 : p4276)
    (h86930 : p3399 ∨ (¬ p4733) ∨ p3527 ∨ (¬ p2177) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p4276) ∨ (¬ p2437))
    : p3527 ∨ p3399 ∨ (¬ p2696) ∨ (¬ p2177) ∨ (¬ p2630) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4733 := h105430;
    let u7 : p4276 := h105516;
    (Or.elim h86930 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step121559 (p2145 p2156 p2177 p2274 p2630 p2696 p3083 p4420 : Prop)
    (h105707 : p4420)
    (h86937 : (¬ p3083) ∨ p2274 ∨ (¬ p2145) ∨ p2156 ∨ p2177 ∨ (¬ p2696) ∨ (¬ p4420) ∨ (¬ p2630))
    : (¬ p2696) ∨ (¬ p2630) ∨ p2274 ∨ p2177 ∨ (¬ p3083) ∨ (¬ p2145) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4420 := h105707;
    (Or.elim h86937 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step121560 (p2187 p2274 p2307 p2630 p2696 p2787 p3083 p4596 : Prop)
    (h105374 : p2787)
    (h86939 : (¬ p3083) ∨ p2307 ∨ (¬ p2630) ∨ (¬ p2787) ∨ (¬ p4596) ∨ p2187 ∨ (¬ p2274) ∨ (¬ p2696))
    : (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2274) ∨ p2307 ∨ p2187 ∨ (¬ p4596) ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2787 := h105374;
    (Or.elim h86939 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step121561 (p2145 p2177 p2437 p2630 p2696 p2881 p3051 p4276 : Prop)
    (h105516 : p4276)
    (h86940 : p2881 ∨ (¬ p2437) ∨ (¬ p2177) ∨ (¬ p2630) ∨ (¬ p2145) ∨ (¬ p4276) ∨ (¬ p2696) ∨ p3051)
    : (¬ p2696) ∨ (¬ p2145) ∨ (¬ p2437) ∨ p2881 ∨ (¬ p2177) ∨ p3051 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4276 := h105516;
    (Or.elim h86940 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (u5 r6)))))))))))))))))

theorem step121563 (p2396 p2630 p2696 p3093 p3309 p3343 p4638 p4733 : Prop)
    (h105430 : p4733)
    (h105409 : p4638)
    (h86942 : (¬ p3343) ∨ (¬ p4638) ∨ p2396 ∨ p3093 ∨ (¬ p2630) ∨ p3309 ∨ (¬ p4733) ∨ (¬ p2696))
    : (¬ p2696) ∨ p3093 ∨ (¬ p2630) ∨ p3309 ∨ (¬ p3343) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4733 := h105430;
    let u7 : p4638 := h105409;
    (Or.elim h86942 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step121567 (p2220 p2363 p2630 p2696 p2753 p3083 p3146 p3645 p4596 p4877 : Prop)
    (h105451 : p4877)
    (h86952 : (¬ p2753) ∨ p3146 ∨ (¬ p2363) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p4877) ∨ (¬ p3645) ∨ p2220 ∨ (¬ p4596) ∨ (¬ p3083))
    : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3083) ∨ p3146 ∨ (¬ p4596) ∨ (¬ p2630) ∨ p2220 ∨ (¬ p3645) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4877 := h105451;
    (Or.elim h86952 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step121568 (p2210 p2437 p2630 p2696 p2753 p3093 p3309 p4276 p4877 : Prop)
    (h105516 : p4276)
    (h105451 : p4877)
    (h86953 : p3093 ∨ p3309 ∨ (¬ p2696) ∨ (¬ p2437) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p4276) ∨ (¬ p2210) ∨ (¬ p2630))
    : (¬ p2210) ∨ (¬ p2630) ∨ p3093 ∨ (¬ p2437) ∨ p3309 ∨ (¬ p2696) ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4276 := h105516;
    let u8 : p4877 := h105451;
    (Or.elim h86953 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step121571 (p2630 p2651 p2745 p2946 p2992 : Prop)
    (h105523 : p2745)
    (h86966 : p2992 ∨ (¬ p2946) ∨ (¬ p2745) ∨ p2651 ∨ (¬ p2630))
    : (¬ p2630) ∨ p2992 ∨ (¬ p2946) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    (Or.elim h86966 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step121580 (p2177 p2254 p2630 p2651 p3005 p3093 p3309 p4041 : Prop)
    (h105366 : p2254)
    (h86990 : (¬ p3309) ∨ (¬ p4041) ∨ p2651 ∨ (¬ p2177) ∨ p3005 ∨ (¬ p2254) ∨ (¬ p2630) ∨ (¬ p3093))
    : p3005 ∨ p2651 ∨ (¬ p2177) ∨ (¬ p2630) ∨ (¬ p3309) ∨ (¬ p3093) ∨ (¬ p4041) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h86990 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step121581 (p2210 p2254 p2630 p2651 p2881 p2891 p3005 p4041 : Prop)
    (h105366 : p2254)
    (h86993 : (¬ p2891) ∨ (¬ p2881) ∨ (¬ p2630) ∨ (¬ p2210) ∨ (¬ p2254) ∨ p3005 ∨ (¬ p4041) ∨ p2651)
    : p3005 ∨ (¬ p4041) ∨ (¬ p2891) ∨ p2651 ∨ (¬ p2881) ∨ (¬ p2630) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h86993 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step121586 (p2493 p2630 p2797 p4389 p4814 : Prop)
    (h105440 : p4814)
    (h87035 : p2797 ∨ (¬ p4389) ∨ (¬ p2493) ∨ (¬ p2630) ∨ (¬ p4814))
    : p2797 ∨ (¬ p2630) ∨ (¬ p2493) ∨ (¬ p4389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4814 := h105440;
    (Or.elim h87035 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121587 (p2573 p2630 p2665 p2797 p4389 : Prop)
    (h105373 : p2665)
    (h87037 : p2797 ∨ (¬ p4389) ∨ (¬ p2573) ∨ (¬ p2665) ∨ (¬ p2630))
    : p2797 ∨ (¬ p2630) ∨ (¬ p2573) ∨ (¬ p4389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2665 := h105373;
    (Or.elim h87037 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121593 (p2470 p2509 p2630 p2656 p2745 p3402 : Prop)
    (h105523 : p2745)
    (h48258 : (¬ p2470) ∨ (¬ p2509) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3402))
    : (¬ p2509) ∨ (¬ p3402) ∨ (¬ p2630) ∨ (¬ p2470) ∨ (¬ p2656) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2745 := h105523;
    (Or.elim h48258 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step121595 (p2220 p2264 p2459 p2630 p2656 p2807 p3969 p4399 p5122 : Prop)
    (h105483 : p5122)
    (h87072 : (¬ p3969) ∨ p2264 ∨ (¬ p5122) ∨ (¬ p2220) ∨ (¬ p2630) ∨ (¬ p2656) ∨ p2807 ∨ (¬ p4399) ∨ p2459)
    : (¬ p3969) ∨ (¬ p2220) ∨ p2807 ∨ p2264 ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p4399) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5122 := h105483;
    (Or.elim h87072 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u7 r7)))))))))))))))))))

theorem step121598 (p2437 p2630 p2745 p2922 p3402 : Prop)
    (h105523 : p2745)
    (h87089 : (¬ p3402) ∨ (¬ p2437) ∨ (¬ p2745) ∨ p2922 ∨ (¬ p2630))
    : (¬ p2630) ∨ p2922 ∨ (¬ p2437) ∨ (¬ p3402) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    (Or.elim h87089 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step121605 (p2630 p2685 p2922 p3575 p4155 p4814 : Prop)
    (h105440 : p4814)
    (h87104 : (¬ p2922) ∨ (¬ p4155) ∨ (¬ p3575) ∨ (¬ p4814) ∨ (¬ p2630) ∨ p2685)
    : p2685 ∨ (¬ p3575) ∨ (¬ p4155) ∨ (¬ p2630) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4814 := h105440;
    (Or.elim h87104 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step121608 (p2553 p2685 p2797 p4973 : Prop)
    (h105835 : p4973)
    (h87124 : (¬ p2553) ∨ (¬ p2797) ∨ p2685 ∨ (¬ p4973))
    : (¬ p2797) ∨ p2685 ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4973 := h105835;
    (Or.elim h87124 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step121610 (p2122 p2220 p2331 p2373 p2396 p2982 p3366 p3519 p4236 p4328 p4376 p4395 p4399 : Prop)
    (h106320 : p4376)
    (h87141 : p2331 ∨ (¬ p4328) ∨ (¬ p4399) ∨ (¬ p3519) ∨ (¬ p4236) ∨ (¬ p3366) ∨ p2396 ∨ (¬ p4395) ∨ (¬ p2982) ∨ (¬ p2220) ∨ p2373 ∨ (¬ p4376) ∨ p2122)
    : p2373 ∨ (¬ p2220) ∨ p2396 ∨ p2331 ∨ p2122 ∨ (¬ p4395) ∨ (¬ p3366) ∨ (¬ p2982) ∨ (¬ p4236) ∨ (¬ p4399) ∨ (¬ p4328) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4376 := h106320;
    (Or.elim h87141 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u0 q10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u12))) (fun r11 => (False.elim (u4 r11)))))))))))))))))))))))))))

theorem step121611 (p2630 p2696 p2774 p4328 p4975 : Prop)
    (h105464 : p4975)
    (h87143 : (¬ p2774) ∨ (¬ p4328) ∨ (¬ p4975) ∨ p2630 ∨ p2696)
    : (¬ p2774) ∨ p2630 ∨ p2696 ∨ (¬ p4328) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4975 := h105464;
    (Or.elim h87143 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step121613 (p2122 p2396 p3246 p3872 p4328 p4564 : Prop)
    (h105401 : p4564)
    (h87153 : (¬ p3246) ∨ (¬ p4328) ∨ p2396 ∨ p2122 ∨ (¬ p3872) ∨ (¬ p4564))
    : (¬ p3246) ∨ (¬ p4328) ∨ p2122 ∨ p2396 ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4564 := h105401;
    (Or.elim h87153 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121614 (p2651 p2737 p2829 p3361 p4328 p4975 : Prop)
    (h105464 : p4975)
    (h87163 : (¬ p2829) ∨ p2737 ∨ (¬ p4328) ∨ p2651 ∨ (¬ p3361) ∨ (¬ p4975))
    : (¬ p3361) ∨ (¬ p2829) ∨ (¬ p4328) ∨ p2651 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3361 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4975 := h105464;
    (Or.elim h87163 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121620 (p2156 p2745 p2860 p2957 p2992 p4313 : Prop)
    (h105523 : p2745)
    (h87188 : p2992 ∨ (¬ p4313) ∨ (¬ p2745) ∨ (¬ p2860) ∨ (¬ p2957) ∨ p2156)
    : (¬ p4313) ∨ p2156 ∨ (¬ p2860) ∨ (¬ p2957) ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2745 := h105523;
    (Or.elim h87188 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u1 r4)))))))))))))

theorem step121621 (p2383 p2668 p2807 p3019 p3983 p4652 : Prop)
    (h105413 : p4652)
    (h87213 : (¬ p2668) ∨ (¬ p3983) ∨ (¬ p3019) ∨ p2383 ∨ (¬ p2807) ∨ (¬ p4652))
    : (¬ p3983) ∨ p2383 ∨ (¬ p2807) ∨ (¬ p2668) ∨ (¬ p3019) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3983 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4652 := h105413;
    (Or.elim h87213 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121639 (p2241 p2459 p2470 p2528 p2992 p3156 p4902 p5193 : Prop)
    (h105456 : p4902)
    (h105488 : p5193)
    (h87276 : (¬ p2992) ∨ p2470 ∨ (¬ p2459) ∨ (¬ p2241) ∨ p2528 ∨ (¬ p3156) ∨ (¬ p4902) ∨ (¬ p5193))
    : (¬ p3156) ∨ (¬ p2992) ∨ (¬ p2241) ∨ p2528 ∨ (¬ p2459) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4902 := h105456;
    let u7 : p5193 := h105488;
    (Or.elim h87276 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121640 (p2470 p2528 p3073 p3453 p5194 : Prop)
    (h105489 : p5194)
    (h87278 : (¬ p2470) ∨ p3073 ∨ (¬ p2528) ∨ (¬ p3453) ∨ (¬ p5194))
    : (¬ p3453) ∨ (¬ p2470) ∨ p3073 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3453 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5194 := h105489;
    (Or.elim h87278 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121642 (p2406 p2528 p3073 p3453 p4608 : Prop)
    (h105540 : p4608)
    (h87282 : p3073 ∨ (¬ p2406) ∨ (¬ p3453) ∨ (¬ p2528) ∨ (¬ p4608))
    : (¬ p2406) ∨ p3073 ∨ (¬ p3453) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4608 := h105540;
    (Or.elim h87282 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121649 (p2386 p2406 p2505 p3319 p3654 p4717 : Prop)
    (h105424 : p4717)
    (h87296 : (¬ p3319) ∨ p3654 ∨ (¬ p2386) ∨ (¬ p4717) ∨ (¬ p2505) ∨ p2406)
    : p2406 ∨ (¬ p3319) ∨ (¬ p2386) ∨ p3654 ∨ (¬ p2505) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4717 := h105424;
    (Or.elim h87296 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step121651 (p2504 p4757 p4976 : Prop)
    (h105465 : p4976)
    (h29318 : (¬ p2504) ∨ p4757 ∨ (¬ p4976))
    : (¬ p2504) ∨ p4757 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2504 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4757) := (fun h => hn (Or.inr h));
    let u2 : p4976 := h105465;
    (Or.elim h29318 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step121654 (p2307 p2504 p2584 p2665 p3016 p3309 : Prop)
    (h105373 : p2665)
    (h87305 : (¬ p2307) ∨ p3309 ∨ p3016 ∨ (¬ p2504) ∨ (¬ p2584) ∨ (¬ p2665))
    : (¬ p2584) ∨ (¬ p2307) ∨ p3016 ∨ (¬ p2504) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2584 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2665 := h105373;
    (Or.elim h87305 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121658 (p2406 p3093 p3379 p4717 : Prop)
    (h105424 : p4717)
    (h87317 : p3379 ∨ (¬ p3093) ∨ p2406 ∨ (¬ p4717))
    : p2406 ∨ p3379 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4717 := h105424;
    (Or.elim h87317 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step121659 (p2504 p3016 p3093 p3379 p4814 : Prop)
    (h105440 : p4814)
    (h87318 : (¬ p3093) ∨ p3379 ∨ p3016 ∨ (¬ p2504) ∨ (¬ p4814))
    : (¬ p3093) ∨ p3379 ∨ (¬ p2504) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4814 := h105440;
    (Or.elim h87318 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121660 (p2504 p3093 p3379 p3422 p5217 : Prop)
    (h105493 : p5217)
    (h87319 : (¬ p3093) ∨ p3379 ∨ p3422 ∨ (¬ p5217) ∨ (¬ p2504))
    : p3422 ∨ p3379 ∨ (¬ p3093) ∨ (¬ p2504) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5217 := h105493;
    (Or.elim h87319 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121663 (p2493 p2573 p2630 p2656 p2745 p3402 : Prop)
    (h105523 : p2745)
    (h87360 : (¬ p3402) ∨ (¬ p2573) ∨ p2493 ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p2630))
    : (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2630) ∨ (¬ p3402) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2745 := h105523;
    (Or.elim h87360 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step121665 (p2255 p2437 p2651 p2922 p3402 : Prop)
    (h105367 : p2255)
    (h87365 : p2922 ∨ (¬ p2437) ∨ (¬ p3402) ∨ (¬ p2255) ∨ (¬ p2651))
    : p2922 ∨ (¬ p2437) ∨ (¬ p3402) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2255 := h105367;
    (Or.elim h87365 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121669 (p2230 p2427 p2573 p3096 p4558 : Prop)
    (h105400 : p4558)
    (h87394 : (¬ p2427) ∨ p2573 ∨ (¬ p4558) ∨ (¬ p3096) ∨ (¬ p2230))
    : p2573 ∨ (¬ p2230) ∨ (¬ p3096) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4558 := h105400;
    (Or.elim h87394 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121671 (p2230 p2573 p2982 p3096 p5046 : Prop)
    (h105472 : p5046)
    (h87403 : (¬ p2982) ∨ (¬ p2230) ∨ (¬ p3096) ∨ p2573 ∨ (¬ p5046))
    : p2573 ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5046 := h105472;
    (Or.elim h87403 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121672 (p2230 p2373 p2573 p3096 p4509 : Prop)
    (h105392 : p4509)
    (h87404 : (¬ p2373) ∨ p2573 ∨ (¬ p4509) ∨ (¬ p3096) ∨ (¬ p2230))
    : p2573 ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4509 := h105392;
    (Or.elim h87404 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121673 (p2230 p2284 p2573 p3096 p4705 : Prop)
    (h106238 : p4705)
    (h87407 : (¬ p2284) ∨ (¬ p2230) ∨ (¬ p4705) ∨ (¬ p3096) ∨ p2573)
    : p2573 ∨ (¬ p2284) ∨ (¬ p2230) ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4705 := h106238;
    (Or.elim h87407 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step121674 (p2192 p2230 p2573 p3096 p4632 : Prop)
    (h106257 : p4632)
    (h87408 : (¬ p2192) ∨ (¬ p2230) ∨ (¬ p3096) ∨ p2573 ∨ (¬ p4632))
    : p2573 ∨ (¬ p2192) ∨ (¬ p3096) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4632 := h106257;
    (Or.elim h87408 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121682 (p2230 p2373 p2470 p4434 : Prop)
    (h106144 : p4434)
    (h87445 : (¬ p2373) ∨ (¬ p2230) ∨ p2470 ∨ (¬ p4434))
    : p2470 ∨ (¬ p2230) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4434 := h106144;
    (Or.elim h87445 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step121687 (p2230 p2417 p3516 p4644 p5197 : Prop)
    (h105411 : p4644)
    (h87489 : (¬ p2417) ∨ (¬ p2230) ∨ (¬ p4644) ∨ p3516 ∨ (¬ p5197))
    : (¬ p5197) ∨ (¬ p2417) ∨ p3516 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5197 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4644 := h105411;
    (Or.elim h87489 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step121688 (p2230 p2352 p2383 p2577 p4715 : Prop)
    (h105423 : p4715)
    (h87491 : (¬ p2577) ∨ (¬ p2352) ∨ p2383 ∨ (¬ p4715) ∨ (¬ p2230))
    : (¬ p2577) ∨ (¬ p2230) ∨ (¬ p2352) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    (Or.elim h87491 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121689 (p2230 p2307 p2553 p2577 p4715 : Prop)
    (h105423 : p4715)
    (h87492 : (¬ p2553) ∨ (¬ p2230) ∨ (¬ p2577) ∨ (¬ p4715) ∨ p2307)
    : (¬ p2577) ∨ p2307 ∨ (¬ p2553) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    (Or.elim h87492 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step121690 (p2187 p2230 p2563 p2608 p2737 p3005 p4774 p5190 : Prop)
    (h105487 : p5190)
    (h87494 : p3005 ∨ p2608 ∨ p2737 ∨ (¬ p4774) ∨ (¬ p2187) ∨ (¬ p2563) ∨ (¬ p5190) ∨ (¬ p2230))
    : p3005 ∨ p2737 ∨ (¬ p2563) ∨ (¬ p4774) ∨ (¬ p2187) ∨ p2608 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5190 := h105487;
    (Or.elim h87494 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step121691 (p2230 p2577 p3564 p3654 p4715 : Prop)
    (h105423 : p4715)
    (h87495 : (¬ p3564) ∨ p3654 ∨ (¬ p4715) ∨ (¬ p2577) ∨ (¬ p2230))
    : (¬ p2577) ∨ (¬ p3564) ∨ p3654 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    (Or.elim h87495 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121693 (p2630 p2707 p2737 p4325 p4652 : Prop)
    (h105413 : p4652)
    (h87507 : (¬ p2707) ∨ p2737 ∨ p2630 ∨ (¬ p4652) ∨ (¬ p4325))
    : (¬ p2707) ∨ (¬ p4325) ∨ p2737 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4652 := h105413;
    (Or.elim h87507 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121696 (p2630 p2696 p3425 p4325 p4652 : Prop)
    (h105413 : p4652)
    (h87530 : p3425 ∨ (¬ p4652) ∨ p2696 ∨ (¬ p4325) ∨ p2630)
    : p3425 ∨ p2630 ∨ (¬ p4325) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4652 := h105413;
    (Or.elim h87530 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step121703 (p2312 p2449 p2668 p3516 p4067 p4405 : Prop)
    (h105512 : p4405)
    (h87560 : (¬ p3516) ∨ (¬ p2312) ∨ p2449 ∨ (¬ p4405) ∨ (¬ p4067) ∨ (¬ p2668))
    : (¬ p3516) ∨ (¬ p2668) ∨ p2449 ∨ (¬ p4067) ∨ (¬ p2312) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4405 := h105512;
    (Or.elim h87560 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step121704 (p2295 p2312 p2493 p2922 p4279 p4976 : Prop)
    (h105465 : p4976)
    (h87561 : (¬ p2312) ∨ (¬ p2295) ∨ p2922 ∨ (¬ p4976) ∨ (¬ p4279) ∨ (¬ p2493))
    : (¬ p4279) ∨ (¬ p2312) ∨ (¬ p2493) ∨ p2922 ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4279 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4976 := h105465;
    (Or.elim h87561 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step121705 (p2311 p2396 p2553 p2581 p3516 : Prop)
    (h105371 : p2581)
    (h87563 : (¬ p2553) ∨ (¬ p2396) ∨ (¬ p2581) ∨ (¬ p2311) ∨ p3516)
    : (¬ p2311) ∨ (¬ p2553) ∨ p3516 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2311 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2581 := h105371;
    (Or.elim h87563 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step121708 (p2311 p2787 p5260 : Prop)
    (h105374 : p2787)
    (h21376 : (¬ p2311) ∨ (¬ p2787) ∨ p5260)
    : (¬ p2311) ∨ p5260 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2311 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5260) := (fun h => hn (Or.inr h));
    let u2 : p2787 := h105374;
    (Or.elim h21376 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step121709 (p2311 p2383 p2396 p3516 p4405 : Prop)
    (h105512 : p4405)
    (h87571 : p3516 ∨ (¬ p2396) ∨ (¬ p2383) ∨ (¬ p4405) ∨ (¬ p2311))
    : (¬ p2383) ∨ p3516 ∨ (¬ p2396) ∨ (¬ p2311) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    (Or.elim h87571 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121712 (p2177 p2311 p2341 p3654 p4624 : Prop)
    (h105408 : p4624)
    (h87582 : p2341 ∨ (¬ p3654) ∨ (¬ p2311) ∨ (¬ p2177) ∨ (¬ p4624))
    : (¬ p3654) ∨ p2341 ∨ (¬ p2311) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    (Or.elim h87582 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121720 (p2331 p2651 p3422 p3984 p4750 : Prop)
    (h105433 : p4750)
    (h87611 : (¬ p2331) ∨ p3422 ∨ (¬ p3984) ∨ p2651 ∨ (¬ p4750))
    : p3422 ∨ p2651 ∨ (¬ p2331) ∨ (¬ p3984) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    (Or.elim h87611 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121727 (p2166 p2220 p2573 p3904 p4034 p4717 : Prop)
    (h105424 : p4717)
    (h87644 : p2220 ∨ (¬ p2573) ∨ (¬ p2166) ∨ (¬ p4034) ∨ (¬ p3904) ∨ (¬ p4717))
    : p2220 ∨ (¬ p2166) ∨ (¬ p3904) ∨ (¬ p2573) ∨ (¬ p4034) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4717 := h105424;
    (Or.elim h87644 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121734 (p2241 p2352 p2383 p2449 p2577 p2630 p2996 p3347 p3487 p3564 p4625 : Prop)
    (h106455 : p4625)
    (h87662 : p2996 ∨ (¬ p2241) ∨ (¬ p2352) ∨ (¬ p3487) ∨ p2383 ∨ (¬ p2449) ∨ (¬ p2577) ∨ (¬ p4625) ∨ p3564 ∨ (¬ p3347) ∨ p2630)
    : p2383 ∨ (¬ p2577) ∨ (¬ p3347) ∨ (¬ p3487) ∨ (¬ p2352) ∨ (¬ p2449) ∨ p2630 ∨ p3564 ∨ p2996 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2383) := (fun h => hn (Or.inl h));
    let u1 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4625 := h106455;
    (Or.elim h87662 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (u6 r9)))))))))))))))))))))))

theorem step121738 (p2493 p2651 p2946 p3487 p4241 p4715 : Prop)
    (h105423 : p4715)
    (h87676 : (¬ p3487) ∨ p2651 ∨ p2493 ∨ (¬ p4241) ∨ (¬ p2946) ∨ (¬ p4715))
    : p2651 ∨ p2493 ∨ (¬ p3487) ∨ (¬ p4241) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4715 := h105423;
    (Or.elim h87676 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121743 (p2177 p2249 p2307 p2417 p2641 p2651 p2922 p3487 p3567 p4666 : Prop)
    (h105658 : p4666)
    (h106513 : p2249)
    (h87684 : (¬ p3567) ∨ p2417 ∨ (¬ p3487) ∨ p2922 ∨ (¬ p4666) ∨ p2651 ∨ (¬ p2307) ∨ (¬ p2177) ∨ (¬ p2641) ∨ (¬ p2249))
    : p2922 ∨ (¬ p2307) ∨ (¬ p3567) ∨ (¬ p2641) ∨ p2417 ∨ (¬ p3487) ∨ p2651 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4666 := h105658;
    let u9 : p2249 := h106513;
    (Or.elim h87684 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step121749 (p2248 p2363 p2651 p2850 p2982 p3093 p3923 p4343 p4450 : Prop)
    (h105365 : p2248)
    (h87715 : p2363 ∨ p3093 ∨ (¬ p2651) ∨ (¬ p3923) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p4343) ∨ (¬ p2248) ∨ (¬ p4450))
    : (¬ p4343) ∨ (¬ p2850) ∨ p3093 ∨ p2363 ∨ (¬ p2651) ∨ (¬ p2982) ∨ (¬ p3923) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2248 := h105365;
    (Or.elim h87715 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step121751 (p2177 p2230 p2850 p3201 p3399 p3527 p3905 p4001 p4559 p4736 : Prop)
    (h105431 : p4736)
    (h105701 : p4559)
    (h87720 : (¬ p3527) ∨ (¬ p2850) ∨ (¬ p4559) ∨ p3201 ∨ p2230 ∨ p2177 ∨ (¬ p3905) ∨ (¬ p3399) ∨ (¬ p4736) ∨ (¬ p4001))
    : p3201 ∨ (¬ p3527) ∨ (¬ p3905) ∨ (¬ p2850) ∨ (¬ p3399) ∨ (¬ p4001) ∨ p2177 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    let u9 : p4559 := h105701;
    (Or.elim h87720 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step121754 (p2230 p2241 p2744 p2850 p3366 p3399 p3527 p3641 p3905 p4438 : Prop)
    (h106503 : p2744)
    (h87726 : (¬ p2850) ∨ p3641 ∨ (¬ p3905) ∨ p2241 ∨ (¬ p4438) ∨ (¬ p2744) ∨ (¬ p3399) ∨ (¬ p3366) ∨ p2230 ∨ (¬ p3527))
    : p3641 ∨ (¬ p2850) ∨ (¬ p3399) ∨ (¬ p4438) ∨ p2230 ∨ (¬ p3527) ∨ (¬ p3366) ∨ p2241 ∨ (¬ p3905) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    (Or.elim h87726 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step121755 (p2363 p2427 p2598 p2850 p2881 p3093 p3923 p4733 : Prop)
    (h105430 : p4733)
    (h87727 : (¬ p2850) ∨ (¬ p2598) ∨ (¬ p3923) ∨ (¬ p2427) ∨ p2363 ∨ p3093 ∨ (¬ p4733) ∨ (¬ p2881))
    : (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2881) ∨ p2363 ∨ (¬ p3923) ∨ p3093 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    (Or.elim h87727 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step121759 (p2295 p2307 p2373 p2598 p2668 p2787 p2850 p4433 : Prop)
    (h106150 : p4433)
    (h105374 : p2787)
    (h87731 : (¬ p2850) ∨ (¬ p2598) ∨ (¬ p2373) ∨ (¬ p2787) ∨ (¬ p4433) ∨ p2307 ∨ (¬ p2295) ∨ p2668)
    : (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2373) ∨ p2307 ∨ (¬ p2295) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4433 := h106150;
    let u7 : p2787 := h105374;
    (Or.elim h87731 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (u5 r6)))))))))))))))))

theorem step121762 (p2230 p2363 p2383 p2459 p2781 p2850 p3641 p3693 p3905 p4905 : Prop)
    (h105995 : p4905)
    (h87739 : p3641 ∨ (¬ p2850) ∨ p2230 ∨ p2459 ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p4905) ∨ (¬ p3905) ∨ (¬ p3693) ∨ (¬ p2363))
    : p3641 ∨ (¬ p2850) ∨ (¬ p2383) ∨ (¬ p2363) ∨ p2459 ∨ (¬ p3693) ∨ (¬ p3905) ∨ p2230 ∨ (¬ p2781) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4905 := h105995;
    (Or.elim h87739 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step121768 (p2220 p2850 p3641 p3693 p4539 : Prop)
    (h105395 : p4539)
    (h87775 : p3641 ∨ (¬ p2850) ∨ (¬ p3693) ∨ (¬ p2220) ∨ (¬ p4539))
    : p3641 ∨ (¬ p2220) ∨ (¬ p2850) ∨ (¬ p3693) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4539 := h105395;
    (Or.elim h87775 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121769 (p2373 p2850 p3201 p3988 p4001 p4555 : Prop)
    (h105542 : p4555)
    (h87780 : (¬ p4001) ∨ (¬ p2850) ∨ (¬ p4555) ∨ (¬ p2373) ∨ p3201 ∨ (¬ p3988))
    : p3201 ∨ (¬ p2850) ∨ (¬ p4001) ∨ (¬ p2373) ∨ (¬ p3988) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4555 := h105542;
    (Or.elim h87780 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step121773 (p2177 p2427 p2598 p2850 p3399 p3527 p4556 p4733 : Prop)
    (h105430 : p4733)
    (h105399 : p4556)
    (h87786 : p3399 ∨ (¬ p2598) ∨ p3527 ∨ (¬ p4733) ∨ (¬ p2427) ∨ (¬ p2850) ∨ (¬ p4556) ∨ (¬ p2177))
    : p3399 ∨ (¬ p2850) ∨ (¬ p2598) ∨ p3527 ∨ (¬ p2427) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4733 := h105430;
    let u7 : p4556 := h105399;
    (Or.elim h87786 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step121775 (p2727 p2850 p2957 p2992 p4109 p4753 : Prop)
    (h105514 : p4753)
    (h87802 : p2992 ∨ (¬ p2850) ∨ (¬ p2957) ∨ (¬ p4109) ∨ (¬ p4753) ∨ (¬ p2727))
    : (¬ p2957) ∨ p2992 ∨ (¬ p2850) ∨ (¬ p2727) ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4753 := h105514;
    (Or.elim h87802 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step121779 (p2598 p2850 p3425 p4106 p4644 : Prop)
    (h105411 : p4644)
    (h61379 : (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3425) ∨ (¬ p4106) ∨ (¬ p4644))
    : (¬ p4106) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4106 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4644 := h105411;
    (Or.elim h61379 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121781 (p2210 p2850 p3379 p4034 p5214 : Prop)
    (h105492 : p5214)
    (h87820 : p2210 ∨ (¬ p2850) ∨ (¬ p3379) ∨ (¬ p4034) ∨ (¬ p5214))
    : (¬ p2850) ∨ p2210 ∨ (¬ p3379) ∨ (¬ p4034) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5214 := h105492;
    (Or.elim h87820 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121785 (p2177 p2248 p2307 p2459 p2651 p2850 p2982 p4343 p4450 p5015 : Prop)
    (h105365 : p2248)
    (h87831 : (¬ p2982) ∨ p2459 ∨ p2307 ∨ (¬ p2248) ∨ (¬ p5015) ∨ (¬ p4450) ∨ (¬ p2651) ∨ p2177 ∨ (¬ p4343) ∨ (¬ p2850))
    : (¬ p4343) ∨ (¬ p2651) ∨ p2459 ∨ (¬ p4450) ∨ p2307 ∨ p2177 ∨ (¬ p5015) ∨ (¬ p2982) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2248 := h105365;
    (Or.elim h87831 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step121786 (p2459 p2598 p2850 p2982 p3399 p3527 p4450 p4733 : Prop)
    (h105430 : p4733)
    (h87832 : (¬ p2982) ∨ p3527 ∨ (¬ p4450) ∨ (¬ p2598) ∨ p2459 ∨ p3399 ∨ (¬ p4733) ∨ (¬ p2850))
    : (¬ p2850) ∨ (¬ p2598) ∨ (¬ p2982) ∨ (¬ p4450) ∨ p2459 ∨ p3527 ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    (Or.elim h87832 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step121788 (p2177 p2307 p2459 p2598 p2850 p2982 p4450 p4733 p5015 : Prop)
    (h105430 : p4733)
    (h87834 : (¬ p2982) ∨ (¬ p4733) ∨ p2307 ∨ (¬ p5015) ∨ p2177 ∨ (¬ p2598) ∨ p2459 ∨ (¬ p2850) ∨ (¬ p4450))
    : (¬ p2598) ∨ (¬ p5015) ∨ (¬ p2982) ∨ p2307 ∨ p2177 ∨ (¬ p4450) ∨ (¬ p2850) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4733 := h105430;
    (Or.elim h87834 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step121790 (p2245 p2264 p2459 p2598 p2807 p2850 p2982 p4450 p4733 : Prop)
    (h105430 : p4733)
    (h87836 : p2264 ∨ p2459 ∨ (¬ p4733) ∨ (¬ p2598) ∨ p2807 ∨ (¬ p4450) ∨ (¬ p2982) ∨ (¬ p2850) ∨ (¬ p2245))
    : (¬ p2850) ∨ p2807 ∨ (¬ p2598) ∨ (¬ p2245) ∨ p2264 ∨ p2459 ∨ (¬ p4450) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4733 := h105430;
    (Or.elim h87836 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step121793 (p2252 p2331 p2363 p2598 p2668 p2750 p2753 p2850 p2982 p4450 : Prop)
    (h106345 : p2750)
    (h87853 : (¬ p2753) ∨ p2363 ∨ p2331 ∨ (¬ p2850) ∨ (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2982) ∨ (¬ p4450) ∨ (¬ p2750) ∨ p2668)
    : (¬ p2850) ∨ (¬ p2598) ∨ p2668 ∨ (¬ p2982) ∨ p2331 ∨ (¬ p2753) ∨ p2363 ∨ (¬ p2252) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2750 := h106345;
    (Or.elim h87853 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u2 r8)))))))))))))))))))))

theorem step121795 (p2406 p2737 p2850 p4257 p4749 : Prop)
    (h105432 : p4749)
    (h87863 : (¬ p2737) ∨ (¬ p2850) ∨ (¬ p4749) ∨ (¬ p4257) ∨ p2406)
    : (¬ p4257) ∨ (¬ p2737) ∨ p2406 ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4257 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4749 := h105432;
    (Or.elim h87863 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step121796 (p2641 p2667 p2727 p2850 p2962 p4109 p4753 : Prop)
    (h105514 : p4753)
    (h87866 : p2641 ∨ (¬ p2850) ∨ (¬ p4109) ∨ (¬ p4753) ∨ (¬ p2962) ∨ (¬ p2667) ∨ (¬ p2727))
    : (¬ p2850) ∨ (¬ p4109) ∨ p2641 ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4753 := h105514;
    (Or.elim h87866 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step121800 (p2850 p3156 p3641 p3693 p4705 : Prop)
    (h106238 : p4705)
    (h87873 : p3641 ∨ (¬ p3156) ∨ (¬ p4705) ∨ (¬ p2850) ∨ (¬ p3693))
    : p3641 ∨ (¬ p3156) ∨ (¬ p3693) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4705 := h106238;
    (Or.elim h87873 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121801 (p2177 p2230 p2295 p2331 p2850 p3641 p3693 p3905 p4786 p4905 : Prop)
    (h105995 : p4905)
    (h106425 : p4786)
    (h87876 : p3641 ∨ (¬ p2850) ∨ (¬ p4905) ∨ (¬ p4786) ∨ (¬ p2295) ∨ (¬ p3905) ∨ (¬ p3693) ∨ p2230 ∨ (¬ p2177) ∨ (¬ p2331))
    : p3641 ∨ (¬ p3693) ∨ (¬ p3905) ∨ (¬ p2295) ∨ (¬ p2331) ∨ p2230 ∨ (¬ p2177) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4905 := h105995;
    let u9 : p4786 := h106425;
    (Or.elim h87876 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step121805 (p2707 p2850 p3367 p4106 p4644 : Prop)
    (h105411 : p4644)
    (h87882 : p2707 ∨ (¬ p2850) ∨ (¬ p4106) ∨ (¬ p3367) ∨ (¬ p4644))
    : (¬ p4106) ∨ p2707 ∨ (¬ p3367) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4106 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4644 := h105411;
    (Or.elim h87882 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121807 (p2284 p2850 p3096 p3422 p4705 : Prop)
    (h106238 : p4705)
    (h87892 : p3422 ∨ (¬ p2284) ∨ (¬ p3096) ∨ (¬ p4705) ∨ (¬ p2850))
    : (¬ p2850) ∨ p3422 ∨ (¬ p3096) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4705 := h106238;
    (Or.elim h87892 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step121808 (p2850 p2982 p3096 p3422 p5046 : Prop)
    (h105472 : p5046)
    (h87893 : (¬ p2982) ∨ p3422 ∨ (¬ p3096) ∨ (¬ p5046) ∨ (¬ p2850))
    : p3422 ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5046 := h105472;
    (Or.elim h87893 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step121809 (p2156 p2850 p3096 p3370 p3422 p4632 : Prop)
    (h106257 : p4632)
    (h87894 : (¬ p3370) ∨ p3422 ∨ (¬ p4632) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p2156))
    : (¬ p2850) ∨ p3422 ∨ (¬ p3096) ∨ (¬ p2156) ∨ (¬ p3370) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4632 := h106257;
    (Or.elim h87894 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step121810 (p2373 p2850 p3096 p3422 p4509 : Prop)
    (h105392 : p4509)
    (h87895 : p3422 ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p2373) ∨ (¬ p4509))
    : p3422 ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4509 := h105392;
    (Or.elim h87895 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121811 (p2850 p2891 p3201 p4001 p4632 : Prop)
    (h106257 : p4632)
    (h87896 : p3201 ∨ (¬ p2850) ∨ (¬ p2891) ∨ (¬ p4632) ∨ (¬ p4001))
    : (¬ p2850) ∨ p3201 ∨ (¬ p2891) ∨ (¬ p4001) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4632 := h106257;
    (Or.elim h87896 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121813 (p2230 p2341 p2437 p2850 p2930 p3093 p3366 p3527 p3545 p3905 p4343 p4866 : Prop)
    (h106063 : p4866)
    (h105376 : p2930)
    (h87898 : p3093 ∨ (¬ p3905) ∨ (¬ p3545) ∨ (¬ p4343) ∨ (¬ p4866) ∨ (¬ p2850) ∨ p2437 ∨ (¬ p2930) ∨ p2230 ∨ p3527 ∨ (¬ p2341) ∨ (¬ p3366))
    : (¬ p4343) ∨ p2437 ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p2850) ∨ p3093 ∨ (¬ p2341) ∨ (¬ p3545) ∨ p3527 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3545 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4866 := h106063;
    let u11 : p2930 := h105376;
    (Or.elim h87898 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u9 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u8 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u6))) (fun r10 => (False.elim (r10 u2)))))))))))))))))))))))))

theorem step121820 (p2177 p2254 p2417 p2651 p3093 p3201 p3309 p3683 p4666 : Prop)
    (h105366 : p2254)
    (h105658 : p4666)
    (h87920 : p2417 ∨ (¬ p3309) ∨ (¬ p3093) ∨ p2651 ∨ (¬ p4666) ∨ (¬ p2177) ∨ (¬ p3683) ∨ (¬ p2254) ∨ p3201)
    : p3201 ∨ (¬ p3683) ∨ (¬ p3309) ∨ (¬ p2177) ∨ p2417 ∨ p2651 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p4666 := h105658;
    (Or.elim h87920 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u0 r7)))))))))))))))))))

theorem step121824 (p2122 p2177 p2241 p2449 p2573 p2744 p3037 p3366 p3399 p3905 p4390 p4668 : Prop)
    (h106503 : p2744)
    (h105414 : p4668)
    (h87948 : (¬ p2449) ∨ p2122 ∨ (¬ p3905) ∨ p2241 ∨ (¬ p3037) ∨ (¬ p4390) ∨ p2573 ∨ p2177 ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p4668) ∨ (¬ p3399))
    : (¬ p3399) ∨ (¬ p3905) ∨ p2177 ∨ p2573 ∨ p2241 ∨ (¬ p3037) ∨ (¬ p3366) ∨ p2122 ∨ (¬ p2449) ∨ (¬ p4390) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    let u11 : p4668 := h105414;
    (Or.elim h87948 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (False.elim (r10 u0)))))))))))))))))))))))))

theorem step121826 (p3958 p4390 p4889 : Prop)
    (h105378 : p3958)
    (h25032 : (¬ p3958) ∨ (¬ p4390) ∨ p4889)
    : (¬ p4390) ∨ p4889 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4390 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4889) := (fun h => hn (Or.inr h));
    let u2 : p3958 := h105378;
    (Or.elim h25032 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step121828 (p2829 p2850 p3367 p4390 p4717 : Prop)
    (h105424 : p4717)
    (h87960 : (¬ p2829) ∨ (¬ p4390) ∨ p3367 ∨ (¬ p4717) ∨ p2850)
    : (¬ p2829) ∨ p2850 ∨ (¬ p4390) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4717 := h105424;
    (Or.elim h87960 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step121830 (p2493 p2598 p2774 p4390 p5214 : Prop)
    (h105492 : p5214)
    (h87964 : (¬ p2774) ∨ (¬ p4390) ∨ (¬ p5214) ∨ p2493 ∨ p2598)
    : (¬ p2774) ∨ (¬ p4390) ∨ p2598 ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5214 := h105492;
    (Or.elim h87964 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step121831 (p2598 p2774 p2850 p4390 p4717 : Prop)
    (h105424 : p4717)
    (h87965 : (¬ p2774) ∨ (¬ p4390) ∨ (¬ p4717) ∨ p2850 ∨ p2598)
    : (¬ p2774) ∨ p2850 ∨ (¬ p4390) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4717 := h105424;
    (Or.elim h87965 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (u3 r3)))))))))))

theorem step121832 (p2598 p2829 p2850 p3366 p4390 p4717 : Prop)
    (h105424 : p4717)
    (h87966 : (¬ p2829) ∨ (¬ p3366) ∨ (¬ p4717) ∨ (¬ p4390) ∨ p2598 ∨ p2850)
    : (¬ p2829) ∨ p2850 ∨ (¬ p3366) ∨ p2598 ∨ (¬ p4390) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4717 := h105424;
    (Or.elim h87966 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (u1 r4)))))))))))))

theorem step121834 (p2187 p2192 p2590 p2819 p4390 p4632 : Prop)
    (h106257 : p4632)
    (h87969 : (¬ p2192) ∨ (¬ p4632) ∨ (¬ p2187) ∨ (¬ p4390) ∨ p2819 ∨ (¬ p2590))
    : (¬ p4390) ∨ (¬ p2590) ∨ p2819 ∨ (¬ p2192) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4390 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4632 := h106257;
    (Or.elim h87969 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step121854 (p2177 p2341 p2396 p3276 p3346 p3347 p3543 p3680 p3951 p4257 p4793 : Prop)
    (h105438 : p4793)
    (h106536 : p3951)
    (h88051 : p3276 ∨ (¬ p3680) ∨ (¬ p4257) ∨ (¬ p2396) ∨ (¬ p4793) ∨ p2177 ∨ (¬ p3543) ∨ (¬ p3347) ∨ (¬ p3346) ∨ (¬ p3951) ∨ (¬ p2341))
    : (¬ p3680) ∨ (¬ p3543) ∨ p2177 ∨ (¬ p2341) ∨ p3276 ∨ (¬ p2396) ∨ (¬ p3347) ∨ (¬ p3346) ∨ (¬ p4257) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4793 := h105438;
    let u10 : p3951 := h106536;
    (Or.elim h88051 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step121856 (p2577 p5021 p5193 : Prop)
    (h105488 : p5193)
    (h24506 : (¬ p2577) ∨ p5021 ∨ (¬ p5193))
    : (¬ p2577) ∨ p5021 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5021) := (fun h => hn (Or.inr h));
    let u2 : p5193 := h105488;
    (Or.elim h24506 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step121857 (p2241 p2459 p2470 p2528 p2641 p2668 p4133 p5193 : Prop)
    (h105488 : p5193)
    (h105712 : p4133)
    (h88071 : (¬ p2641) ∨ (¬ p2668) ∨ p2470 ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p4133) ∨ p2528)
    : (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2241) ∨ (¬ p2459) ∨ p2470 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5193 := h105488;
    let u7 : p4133 := h105712;
    (Or.elim h88071 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u5 r6)))))))))))))))))

theorem step121858 (p2241 p2573 p3189 p3461 p3564 p4009 p5119 p5193 : Prop)
    (h105488 : p5193)
    (h88072 : (¬ p4009) ∨ (¬ p3189) ∨ (¬ p5193) ∨ p3461 ∨ p2573 ∨ (¬ p5119) ∨ (¬ p2241) ∨ p3564)
    : (¬ p4009) ∨ p3564 ∨ p3461 ∨ p2573 ∨ (¬ p3189) ∨ (¬ p2241) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h88072 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step121860 (p2241 p2352 p2363 p2449 p2573 p2996 p3950 p5193 : Prop)
    (h105488 : p5193)
    (h88074 : p2996 ∨ p2573 ∨ (¬ p2241) ∨ p2352 ∨ p2363 ∨ (¬ p3950) ∨ (¬ p2449) ∨ (¬ p5193))
    : p2996 ∨ p2573 ∨ p2363 ∨ (¬ p2449) ∨ p2352 ∨ (¬ p2241) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h88074 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121862 (p2230 p2427 p3246 p3266 p3707 p3830 p4669 p5193 : Prop)
    (h105488 : p5193)
    (h105415 : p4669)
    (h88078 : p3266 ∨ (¬ p3707) ∨ p2230 ∨ p2427 ∨ (¬ p3830) ∨ (¬ p5193) ∨ (¬ p4669) ∨ p3246)
    : (¬ p3707) ∨ p2230 ∨ (¬ p3830) ∨ p3266 ∨ p2427 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2230) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5193 := h105488;
    let u7 : p4669 := h105415;
    (Or.elim h88078 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u5 r6)))))))))))))))))

theorem step121864 (p2241 p2459 p2630 p2641 p2797 p2911 p3389 p5193 : Prop)
    (h105488 : p5193)
    (h88081 : (¬ p2641) ∨ p2797 ∨ (¬ p2630) ∨ (¬ p2241) ∨ p2459 ∨ p3389 ∨ (¬ p5193) ∨ p2911)
    : p2797 ∨ (¬ p2241) ∨ (¬ p2630) ∨ p2911 ∨ p3389 ∨ p2459 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h88081 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step121865 (p2406 p2651 p2946 p4241 p4811 : Prop)
    (h105633 : p4811)
    (h88082 : (¬ p2946) ∨ p2651 ∨ p2406 ∨ (¬ p4241) ∨ (¬ p4811))
    : p2651 ∨ (¬ p2946) ∨ p2406 ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4811 := h105633;
    (Or.elim h88082 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121866 (p2156 p2284 p2406 p3413 p4031 p4811 : Prop)
    (h105633 : p4811)
    (h88083 : (¬ p2284) ∨ (¬ p4031) ∨ (¬ p3413) ∨ p2156 ∨ p2406 ∨ (¬ p4811))
    : p2156 ∨ (¬ p2284) ∨ (¬ p3413) ∨ p2406 ∨ (¬ p4031) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4811 := h105633;
    (Or.elim h88083 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step121875 (p2254 p2307 p2528 p2651 p3083 p3309 p3319 p4330 p5020 : Prop)
    (h105366 : p2254)
    (h106329 : p4330)
    (h88116 : p2528 ∨ (¬ p3319) ∨ (¬ p2254) ∨ p2651 ∨ (¬ p5020) ∨ p3309 ∨ (¬ p4330) ∨ p3083 ∨ (¬ p2307))
    : p3083 ∨ p2651 ∨ (¬ p5020) ∨ p3309 ∨ p2528 ∨ (¬ p2307) ∨ (¬ p3319) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p4330 := h106329;
    (Or.elim h88116 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step121877 (p2254 p2528 p2608 p2651 p2829 p3083 p3483 p4330 : Prop)
    (h105366 : p2254)
    (h106329 : p4330)
    (h88118 : (¬ p3483) ∨ p2528 ∨ (¬ p2829) ∨ (¬ p2608) ∨ (¬ p2254) ∨ (¬ p4330) ∨ p2651 ∨ p3083)
    : p3083 ∨ p2651 ∨ (¬ p2608) ∨ (¬ p3483) ∨ (¬ p2829) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4330 := h106329;
    (Or.elim h88118 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step121878 (p2254 p2946 p3093 p3115 p3309 p3791 p4322 p4826 : Prop)
    (h105366 : p2254)
    (h105444 : p4826)
    (h88119 : (¬ p3791) ∨ (¬ p4826) ∨ p3115 ∨ p2946 ∨ (¬ p3093) ∨ (¬ p2254) ∨ (¬ p4322) ∨ (¬ p3309))
    : (¬ p3791) ∨ p3115 ∨ p2946 ∨ (¬ p3093) ∨ (¬ p4322) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4826 := h105444;
    (Or.elim h88119 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step121881 (p2437 p2881 p3083 p4404 p4647 : Prop)
    (h105412 : p4647)
    (h88133 : (¬ p4404) ∨ (¬ p3083) ∨ (¬ p4647) ∨ p2437 ∨ p2881)
    : (¬ p4404) ∨ (¬ p3083) ∨ p2881 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4404 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4647 := h105412;
    (Or.elim h88133 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step121883 (p2177 p2662 p3083 p3389 p4404 p4712 : Prop)
    (h105422 : p4712)
    (h88137 : (¬ p4404) ∨ (¬ p3083) ∨ p2177 ∨ (¬ p2662) ∨ (¬ p4712) ∨ p3389)
    : p3389 ∨ (¬ p2662) ∨ p2177 ∨ (¬ p3083) ∨ (¬ p4404) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4712 := h105422;
    (Or.elim h88137 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step121886 (p2341 p2737 p3363 p3527 p3687 p4752 p5197 : Prop)
    (h105434 : p4752)
    (h88146 : (¬ p3527) ∨ (¬ p3687) ∨ p2341 ∨ (¬ p4752) ∨ (¬ p5197) ∨ (¬ p3363) ∨ p2737)
    : p2341 ∨ (¬ p3527) ∨ (¬ p5197) ∨ (¬ p3363) ∨ (¬ p3687) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4752 := h105434;
    (Or.elim h88146 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u5 r5)))))))))))))))

theorem step121888 (p2210 p3516 p3631 p3687 p4877 p5206 : Prop)
    (h105451 : p4877)
    (h88149 : (¬ p3631) ∨ p3516 ∨ (¬ p4877) ∨ (¬ p5206) ∨ (¬ p2210) ∨ (¬ p3687))
    : (¬ p3631) ∨ (¬ p3687) ∨ (¬ p2210) ∨ (¬ p5206) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4877 := h105451;
    (Or.elim h88149 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step121891 (p2241 p2750 p3516 p3631 p3687 p5206 : Prop)
    (h106345 : p2750)
    (h88155 : (¬ p3631) ∨ (¬ p5206) ∨ (¬ p3687) ∨ (¬ p2750) ∨ (¬ p2241) ∨ p3516)
    : (¬ p5206) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p2241) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5206 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2750 := h106345;
    (Or.elim h88155 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u4 r4)))))))))))))

theorem step121894 (p2363 p2383 p2459 p2518 p2608 p3204 p3379 p4420 p4870 : Prop)
    (h105707 : p4420)
    (h88164 : p2363 ∨ p2608 ∨ (¬ p3379) ∨ (¬ p3204) ∨ (¬ p2459) ∨ (¬ p4870) ∨ (¬ p4420) ∨ (¬ p2518) ∨ p2383)
    : (¬ p2518) ∨ (¬ p4870) ∨ (¬ p3204) ∨ (¬ p3379) ∨ p2363 ∨ (¬ p2459) ∨ p2608 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4420 := h105707;
    (Or.elim h88164 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (u7 r7)))))))))))))))))))

theorem step121902 (p2406 p2497 p2498 p2573 p2850 p4730 : Prop)
    (h106074 : p4730)
    (h88185 : p2850 ∨ (¬ p2573) ∨ (¬ p2406) ∨ (¬ p2497) ∨ (¬ p4730) ∨ (¬ p2498))
    : (¬ p2498) ∨ p2850 ∨ (¬ p2497) ∨ (¬ p2573) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2498 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4730 := h106074;
    (Or.elim h88185 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step121906 (p2497 p2553 p2573 p3309 p5194 : Prop)
    (h105489 : p5194)
    (h88191 : p3309 ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p5194) ∨ (¬ p2497))
    : (¬ p2497) ∨ (¬ p2553) ∨ p3309 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2497 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5194 := h105489;
    (Or.elim h88191 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step121909 (p2341 p2641 p2656 p3031 p3527 p4975 p5201 : Prop)
    (h105464 : p4975)
    (h88218 : (¬ p2341) ∨ p3527 ∨ (¬ p5201) ∨ (¬ p3031) ∨ (¬ p4975) ∨ (¬ p2656) ∨ (¬ p2641))
    : (¬ p2656) ∨ (¬ p3031) ∨ (¬ p5201) ∨ (¬ p2641) ∨ p3527 ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2656 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4975 := h105464;
    (Or.elim h88218 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step121913 (p2255 p2264 p2807 p3031 p3527 : Prop)
    (h105367 : p2255)
    (h88242 : p3527 ∨ (¬ p3031) ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p2255))
    : p3527 ∨ (¬ p3031) ∨ (¬ p2807) ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2255 := h105367;
    (Or.elim h88242 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121915 (p2696 p2707 p3367 p3425 p4752 : Prop)
    (h105434 : p4752)
    (h88251 : p2707 ∨ p3425 ∨ (¬ p3367) ∨ p2696 ∨ (¬ p4752))
    : p2707 ∨ p3425 ∨ (¬ p3367) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4752 := h105434;
    (Or.elim h88251 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121916 (p2707 p2737 p2807 p4777 p4790 : Prop)
    (h106424 : p4790)
    (h88255 : p2707 ∨ (¬ p4777) ∨ (¬ p4790) ∨ (¬ p2737) ∨ (¬ p2807))
    : p2707 ∨ (¬ p4777) ∨ (¬ p2807) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    (Or.elim h88255 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step121917 (p2210 p2707 p3425 p3589 p4377 : Prop)
    (h106170 : p4377)
    (h88268 : p2707 ∨ (¬ p3589) ∨ p2210 ∨ p3425 ∨ (¬ p4377))
    : p2707 ∨ p3425 ∨ p2210 ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4377 := h106170;
    (Or.elim h88268 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121918 (p2187 p2254 p2284 p2707 p2946 p3425 p3537 p3589 p4859 : Prop)
    (h105366 : p2254)
    (h88269 : (¬ p3537) ∨ p2707 ∨ p2187 ∨ (¬ p4859) ∨ p2284 ∨ p2946 ∨ (¬ p2254) ∨ p3425 ∨ (¬ p3589))
    : p3425 ∨ p2946 ∨ (¬ p3537) ∨ p2187 ∨ (¬ p4859) ∨ p2707 ∨ (¬ p3589) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4859 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2254 := h105366;
    (Or.elim h88269 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step121920 (p2254 p2274 p2295 p2707 p2829 p2946 p3425 p3589 p4153 p4889 : Prop)
    (h105366 : p2254)
    (h88282 : p2295 ∨ (¬ p4153) ∨ (¬ p2274) ∨ p2707 ∨ (¬ p2829) ∨ (¬ p4889) ∨ p2946 ∨ p3425 ∨ (¬ p3589) ∨ (¬ p2254))
    : (¬ p4153) ∨ p2946 ∨ p2295 ∨ p2707 ∨ (¬ p4889) ∨ (¬ p2274) ∨ p3425 ∨ (¬ p3589) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4153 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2254 := h105366;
    (Or.elim h88282 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step121923 (p2248 p2528 p2608 p2651 p2707 p3083 p3434 p4669 : Prop)
    (h105365 : p2248)
    (h105415 : p4669)
    (h88291 : p2707 ∨ p2608 ∨ (¬ p2651) ∨ (¬ p2528) ∨ (¬ p2248) ∨ (¬ p3083) ∨ (¬ p4669) ∨ p3434)
    : p3434 ∨ (¬ p2651) ∨ p2608 ∨ (¬ p2528) ∨ (¬ p3083) ∨ p2707 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4669 := h105415;
    (Or.elim h88291 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step121924 (p2248 p2331 p2363 p2608 p2668 p2707 p3434 p4669 : Prop)
    (h105365 : p2248)
    (h105415 : p4669)
    (h88292 : (¬ p2668) ∨ p2608 ∨ (¬ p2331) ∨ p2707 ∨ (¬ p2363) ∨ (¬ p2248) ∨ p3434 ∨ (¬ p4669))
    : p2707 ∨ (¬ p2668) ∨ (¬ p2331) ∨ p3434 ∨ p2608 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4669 := h105415;
    (Or.elim h88292 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121931 (p2352 p2363 p2573 p2608 p2707 p3434 p4669 p5190 : Prop)
    (h105415 : p4669)
    (h105487 : p5190)
    (h88307 : p2707 ∨ (¬ p2573) ∨ (¬ p2363) ∨ (¬ p5190) ∨ p2608 ∨ (¬ p4669) ∨ p3434 ∨ (¬ p2352))
    : p2707 ∨ p3434 ∨ (¬ p2573) ∨ (¬ p2363) ∨ p2608 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4669 := h105415;
    let u7 : p5190 := h105487;
    (Or.elim h88307 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step121934 (p2248 p2373 p2440 p2608 p2651 p2707 p2717 p4902 : Prop)
    (h105365 : p2248)
    (h105456 : p4902)
    (h88312 : (¬ p2651) ∨ p2440 ∨ (¬ p2373) ∨ p2608 ∨ p2707 ∨ p2717 ∨ (¬ p2248) ∨ (¬ p4902))
    : p2707 ∨ (¬ p2373) ∨ p2440 ∨ p2717 ∨ (¬ p2651) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4902 := h105456;
    (Or.elim h88312 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step121935 (p2187 p2230 p2563 p2608 p2707 p2717 p4133 p5190 : Prop)
    (h105712 : p4133)
    (h105487 : p5190)
    (h88322 : p2608 ∨ p2717 ∨ (¬ p2563) ∨ (¬ p2230) ∨ (¬ p2187) ∨ p2707 ∨ (¬ p5190) ∨ (¬ p4133))
    : p2717 ∨ (¬ p2230) ∨ (¬ p2187) ∨ p2707 ∨ (¬ p2563) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4133 := h105712;
    let u7 : p5190 := h105487;
    (Or.elim h88322 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step121943 (p2248 p2608 p2707 p2946 p3146 p3156 p3434 p4669 : Prop)
    (h105365 : p2248)
    (h105415 : p4669)
    (h88347 : (¬ p3146) ∨ (¬ p2248) ∨ p2707 ∨ p3434 ∨ (¬ p4669) ∨ (¬ p3156) ∨ (¬ p2946) ∨ p2608)
    : p2707 ∨ p3434 ∨ (¬ p3156) ∨ p2608 ∨ (¬ p3146) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4669 := h105415;
    (Or.elim h88347 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step121944 (p2437 p2707 p3367 p4106 p4750 : Prop)
    (h105433 : p4750)
    (h88349 : p2707 ∨ (¬ p3367) ∨ (¬ p4106) ∨ (¬ p4750) ∨ (¬ p2437))
    : (¬ p4106) ∨ p2707 ∨ (¬ p3367) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4106 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    (Or.elim h88349 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121949 (p2241 p2707 p2744 p3425 p3589 : Prop)
    (h106503 : p2744)
    (h88381 : p2707 ∨ p2241 ∨ p3425 ∨ (¬ p3589) ∨ (¬ p2744))
    : p2707 ∨ p3425 ∨ p2241 ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2744 := h106503;
    (Or.elim h88381 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121950 (p2230 p2373 p2608 p2707 p3146 p3434 p4669 p5190 : Prop)
    (h105415 : p4669)
    (h105487 : p5190)
    (h88389 : p2608 ∨ (¬ p3146) ∨ (¬ p5190) ∨ p3434 ∨ (¬ p4669) ∨ p2707 ∨ (¬ p2373) ∨ (¬ p2230))
    : p3434 ∨ p2707 ∨ p2608 ∨ (¬ p3146) ∨ (¬ p2230) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4669 := h105415;
    let u7 : p5190 := h105487;
    (Or.elim h88389 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step121951 (p2363 p2510 p2528 p2573 p2608 p2707 p2717 p4133 p5190 : Prop)
    (h105712 : p4133)
    (h105487 : p5190)
    (h88404 : (¬ p2510) ∨ (¬ p2528) ∨ p2608 ∨ (¬ p2573) ∨ (¬ p5190) ∨ p2707 ∨ p2363 ∨ (¬ p4133) ∨ p2717)
    : (¬ p2573) ∨ p2707 ∨ p2363 ∨ (¬ p2510) ∨ p2717 ∨ p2608 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4133 := h105712;
    let u8 : p5190 := h105487;
    (Or.elim h88404 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u4 r7)))))))))))))))))))

theorem step121953 (p2177 p2248 p2295 p2331 p2608 p2707 p3434 p4666 : Prop)
    (h105365 : p2248)
    (h105658 : p4666)
    (h88414 : p2608 ∨ p2707 ∨ (¬ p4666) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2177) ∨ p3434 ∨ (¬ p2248))
    : p3434 ∨ p2707 ∨ p2608 ∨ (¬ p2295) ∨ (¬ p2177) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4666 := h105658;
    (Or.elim h88414 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step121957 (p2098 p2248 p2449 p2707 p2807 p3246 p3537 p3873 p4898 : Prop)
    (h105365 : p2248)
    (h105455 : p4898)
    (h88428 : (¬ p3537) ∨ (¬ p2449) ∨ p2707 ∨ p3246 ∨ (¬ p2248) ∨ (¬ p4898) ∨ (¬ p3873) ∨ (¬ p2807) ∨ p2098)
    : p2707 ∨ p2098 ∨ (¬ p3873) ∨ (¬ p2807) ∨ p3246 ∨ (¬ p3537) ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    let u8 : p4898 := h105455;
    (Or.elim h88428 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (u1 r7)))))))))))))))))))

theorem step121958 (p2098 p2248 p2427 p2440 p2651 p2707 p3537 p3873 p4898 : Prop)
    (h105365 : p2248)
    (h105455 : p4898)
    (h88431 : (¬ p3537) ∨ p2098 ∨ (¬ p4898) ∨ p2707 ∨ p2440 ∨ (¬ p2651) ∨ (¬ p3873) ∨ (¬ p2248) ∨ (¬ p2427))
    : (¬ p3537) ∨ p2098 ∨ p2440 ∨ (¬ p3873) ∨ (¬ p2427) ∨ p2707 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    let u8 : p4898 := h105455;
    (Or.elim h88431 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step121959 (p2248 p2352 p2608 p2651 p2707 p2717 p3016 p4133 : Prop)
    (h105365 : p2248)
    (h105712 : p4133)
    (h88432 : (¬ p2352) ∨ (¬ p3016) ∨ p2707 ∨ p2608 ∨ (¬ p2248) ∨ (¬ p4133) ∨ p2717 ∨ (¬ p2651))
    : p2707 ∨ p2608 ∨ (¬ p3016) ∨ p2717 ∨ (¬ p2651) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    let u7 : p4133 := h105712;
    (Or.elim h88432 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step121960 (p2132 p2651 p2707 p2811 p3276 p3343 p3366 p4423 p4831 p5052 : Prop)
    (h105473 : p5052)
    (h105445 : p4831)
    (h88435 : (¬ p3343) ∨ p3366 ∨ (¬ p3276) ∨ (¬ p2132) ∨ (¬ p2811) ∨ (¬ p5052) ∨ p2707 ∨ (¬ p2651) ∨ (¬ p4423) ∨ (¬ p4831))
    : (¬ p3343) ∨ (¬ p3276) ∨ p2707 ∨ p3366 ∨ (¬ p2651) ∨ (¬ p2811) ∨ (¬ p2132) ∨ (¬ p4423) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3366) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4423 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5052 := h105473;
    let u9 : p4831 := h105445;
    (Or.elim h88435 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step121967 (p2363 p2470 p2528 p2608 p2707 p2717 p4133 p5190 : Prop)
    (h105712 : p4133)
    (h105487 : p5190)
    (h88454 : p2363 ∨ (¬ p2528) ∨ (¬ p4133) ∨ p2707 ∨ p2608 ∨ p2717 ∨ (¬ p5190) ∨ (¬ p2470))
    : (¬ p2470) ∨ p2707 ∨ p2608 ∨ p2363 ∨ (¬ p2528) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4133 := h105712;
    let u7 : p5190 := h105487;
    (Or.elim h88454 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step121974 (p2132 p2449 p2737 p2807 p2881 p2891 p3361 p4418 p4666 : Prop)
    (h105658 : p4666)
    (h88502 : p2449 ∨ p2737 ∨ (¬ p2132) ∨ p2807 ∨ (¬ p2881) ∨ (¬ p4418) ∨ (¬ p2891) ∨ (¬ p3361) ∨ (¬ p4666))
    : (¬ p2132) ∨ (¬ p3361) ∨ p2449 ∨ (¬ p2891) ∨ p2807 ∨ (¬ p2881) ∨ p2737 ∨ (¬ p4418) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4666 := h105658;
    (Or.elim h88502 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step121975 (p2132 p2331 p2737 p2891 p3246 p3323 p3361 p4418 p4625 : Prop)
    (h106455 : p4625)
    (h88503 : p2331 ∨ p2737 ∨ (¬ p4418) ∨ (¬ p3246) ∨ (¬ p2891) ∨ (¬ p4625) ∨ p3323 ∨ (¬ p2132) ∨ (¬ p3361))
    : (¬ p2891) ∨ p2331 ∨ p2737 ∨ (¬ p4418) ∨ (¬ p3246) ∨ (¬ p2132) ∨ (¬ p3361) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4625 := h106455;
    (Or.elim h88503 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step121976 (p2264 p2598 p2807 p3276 p3361 p3619 p4749 p5123 p5164 p5558 : Prop)
    (h105432 : p4749)
    (h88511 : (¬ p3619) ∨ (¬ p5164) ∨ (¬ p4749) ∨ (¬ p5558) ∨ p2264 ∨ p2598 ∨ p2807 ∨ (¬ p5123) ∨ (¬ p3276) ∨ (¬ p3361))
    : (¬ p3276) ∨ (¬ p5164) ∨ p2807 ∨ p2598 ∨ (¬ p3361) ∨ p2264 ∨ (¬ p3619) ∨ (¬ p5123) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5164 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4749 := h105432;
    (Or.elim h88511 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step121980 (p2737 p3166 p3361 p3367 p3683 p5008 : Prop)
    (h105469 : p5008)
    (h88530 : p2737 ∨ p3166 ∨ (¬ p5008) ∨ (¬ p3683) ∨ (¬ p3361) ∨ (¬ p3367))
    : p3166 ∨ (¬ p3361) ∨ (¬ p3683) ∨ (¬ p3367) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5008 := h105469;
    (Or.elim h88530 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step121982 (p2749 p2946 p2992 p3361 p3367 p4749 : Prop)
    (h105432 : p4749)
    (h88548 : (¬ p2992) ∨ p2946 ∨ (¬ p4749) ∨ (¬ p3361) ∨ p3367 ∨ (¬ p2749))
    : (¬ p3361) ∨ (¬ p2749) ∨ p3367 ∨ (¬ p2992) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3361 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4749 := h105432;
    (Or.elim h88548 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step121983 (p2132 p2707 p2737 p3425 p5052 : Prop)
    (h105473 : p5052)
    (h88553 : (¬ p2707) ∨ p2737 ∨ (¬ p5052) ∨ (¬ p3425) ∨ (¬ p2132))
    : (¬ p2132) ∨ (¬ p3425) ∨ (¬ p2707) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5052 := h105473;
    (Or.elim h88553 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step121984 (p2132 p2860 p3425 p4169 p4555 : Prop)
    (h105542 : p4555)
    (h41110 : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4555))
    : (¬ p4169) ∨ (¬ p3425) ∨ (¬ p2860) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4169 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    (Or.elim h41110 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121987 (p2241 p2707 p2750 p3425 p3873 : Prop)
    (h106345 : p2750)
    (h42585 : (¬ p2241) ∨ (¬ p2707) ∨ (¬ p2750) ∨ (¬ p3425) ∨ (¬ p3873))
    : (¬ p2707) ∨ (¬ p3425) ∨ (¬ p2241) ∨ (¬ p3873) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2750 := h106345;
    (Or.elim h42585 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step121988 (p2132 p2901 p3425 p4169 p4906 : Prop)
    (h105632 : p4906)
    (h42287 : (¬ p2132) ∨ (¬ p2901) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4906))
    : (¬ p4169) ∨ (¬ p3425) ∨ (¬ p2132) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4169 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4906 := h105632;
    (Or.elim h42287 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121989 (p2132 p2427 p3425 p4169 p4882 : Prop)
    (h105453 : p4882)
    (h50563 : (¬ p2132) ∨ (¬ p2427) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4882))
    : (¬ p4169) ∨ (¬ p3425) ∨ (¬ p2427) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4169 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4882 := h105453;
    (Or.elim h50563 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121990 (p2132 p2891 p3425 p4169 p4878 : Prop)
    (h105452 : p4878)
    (h50050 : (¬ p2132) ∨ (¬ p2891) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4878))
    : (¬ p4169) ∨ (¬ p3425) ∨ (¬ p2891) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4169 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4878 := h105452;
    (Or.elim h50050 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121992 (p2696 p2751 p2996 p3425 p4777 : Prop)
    (h106343 : p2751)
    (h88569 : (¬ p3425) ∨ p2996 ∨ (¬ p2696) ∨ (¬ p4777) ∨ (¬ p2751))
    : (¬ p3425) ∨ (¬ p2696) ∨ p2996 ∨ (¬ p4777) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    (Or.elim h88569 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step121996 (p2331 p2459 p2737 p2811 p3323 p3425 p3527 p3576 p4330 : Prop)
    (h106329 : p4330)
    (h88577 : (¬ p2811) ∨ (¬ p3425) ∨ (¬ p4330) ∨ (¬ p2737) ∨ (¬ p3576) ∨ p3527 ∨ (¬ p3323) ∨ (¬ p2331) ∨ p2459)
    : (¬ p3576) ∨ (¬ p3425) ∨ (¬ p2811) ∨ p3527 ∨ p2459 ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3576 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4330 := h106329;
    (Or.elim h88577 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (u4 r7)))))))))))))))))))

theorem step122006 (p2241 p2459 p2717 p2744 p3093 p3323 p3366 p3425 p3922 p4330 : Prop)
    (h106503 : p2744)
    (h106329 : p4330)
    (h88597 : p2717 ∨ (¬ p3425) ∨ (¬ p3366) ∨ (¬ p3093) ∨ p2241 ∨ p2459 ∨ (¬ p2744) ∨ (¬ p3922) ∨ (¬ p3323) ∨ (¬ p4330))
    : p2717 ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3425) ∨ p2241 ∨ (¬ p3922) ∨ (¬ p3323) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4330 := h106329;
    (Or.elim h88597 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step122010 (p2177 p2253 p2717 p2946 p2992 p2996 p3425 p4736 : Prop)
    (h105431 : p4736)
    (h88607 : p2996 ∨ p2992 ∨ (¬ p4736) ∨ (¬ p2946) ∨ (¬ p2253) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p2177))
    : p2717 ∨ p2992 ∨ (¬ p2253) ∨ (¬ p2946) ∨ p2996 ∨ (¬ p3425) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h88607 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step122015 (p2241 p2459 p2641 p2717 p3323 p3425 p4330 p4736 : Prop)
    (h105431 : p4736)
    (h106329 : p4330)
    (h88615 : (¬ p2241) ∨ (¬ p2641) ∨ p2459 ∨ (¬ p4736) ∨ (¬ p4330) ∨ (¬ p3323) ∨ p2717 ∨ (¬ p3425))
    : (¬ p3425) ∨ (¬ p2241) ∨ (¬ p2641) ∨ p2459 ∨ p2717 ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4330 := h106329;
    (Or.elim h88615 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step122017 (p2459 p2493 p2717 p3379 p3425 p3564 p4330 p4736 : Prop)
    (h105431 : p4736)
    (h106329 : p4330)
    (h88622 : (¬ p3564) ∨ (¬ p3425) ∨ p2459 ∨ (¬ p4736) ∨ (¬ p4330) ∨ p2717 ∨ (¬ p3379) ∨ (¬ p2493))
    : (¬ p3564) ∨ (¬ p2493) ∨ (¬ p3379) ∨ p2717 ∨ (¬ p3425) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4736 := h105431;
    let u7 : p4330 := h106329;
    (Or.elim h88622 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step122021 (p2406 p2459 p2717 p2982 p3379 p3425 p4450 p4736 : Prop)
    (h105431 : p4736)
    (h88630 : (¬ p2982) ∨ p2717 ∨ (¬ p3425) ∨ (¬ p4736) ∨ (¬ p4450) ∨ p2459 ∨ (¬ p3379) ∨ (¬ p2406))
    : p2717 ∨ (¬ p3379) ∨ (¬ p4450) ∨ (¬ p2982) ∨ (¬ p3425) ∨ p2459 ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    (Or.elim h88630 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step122022 (p2230 p2459 p2563 p2717 p3125 p3366 p3425 p3519 p4330 p4376 : Prop)
    (h106320 : p4376)
    (h106329 : p4330)
    (h88633 : p2717 ∨ (¬ p3125) ∨ (¬ p2230) ∨ (¬ p3519) ∨ (¬ p4330) ∨ (¬ p3425) ∨ (¬ p2563) ∨ (¬ p3366) ∨ p2459 ∨ (¬ p4376))
    : (¬ p3425) ∨ p2717 ∨ (¬ p2230) ∨ p2459 ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3366) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p4330 := h106329;
    (Or.elim h88633 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step122025 (p2246 p2331 p2717 p2744 p3323 p3366 p3425 p3461 p5123 p5558 : Prop)
    (h106503 : p2744)
    (h88641 : (¬ p3323) ∨ (¬ p5123) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p2744) ∨ (¬ p2331) ∨ p2717 ∨ (¬ p3425) ∨ (¬ p2246) ∨ (¬ p5558))
    : (¬ p2246) ∨ p2717 ∨ (¬ p5123) ∨ (¬ p3323) ∨ (¬ p3425) ∨ (¬ p3366) ∨ (¬ p5558) ∨ (¬ p2331) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    (Or.elim h88641 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step122028 (p3425 p3434 p3516 p3873 p5207 : Prop)
    (h105491 : p5207)
    (h88645 : p3434 ∨ (¬ p3425) ∨ (¬ p3516) ∨ (¬ p5207) ∨ (¬ p3873))
    : p3434 ∨ (¬ p3516) ∨ (¬ p3873) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5207 := h105491;
    (Or.elim h88645 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step122030 (p2156 p2246 p2284 p2459 p2717 p2744 p2958 p3115 p3366 p3425 p4330 p5045 : Prop)
    (h106503 : p2744)
    (h106329 : p4330)
    (h88650 : (¬ p3115) ∨ p2284 ∨ p2717 ∨ (¬ p2246) ∨ (¬ p2744) ∨ p2459 ∨ (¬ p5045) ∨ (¬ p2156) ∨ (¬ p2958) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p4330))
    : (¬ p3425) ∨ (¬ p3366) ∨ (¬ p2156) ∨ p2717 ∨ p2459 ∨ p2284 ∨ (¬ p2958) ∨ (¬ p3115) ∨ (¬ p2246) ∨ (¬ p5045) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    let u11 : p4330 := h106329;
    (Or.elim h88650 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u0))) (fun r10 => (False.elim (r10 u11)))))))))))))))))))))))))

theorem step122034 (p2210 p2470 p3083 p3343 p3366 p3371 p3425 p3434 p4638 p5190 : Prop)
    (h105487 : p5190)
    (h105409 : p4638)
    (h88661 : (¬ p2470) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p5190) ∨ p3434 ∨ p2210 ∨ (¬ p3425) ∨ (¬ p3371) ∨ (¬ p4638) ∨ p3083)
    : (¬ p3371) ∨ p3083 ∨ (¬ p2470) ∨ p3434 ∨ p2210 ∨ (¬ p3425) ∨ (¬ p3366) ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3371 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5190 := h105487;
    let u9 : p4638 := h105409;
    (Or.elim h88661 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u1 r8)))))))))))))))))))))

theorem step122035 (p2246 p2553 p2651 p2717 p2744 p2881 p3016 p3366 p3425 p4559 : Prop)
    (h106503 : p2744)
    (h105701 : p4559)
    (h88662 : (¬ p2553) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p3366) ∨ (¬ p2881) ∨ (¬ p4559) ∨ (¬ p3016) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2651))
    : (¬ p3425) ∨ p2717 ∨ (¬ p2246) ∨ (¬ p2881) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p3366) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2744 := h106503;
    let u9 : p4559 := h105701;
    (Or.elim h88662 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step122036 (p2459 p2651 p2717 p3016 p3425 p3564 p4330 p4786 : Prop)
    (h106425 : p4786)
    (h106329 : p4330)
    (h88665 : (¬ p3564) ∨ p2717 ∨ (¬ p3016) ∨ (¬ p4330) ∨ (¬ p3425) ∨ (¬ p2651) ∨ (¬ p4786) ∨ p2459)
    : (¬ p3425) ∨ p2717 ∨ (¬ p3016) ∨ (¬ p2651) ∨ p2459 ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4786 := h106425;
    let u7 : p4330 := h106329;
    (Or.elim h88665 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step122037 (p2459 p2573 p2663 p2717 p3016 p3343 p3425 p4332 p4786 : Prop)
    (h106425 : p4786)
    (h88666 : (¬ p3343) ∨ p3016 ∨ p2459 ∨ (¬ p4332) ∨ (¬ p4786) ∨ p2717 ∨ (¬ p3425) ∨ (¬ p2573) ∨ (¬ p2663))
    : (¬ p3425) ∨ p2717 ∨ p3016 ∨ (¬ p4332) ∨ (¬ p2663) ∨ (¬ p3343) ∨ (¬ p2573) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4786 := h106425;
    (Or.elim h88666 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step122040 (p2156 p2284 p2707 p3156 p3425 p3537 p3873 p4399 p4746 p5190 : Prop)
    (h105487 : p5190)
    (h88669 : (¬ p2707) ∨ (¬ p3873) ∨ (¬ p5190) ∨ (¬ p2156) ∨ (¬ p3156) ∨ p2284 ∨ p3537 ∨ (¬ p4746) ∨ (¬ p4399) ∨ (¬ p3425))
    : p3537 ∨ (¬ p2707) ∨ (¬ p3873) ∨ (¬ p2156) ∨ (¬ p4746) ∨ (¬ p3156) ∨ (¬ p4399) ∨ p2284 ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5190 := h105487;
    (Or.elim h88669 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step122048 (p2230 p2373 p2717 p3146 p3425 p4419 p5118 p5558 : Prop)
    (h105482 : p5118)
    (h88681 : (¬ p5558) ∨ (¬ p5118) ∨ (¬ p4419) ∨ (¬ p2230) ∨ p2717 ∨ (¬ p3425) ∨ (¬ p3146) ∨ (¬ p2373))
    : (¬ p5558) ∨ (¬ p2230) ∨ (¬ p3425) ∨ (¬ p2373) ∨ (¬ p3146) ∨ p2717 ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5118 := h105482;
    (Or.elim h88681 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step122050 (p2098 p2177 p3425 p4169 p4559 p4804 : Prop)
    (h105701 : p4559)
    (h88692 : (¬ p4804) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4559) ∨ p2177 ∨ (¬ p2098))
    : (¬ p2098) ∨ (¬ p4169) ∨ p2177 ∨ (¬ p3425) ∨ (¬ p4804) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4804 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4559 := h105701;
    (Or.elim h88692 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step122052 (p2132 p2187 p2509 p2860 p2922 p3389 p4108 p4384 p4733 : Prop)
    (h105430 : p4733)
    (h106167 : p4384)
    (h88700 : (¬ p2922) ∨ p3389 ∨ (¬ p2860) ∨ (¬ p2509) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p4733) ∨ (¬ p4384) ∨ (¬ p4108))
    : (¬ p2509) ∨ (¬ p2132) ∨ (¬ p4108) ∨ p3389 ∨ (¬ p2187) ∨ (¬ p2860) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    let u8 : p4384 := h106167;
    (Or.elim h88700 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step122054 (p2132 p2742 p2922 p3389 p3905 p4281 p5052 : Prop)
    (h105473 : p5052)
    (h88713 : (¬ p2922) ∨ (¬ p3905) ∨ (¬ p2742) ∨ p3389 ∨ (¬ p5052) ∨ (¬ p2132) ∨ (¬ p4281))
    : (¬ p3905) ∨ (¬ p2132) ∨ (¬ p2922) ∨ (¬ p2742) ∨ p3389 ∨ (¬ p4281) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3905 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5052 := h105473;
    (Or.elim h88713 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step122055 (p2220 p2363 p2911 p2922 p3146 p3379 p4503 : Prop)
    (h106530 : p4503)
    (h88714 : p2220 ∨ p3146 ∨ (¬ p3379) ∨ (¬ p2922) ∨ (¬ p2911) ∨ (¬ p2363) ∨ (¬ p4503))
    : p3146 ∨ (¬ p2922) ∨ (¬ p2911) ∨ (¬ p2363) ∨ p2220 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4503 := h106530;
    (Or.elim h88714 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step122056 (p2210 p2749 p2922 p3389 p4108 p4281 p4877 : Prop)
    (h105451 : p4877)
    (h88718 : (¬ p2922) ∨ (¬ p2749) ∨ (¬ p4281) ∨ p3389 ∨ (¬ p4108) ∨ (¬ p4877) ∨ (¬ p2210))
    : (¬ p2749) ∨ (¬ p4108) ∨ (¬ p2922) ∨ (¬ p4281) ∨ p3389 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2749 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4877 := h105451;
    (Or.elim h88718 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step122057 (p2241 p2750 p2922 p3389 p3541 p4108 : Prop)
    (h106345 : p2750)
    (h88719 : (¬ p3541) ∨ (¬ p2241) ∨ (¬ p2922) ∨ (¬ p2750) ∨ (¬ p4108) ∨ p3389)
    : (¬ p4108) ∨ (¬ p3541) ∨ (¬ p2241) ∨ p3389 ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4108 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2750 := h106345;
    (Or.elim h88719 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step122060 (p2630 p2656 p2922 p3136 p3347 p3879 p4646 : Prop)
    (h105534 : p4646)
    (h88734 : p3136 ∨ (¬ p2922) ∨ (¬ p2630) ∨ (¬ p4646) ∨ (¬ p3347) ∨ (¬ p3879) ∨ (¬ p2656))
    : (¬ p2656) ∨ (¬ p2630) ∨ (¬ p2922) ∨ (¬ p3347) ∨ (¬ p3879) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2656 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4646 := h105534;
    (Or.elim h88734 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step122063 (p2156 p2252 p2284 p2608 p2750 p2901 p2922 p2950 p3379 p4277 : Prop)
    (h106345 : p2750)
    (h105380 : p4277)
    (h88743 : p2608 ∨ (¬ p2950) ∨ (¬ p2750) ∨ (¬ p3379) ∨ (¬ p2284) ∨ (¬ p2922) ∨ (¬ p2252) ∨ (¬ p4277) ∨ p2156 ∨ p2901)
    : (¬ p2950) ∨ p2156 ∨ p2901 ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p2252) ∨ p2608 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2950 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    let u9 : p4277 := h105380;
    (Or.elim h88743 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (False.elim (u2 r8)))))))))))))))))))))

theorem step122064 (p2254 p2284 p2417 p2922 p2946 p3125 p3379 p4625 : Prop)
    (h105366 : p2254)
    (h106455 : p4625)
    (h88749 : p3125 ∨ (¬ p2254) ∨ (¬ p2417) ∨ p2284 ∨ (¬ p3379) ∨ (¬ p4625) ∨ (¬ p2922) ∨ p2946)
    : p2946 ∨ p2284 ∨ (¬ p2922) ∨ (¬ p3379) ∨ p3125 ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4625 := h106455;
    (Or.elim h88749 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u0 r6)))))))))))))))))

theorem step122067 (p2156 p2254 p2295 p2396 p2911 p2922 p2950 p3379 p3986 p4666 : Prop)
    (h105366 : p2254)
    (h105658 : p4666)
    (h88756 : (¬ p3986) ∨ p2396 ∨ (¬ p2950) ∨ p2156 ∨ p2295 ∨ (¬ p2922) ∨ (¬ p2254) ∨ (¬ p4666) ∨ (¬ p2911) ∨ (¬ p3379))
    : (¬ p2950) ∨ p2156 ∨ p2396 ∨ (¬ p3986) ∨ (¬ p2922) ∨ (¬ p2911) ∨ (¬ p3379) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2950 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2254 := h105366;
    let u9 : p4666 := h105658;
    (Or.elim h88756 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step122069 (p2166 p2373 p2922 p4202 p4646 : Prop)
    (h105534 : p4646)
    (h88762 : (¬ p2922) ∨ (¬ p2373) ∨ (¬ p4646) ∨ (¬ p4202) ∨ p2166)
    : p2166 ∨ (¬ p4202) ∨ (¬ p2922) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2166) := (fun h => hn (Or.inl h));
    let u1 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4646 := h105534;
    (Or.elim h88762 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step122072 (p2177 p2230 p2406 p2717 p2922 p3425 p4079 p4276 p4736 : Prop)
    (h105431 : p4736)
    (h105516 : p4276)
    (h88776 : (¬ p2922) ∨ p2406 ∨ (¬ p4276) ∨ (¬ p3425) ∨ (¬ p4736) ∨ (¬ p2230) ∨ p2717 ∨ (¬ p4079) ∨ (¬ p2177))
    : p2717 ∨ p2406 ∨ (¬ p2177) ∨ (¬ p4079) ∨ (¬ p2922) ∨ (¬ p3425) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2406) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4276 := h105516;
    (Or.elim h88776 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step122073 (p2210 p2922 p3379 p4034 p4646 : Prop)
    (h105534 : p4646)
    (h88778 : p2210 ∨ (¬ p3379) ∨ (¬ p4034) ∨ (¬ p4646) ∨ (¬ p2922))
    : p2210 ∨ (¬ p2922) ∨ (¬ p4034) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4646 := h105534;
    (Or.elim h88778 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step122074 (p2651 p2807 p2922 p4814 : Prop)
    (h105440 : p4814)
    (h88786 : (¬ p2922) ∨ p2807 ∨ (¬ p2651) ∨ (¬ p4814))
    : (¬ p2651) ∨ p2807 ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4814 := h105440;
    (Or.elim h88786 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step122077 (p2254 p2331 p2922 p3323 p3379 p3461 p3868 p4826 : Prop)
    (h105366 : p2254)
    (h105444 : p4826)
    (h88798 : (¬ p3868) ∨ p3323 ∨ p2331 ∨ (¬ p2254) ∨ (¬ p2922) ∨ (¬ p3379) ∨ p3461 ∨ (¬ p4826))
    : (¬ p3868) ∨ p2331 ∨ p3461 ∨ p3323 ∨ (¬ p2922) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4826 := h105444;
    (Or.elim h88798 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step122078 (p2493 p2573 p2717 p2881 p2922 p3425 p4079 p4277 p4736 : Prop)
    (h105431 : p4736)
    (h105380 : p4277)
    (h88799 : (¬ p2922) ∨ p2493 ∨ p2717 ∨ (¬ p4736) ∨ (¬ p3425) ∨ (¬ p4277) ∨ (¬ p4079) ∨ (¬ p2881) ∨ (¬ p2573))
    : (¬ p3425) ∨ p2717 ∨ p2493 ∨ (¬ p2573) ∨ (¬ p2922) ∨ (¬ p2881) ∨ (¬ p4079) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4277 := h105380;
    (Or.elim h88799 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step122079 (p2177 p2254 p2295 p2331 p2417 p2922 p3379 p4668 : Prop)
    (h105366 : p2254)
    (h105414 : p4668)
    (h88808 : (¬ p2417) ∨ p2331 ∨ p2177 ∨ (¬ p2254) ∨ (¬ p4668) ∨ (¬ p2922) ∨ p2295 ∨ (¬ p3379))
    : (¬ p2922) ∨ (¬ p3379) ∨ p2295 ∨ p2177 ∨ p2331 ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p4668 := h105414;
    (Or.elim h88808 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step122084 (p2493 p2573 p2685 p2922 p2946 p3136 p4079 p4236 p4653 p4736 : Prop)
    (h105431 : p4736)
    (h88816 : (¬ p2922) ∨ (¬ p3136) ∨ p2685 ∨ (¬ p2573) ∨ (¬ p4736) ∨ (¬ p4079) ∨ p2946 ∨ p2493 ∨ (¬ p4236) ∨ (¬ p4653))
    : p2685 ∨ (¬ p3136) ∨ (¬ p4079) ∨ (¬ p2573) ∨ p2493 ∨ (¬ p2922) ∨ (¬ p4236) ∨ (¬ p4653) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4736 := h105431;
    (Or.elim h88816 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u8 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step122085 (p2493 p2573 p2696 p2901 p2922 p3136 p4079 p4277 p4736 : Prop)
    (h105431 : p4736)
    (h105380 : p4277)
    (h88817 : (¬ p2922) ∨ p2901 ∨ (¬ p2573) ∨ p3136 ∨ p2696 ∨ (¬ p4736) ∨ p2493 ∨ (¬ p4079) ∨ (¬ p4277))
    : (¬ p2573) ∨ p2901 ∨ (¬ p4079) ∨ p3136 ∨ (¬ p2922) ∨ p2493 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4277 := h105380;
    (Or.elim h88817 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step122086 (p2249 p2437 p2651 p2922 p4281 : Prop)
    (h106513 : p2249)
    (h88818 : (¬ p4281) ∨ (¬ p2249) ∨ p2437 ∨ p2651 ∨ (¬ p2922))
    : p2651 ∨ p2437 ∨ (¬ p4281) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2249 := h106513;
    (Or.elim h88818 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step122087 (p2088 p2255 p2363 p2651 p2911 p2922 p3177 p3189 p4116 p4503 : Prop)
    (h106530 : p4503)
    (h105367 : p2255)
    (h88822 : p3189 ∨ (¬ p2363) ∨ (¬ p4116) ∨ (¬ p2255) ∨ (¬ p3177) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p2651) ∨ p2088 ∨ (¬ p4503))
    : (¬ p4116) ∨ p3189 ∨ (¬ p2363) ∨ (¬ p2922) ∨ (¬ p2911) ∨ p2088 ∨ (¬ p2651) ∨ (¬ p3177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4503 := h106530;
    let u9 : p2255 := h105367;
    (Or.elim h88822 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step122088 (p2509 p2881 p2922 p4277 p4383 : Prop)
    (h105380 : p4277)
    (h41332 : (¬ p2509) ∨ (¬ p2881) ∨ (¬ p2922) ∨ (¬ p4277) ∨ (¬ p4383))
    : (¬ p2509) ∨ (¬ p4383) ∨ (¬ p2881) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4277 := h105380;
    (Or.elim h41332 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step122089 (p2177 p2307 p2417 p2598 p2785 p2829 p2922 p3590 p4668 : Prop)
    (h105414 : p4668)
    (h88824 : (¬ p2417) ∨ p2307 ∨ (¬ p2598) ∨ (¬ p2785) ∨ (¬ p4668) ∨ (¬ p3590) ∨ p2829 ∨ p2177 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2417) ∨ (¬ p2785) ∨ p2307 ∨ (¬ p3590) ∨ p2177 ∨ p2829 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4668 := h105414;
    (Or.elim h88824 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step122091 (p2254 p2295 p2331 p2911 p2922 p3246 p3379 p4140 p4666 : Prop)
    (h105366 : p2254)
    (h105658 : p4666)
    (h88827 : p3246 ∨ (¬ p2911) ∨ (¬ p4666) ∨ (¬ p2254) ∨ p2331 ∨ p2295 ∨ (¬ p3379) ∨ (¬ p4140) ∨ (¬ p2922))
    : p2331 ∨ (¬ p3379) ∨ (¬ p4140) ∨ (¬ p2911) ∨ (¬ p2922) ∨ p2295 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : p4666 := h105658;
    (Or.elim h88827 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step122092 (p2254 p2331 p2363 p2417 p2668 p2922 p3379 p3950 : Prop)
    (h105366 : p2254)
    (h88831 : p2363 ∨ (¬ p2417) ∨ (¬ p3379) ∨ (¬ p2254) ∨ p2668 ∨ (¬ p2922) ∨ (¬ p3950) ∨ p2331)
    : (¬ p3950) ∨ (¬ p3379) ∨ (¬ p2922) ∨ p2331 ∨ p2363 ∨ p2668 ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3950 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    (Or.elim h88831 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (u3 r6)))))))))))))))))

theorem step122093 (p2459 p2608 p2911 p2922 p3093 p3319 p4376 p4604 : Prop)
    (h106320 : p4376)
    (h106293 : p4604)
    (h88833 : p3093 ∨ (¬ p2608) ∨ p3319 ∨ (¬ p2459) ∨ (¬ p4604) ∨ (¬ p4376) ∨ (¬ p2911) ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2911) ∨ (¬ p2608) ∨ p3093 ∨ (¬ p2459) ∨ p3319 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4376 := h106320;
    let u7 : p4604 := h106293;
    (Or.elim h88833 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step122095 (p2341 p2922 p3193 p3575 p4636 p4666 : Prop)
    (h105658 : p4666)
    (h53150 : (¬ p2341) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p3575) ∨ (¬ p4636) ∨ (¬ p4666))
    : (¬ p3193) ∨ (¬ p3575) ∨ (¬ p4636) ∨ (¬ p2922) ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4666 := h105658;
    (Or.elim h53150 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step122098 (p2396 p2922 p3193 p4276 p4636 : Prop)
    (h105516 : p4276)
    (h41361 : (¬ p2396) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p4276) ∨ (¬ p4636))
    : (¬ p3193) ∨ (¬ p4636) ∨ (¬ p2922) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4276 := h105516;
    (Or.elim h41361 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step122100 (p2608 p2922 p3389 p4108 p4376 : Prop)
    (h106320 : p4376)
    (h88849 : (¬ p2922) ∨ p3389 ∨ (¬ p2608) ∨ (¬ p4108) ∨ (¬ p4376))
    : (¬ p4108) ∨ p3389 ∨ (¬ p2608) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4108 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4376 := h106320;
    (Or.elim h88849 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step122102 (p2254 p2922 p2946 p3156 p3379 p3868 p5560 p5568 : Prop)
    (h105366 : p2254)
    (h106188 : p5560)
    (h88861 : (¬ p5568) ∨ (¬ p5560) ∨ (¬ p2254) ∨ (¬ p3379) ∨ (¬ p2922) ∨ (¬ p3868) ∨ p2946 ∨ p3156)
    : (¬ p3868) ∨ p3156 ∨ (¬ p3379) ∨ p2946 ∨ (¬ p5568) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2254 := h105366;
    let u7 : p5560 := h106188;
    (Or.elim h88861 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (u1 r6)))))))))))))))))

theorem step122103 (p2406 p2901 p2922 p3575 p4283 p4702 : Prop)
    (h106079 : p4702)
    (h88870 : (¬ p3575) ∨ p2901 ∨ p2406 ∨ (¬ p4283) ∨ (¬ p4702) ∨ (¬ p2922))
    : (¬ p3575) ∨ p2901 ∨ p2406 ∨ (¬ p4283) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3575 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4702 := h106079;
    (Or.elim h88870 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step122104 (p2274 p2563 p2982 p4624 : Prop)
    (h105408 : p4624)
    (h88877 : (¬ p2982) ∨ (¬ p4624) ∨ p2274 ∨ p2563)
    : (¬ p2982) ∨ p2563 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4624 := h105408;
    (Or.elim h88877 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step122106 (p2396 p2553 p2573 p2608 p3347 p3399 p3527 p4666 : Prop)
    (h105658 : p4666)
    (h88906 : p2608 ∨ p2396 ∨ p2553 ∨ (¬ p3527) ∨ (¬ p4666) ∨ p2573 ∨ (¬ p3399) ∨ (¬ p3347))
    : p2573 ∨ p2553 ∨ (¬ p3347) ∨ (¬ p3527) ∨ p2396 ∨ p2608 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4666 := h105658;
    (Or.elim h88906 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step122107 (p2166 p2210 p2459 p2470 p2528 p2608 p3347 p4902 : Prop)
    (h105456 : p4902)
    (h88909 : p2470 ∨ p2528 ∨ (¬ p3347) ∨ (¬ p4902) ∨ (¬ p2166) ∨ p2608 ∨ (¬ p2210) ∨ (¬ p2459))
    : p2470 ∨ (¬ p2166) ∨ (¬ p3347) ∨ p2528 ∨ (¬ p2210) ∨ (¬ p2459) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4902 := h105456;
    (Or.elim h88909 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step122112 (p2187 p2230 p2459 p2563 p2753 p3166 p3256 p3347 p4117 p4503 : Prop)
    (h106530 : p4503)
    (h88924 : (¬ p2753) ∨ (¬ p3256) ∨ (¬ p4503) ∨ (¬ p3166) ∨ (¬ p4117) ∨ p2459 ∨ p2230 ∨ p2563 ∨ p2187 ∨ (¬ p3347))
    : (¬ p4117) ∨ (¬ p2753) ∨ p2459 ∨ p2187 ∨ p2230 ∨ (¬ p3256) ∨ (¬ p3347) ∨ p2563 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4117 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4503 := h106530;
    (Or.elim h88924 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step122113 (p2230 p2493 p2982 p3347 p4203 p5043 : Prop)
    (h105471 : p5043)
    (h88925 : (¬ p5043) ∨ p2982 ∨ (¬ p2493) ∨ p2230 ∨ (¬ p3347) ∨ (¬ p4203))
    : p2230 ∨ p2982 ∨ (¬ p2493) ∨ (¬ p4203) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2230) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5043 := h105471;
    (Or.elim h88925 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step122114 (p2373 p2427 p2608 p3051 p3063 p3093 p3347 p3904 p4134 : Prop)
    (h105379 : p4134)
    (h88930 : p2608 ∨ p3051 ∨ (¬ p3093) ∨ (¬ p3904) ∨ (¬ p2427) ∨ p2373 ∨ (¬ p3063) ∨ (¬ p4134) ∨ (¬ p3347))
    : (¬ p3347) ∨ (¬ p3063) ∨ p2373 ∨ p2608 ∨ (¬ p2427) ∨ p3051 ∨ (¬ p3904) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3347 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4134 := h105379;
    (Or.elim h88930 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step122117 (p2230 p2427 p2608 p3246 p3347 p3399 p3527 p4666 : Prop)
    (h105658 : p4666)
    (h88934 : (¬ p3527) ∨ p2608 ∨ p3246 ∨ p2427 ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p4666) ∨ p2230)
    : p2608 ∨ (¬ p3347) ∨ (¬ p3527) ∨ (¬ p3399) ∨ p2230 ∨ p3246 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4666 := h105658;
    (Or.elim h88934 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step122121 (p2230 p2498 p3093 p3379 p4257 p4715 p4866 : Prop)
    (h105423 : p4715)
    (h106063 : p4866)
    (h88948 : p3093 ∨ (¬ p2498) ∨ (¬ p4715) ∨ (¬ p4866) ∨ (¬ p3379) ∨ (¬ p2230) ∨ (¬ p4257))
    : (¬ p2498) ∨ p3093 ∨ (¬ p4257) ∨ (¬ p2230) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2498 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4715 := h105423;
    let u6 : p4866 := h106063;
    (Or.elim h88948 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step122126 (p2630 p2685 p3016 p3579 p4711 : Prop)
    (h105655 : p4711)
    (h88963 : (¬ p3579) ∨ p3016 ∨ (¬ p2685) ∨ p2630 ∨ (¬ p4711))
    : p2630 ∨ (¬ p3579) ∨ (¬ p2685) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4711 := h105655;
    (Or.elim h88963 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step122127 (p2427 p2685 p3136 p4066 p4283 p4705 : Prop)
    (h106238 : p4705)
    (h88971 : (¬ p4283) ∨ p3136 ∨ (¬ p4705) ∨ (¬ p2685) ∨ p2427 ∨ (¬ p4066))
    : p3136 ∨ (¬ p4066) ∨ p2427 ∨ (¬ p4283) ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    (Or.elim h88971 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step122128 (p2630 p2685 p2922 p3579 p4811 : Prop)
    (h105633 : p4811)
    (h88972 : (¬ p4811) ∨ p2922 ∨ (¬ p3579) ∨ (¬ p2685) ∨ p2630)
    : p2630 ∨ p2922 ∨ (¬ p2685) ∨ (¬ p3579) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4811 := h105633;
    (Or.elim h88972 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u0 r3)))))))))))

theorem step122133 (p2246 p2630 p2651 p2685 p2749 p3032 p4796 : Prop)
    (h105439 : p4796)
    (h88986 : (¬ p3032) ∨ (¬ p2246) ∨ (¬ p2749) ∨ (¬ p2685) ∨ p2630 ∨ (¬ p2651) ∨ (¬ p4796))
    : (¬ p2749) ∨ (¬ p3032) ∨ p2630 ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2749 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4796 := h105439;
    (Or.elim h88986 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step122134 (p2248 p2396 p2630 p2651 p2685 p3399 p3631 : Prop)
    (h105365 : p2248)
    (h88988 : p3399 ∨ (¬ p2396) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2248) ∨ p3631 ∨ p2630)
    : p2630 ∨ p3399 ∨ (¬ p2651) ∨ (¬ p2396) ∨ p3631 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2248 := h105365;
    (Or.elim h88988 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (u0 r5)))))))))))))))

theorem step122138 (p2230 p2449 p2563 p2685 p2696 p2753 p3125 p3347 p4625 : Prop)
    (h106455 : p4625)
    (h88997 : (¬ p2753) ∨ (¬ p2449) ∨ p2563 ∨ (¬ p2696) ∨ p2230 ∨ p3125 ∨ (¬ p3347) ∨ (¬ p2685) ∨ (¬ p4625))
    : p3125 ∨ p2230 ∨ (¬ p2685) ∨ (¬ p3347) ∨ (¬ p2449) ∨ (¬ p2696) ∨ (¬ p2753) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2230) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4625 := h106455;
    (Or.elim h88997 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step122139 (p2230 p2685 p2696 p2982 p3931 p4322 p4729 p4826 : Prop)
    (h105444 : p4826)
    (h105429 : p4729)
    (h88998 : (¬ p4322) ∨ (¬ p3931) ∨ p2230 ∨ (¬ p4826) ∨ (¬ p2685) ∨ (¬ p4729) ∨ (¬ p2696) ∨ p2982)
    : (¬ p3931) ∨ (¬ p2696) ∨ p2230 ∨ (¬ p4322) ∨ (¬ p2685) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4826 := h105444;
    let u7 : p4729 := h105429;
    (Or.elim h88998 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (u5 r6)))))))))))))))))

theorem step122144 (p2264 p2417 p2685 p2696 p2753 p2927 p3379 p3399 p4666 : Prop)
    (h105658 : p4666)
    (h89007 : (¬ p2753) ∨ p3399 ∨ (¬ p4666) ∨ (¬ p2264) ∨ (¬ p3379) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2927) ∨ p2417)
    : (¬ p2927) ∨ p3399 ∨ (¬ p2696) ∨ (¬ p3379) ∨ (¬ p2264) ∨ p2417 ∨ (¬ p2685) ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2927 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4666 := h105658;
    (Or.elim h89007 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (u5 r7)))))))))))))))))))

theorem step122145 (p2363 p2449 p2685 p2696 p3093 p3923 p3950 p4733 : Prop)
    (h105430 : p4733)
    (h89008 : (¬ p2449) ∨ p2363 ∨ (¬ p3950) ∨ (¬ p3923) ∨ (¬ p4733) ∨ (¬ p2685) ∨ (¬ p2696) ∨ p3093)
    : (¬ p3923) ∨ (¬ p2685) ∨ (¬ p2449) ∨ (¬ p2696) ∨ p3093 ∨ p2363 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3923 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    (Or.elim h89008 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step122146 (p2470 p2528 p2685 p2696 p3266 p3931 p4729 p4826 : Prop)
    (h105444 : p4826)
    (h105429 : p4729)
    (h89010 : (¬ p3931) ∨ p3266 ∨ (¬ p4826) ∨ p2528 ∨ p2470 ∨ (¬ p4729) ∨ (¬ p2685) ∨ (¬ p2696))
    : (¬ p3931) ∨ (¬ p2696) ∨ p2470 ∨ p2528 ∨ (¬ p2685) ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4826 := h105444;
    let u7 : p4729 := h105429;
    (Or.elim h89010 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step122147 (p2210 p2264 p2685 p2696 p2753 p3399 p3631 p4666 p4877 : Prop)
    (h105658 : p4666)
    (h105451 : p4877)
    (h89011 : p3631 ∨ p3399 ∨ (¬ p4666) ∨ (¬ p2264) ∨ (¬ p2753) ∨ (¬ p2685) ∨ (¬ p4877) ∨ (¬ p2210) ∨ (¬ p2696))
    : (¬ p2696) ∨ p3399 ∨ (¬ p2685) ∨ (¬ p2753) ∨ (¬ p2264) ∨ (¬ p2210) ∨ p3631 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4666 := h105658;
    let u8 : p4877 := h105451;
    (Or.elim h89011 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step122149 (p2156 p2685 p2957 p3136 p4333 p4558 : Prop)
    (h105400 : p4558)
    (h89027 : (¬ p4333) ∨ (¬ p4558) ∨ p2156 ∨ (¬ p2957) ∨ (¬ p2685) ∨ p3136)
    : p3136 ∨ p2156 ∨ (¬ p4333) ∨ (¬ p2685) ∨ (¬ p2957) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    (Or.elim h89027 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step122150 (p2396 p2417 p2573 p2608 p2685 p2737 p3581 p5193 : Prop)
    (h105488 : p5193)
    (h89033 : (¬ p2396) ∨ (¬ p2608) ∨ (¬ p3581) ∨ (¬ p2685) ∨ (¬ p5193) ∨ p2417 ∨ p2573 ∨ (¬ p2737))
    : (¬ p2737) ∨ (¬ p2685) ∨ p2417 ∨ (¬ p2608) ∨ (¬ p3581) ∨ (¬ p2396) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    (Or.elim h89033 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step122152 (p2156 p2166 p2192 p2254 p2685 p2807 p3005 p4043 p4172 : Prop)
    (h105366 : p2254)
    (h89036 : (¬ p2166) ∨ p2192 ∨ (¬ p2156) ∨ (¬ p4043) ∨ (¬ p2254) ∨ (¬ p2685) ∨ p3005 ∨ p2807 ∨ (¬ p4172))
    : p3005 ∨ (¬ p2166) ∨ (¬ p4172) ∨ p2192 ∨ (¬ p2156) ∨ (¬ p4043) ∨ (¬ p2685) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2254 := h105366;
    (Or.elim h89036 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step122154 (p2352 p2449 p2685 p2696 p2753 p3564 p3923 p4625 p4870 : Prop)
    (h106455 : p4625)
    (h89043 : p3564 ∨ (¬ p2352) ∨ (¬ p4870) ∨ (¬ p2685) ∨ (¬ p3923) ∨ (¬ p2696) ∨ (¬ p2449) ∨ (¬ p2753) ∨ (¬ p4625))
    : (¬ p3923) ∨ (¬ p2352) ∨ (¬ p2685) ∨ p3564 ∨ (¬ p2696) ∨ (¬ p2449) ∨ (¬ p2753) ∨ (¬ p4870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3923 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4625 := h106455;
    (Or.elim h89043 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step122155 (p2187 p2192 p2210 p2685 p2807 p3005 p4236 p4736 p4774 : Prop)
    (h105431 : p4736)
    (h89044 : p2807 ∨ p3005 ∨ (¬ p2210) ∨ (¬ p4774) ∨ (¬ p4736) ∨ (¬ p4236) ∨ (¬ p2192) ∨ (¬ p2187) ∨ (¬ p2685))
    : p3005 ∨ (¬ p2192) ∨ (¬ p4236) ∨ (¬ p2210) ∨ (¬ p2685) ∨ (¬ p2187) ∨ p2807 ∨ (¬ p4774) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    (Or.elim h89044 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step122157 (p2352 p2363 p2449 p2573 p2685 p2696 p3950 p4729 : Prop)
    (h105429 : p4729)
    (h89053 : (¬ p2449) ∨ (¬ p3950) ∨ (¬ p2685) ∨ p2363 ∨ (¬ p2696) ∨ p2352 ∨ (¬ p4729) ∨ p2573)
    : (¬ p2685) ∨ p2363 ∨ (¬ p2696) ∨ (¬ p2449) ∨ p2573 ∨ p2352 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4729 := h105429;
    (Or.elim h89053 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u4 r6)))))))))))))))))

theorem step122160 (p2651 p2685 p2727 p2745 p2807 : Prop)
    (h105523 : p2745)
    (h89056 : p2807 ∨ (¬ p2651) ∨ (¬ p2745) ∨ p2727 ∨ (¬ p2685))
    : (¬ p2651) ∨ p2807 ∨ (¬ p2685) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2745 := h105523;
    (Or.elim h89056 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step122162 (p2145 p2220 p2685 p2696 p3146 p3266 p3931 p4826 : Prop)
    (h105444 : p4826)
    (h89063 : p3146 ∨ p2220 ∨ p3266 ∨ (¬ p4826) ∨ (¬ p3931) ∨ (¬ p2696) ∨ (¬ p2145) ∨ (¬ p2685))
    : (¬ p3931) ∨ (¬ p2696) ∨ (¬ p2145) ∨ p3266 ∨ p3146 ∨ (¬ p2685) ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4826 := h105444;
    (Or.elim h89063 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step122163 (p2363 p2470 p2528 p2685 p2741 p2996 p3005 p3519 p4376 p4774 : Prop)
    (h106320 : p4376)
    (h89065 : (¬ p3519) ∨ (¬ p4774) ∨ (¬ p2470) ∨ (¬ p2685) ∨ (¬ p4376) ∨ (¬ p2528) ∨ p3005 ∨ p2363 ∨ (¬ p2741) ∨ (¬ p2996))
    : p3005 ∨ (¬ p3519) ∨ p2363 ∨ (¬ p2996) ∨ (¬ p2528) ∨ (¬ p2470) ∨ (¬ p2685) ∨ (¬ p2741) ∨ (¬ p4774) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    (Or.elim h89065 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step122164 (p2341 p2685 p2745 p3031 p3527 p4066 : Prop)
    (h105523 : p2745)
    (h89066 : (¬ p4066) ∨ (¬ p2341) ∨ (¬ p2745) ∨ (¬ p2685) ∨ p3527 ∨ (¬ p3031))
    : (¬ p3031) ∨ (¬ p4066) ∨ p3527 ∨ (¬ p2685) ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3031 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2745 := h105523;
    (Or.elim h89066 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step122165 (p2264 p2363 p2528 p2573 p2685 p2696 p2753 p3347 p3573 p4503 : Prop)
    (h106530 : p4503)
    (h89074 : p2528 ∨ (¬ p2264) ∨ p2573 ∨ (¬ p2363) ∨ (¬ p3573) ∨ (¬ p2696) ∨ (¬ p4503) ∨ (¬ p3347) ∨ (¬ p2685) ∨ (¬ p2753))
    : (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2363) ∨ (¬ p3573) ∨ p2573 ∨ (¬ p2264) ∨ (¬ p2753) ∨ (¬ p3347) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4503 := h106530;
    (Or.elim h89074 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step122168 (p2230 p2373 p2449 p2685 p2696 p3146 p3950 p4729 : Prop)
    (h105429 : p4729)
    (h89082 : (¬ p3950) ∨ p3146 ∨ (¬ p2685) ∨ (¬ p4729) ∨ p2373 ∨ (¬ p2696) ∨ p2230 ∨ (¬ p2449))
    : (¬ p2685) ∨ p2230 ∨ (¬ p3950) ∨ p3146 ∨ (¬ p2696) ∨ (¬ p2449) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2230) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4729 := h105429;
    (Or.elim h89082 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

end ElevenRUP
