import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step109379 (p2685 p2996 p3005 p3034 p3171 p3527 p4403 : Prop)
    (h93790 : (¬ p4403) ∨ (¬ p3005) ∨ p2685 ∨ (¬ p3034) ∨ (¬ p3171) ∨ p3527)
    (h102816 : p3034 ∨ (¬ p2996))
    : (¬ p2996) ∨ (¬ p3171) ∨ (¬ p4403) ∨ p2685 ∨ (¬ p3005) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3034) := (Or.elim h93790 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h102816 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109384 (p3193 p3233 p3379 p3830 : Prop)
    (h27477 : (¬ p3233) ∨ (¬ p3379) ∨ p3830)
    (h96853 : p3233 ∨ p3193)
    : p3193 ∨ p3830 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3233) := (Or.elim h27477 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h96853 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109385 (p2230 p2406 p3193 p3233 p3276 p3707 : Prop)
    (h91393 : p3276 ∨ (¬ p3707) ∨ (¬ p2230) ∨ p2406 ∨ (¬ p3233))
    (h96853 : p3233 ∨ p3193)
    : p3193 ∨ p3276 ∨ (¬ p3707) ∨ (¬ p2230) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3233) := (Or.elim h91393 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h96853 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109386 (p3193 p3233 p3276 p3707 p5160 p5217 : Prop)
    (h105493 : p5217)
    (h99812 : p3276 ∨ (¬ p3707) ∨ (¬ p5160) ∨ (¬ p3233) ∨ (¬ p5217))
    (h96853 : p3233 ∨ p3193)
    : p3193 ∨ p3276 ∨ (¬ p3707) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5217 := h105493;
    let u5 : (¬ p3233) := (Or.elim h99812 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96853 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109387 (p2230 p3193 p3233 p3276 p3347 p3707 p4953 : Prop)
    (h88929 : p3276 ∨ (¬ p3707) ∨ p2230 ∨ (¬ p3233) ∨ (¬ p3347) ∨ (¬ p4953))
    (h96853 : p3233 ∨ p3193)
    : p3193 ∨ p3276 ∨ (¬ p3707) ∨ (¬ p3347) ∨ p2230 ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3233) := (Or.elim h88929 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96853 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109389 (p2406 p3193 p3233 p3707 p4953 p5175 p5284 : Prop)
    (h96625 : (¬ p5284) ∨ (¬ p3707) ∨ (¬ p4953) ∨ (¬ p3233) ∨ p2406 ∨ (¬ p5175))
    (h96853 : p3233 ∨ p3193)
    : p3193 ∨ (¬ p3707) ∨ (¬ p5284) ∨ (¬ p5175) ∨ (¬ p4953) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3233) := (Or.elim h96625 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h96853 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109391 (p2254 p2331 p2363 p2668 p3193 p3233 p3276 p3379 p3707 p4332 : Prop)
    (h105366 : p2254)
    (h91392 : (¬ p3707) ∨ p3276 ∨ (¬ p2254) ∨ (¬ p3379) ∨ p2668 ∨ (¬ p3233) ∨ p2363 ∨ (¬ p4332) ∨ p2331)
    (h96853 : p3233 ∨ p3193)
    : p3193 ∨ p2363 ∨ (¬ p4332) ∨ p2668 ∨ p3276 ∨ (¬ p3707) ∨ (¬ p3379) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2254 := h105366;
    let u9 : (¬ p3233) := (Or.elim h91392 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (u7 r7))))))))))))))))));
    (Or.elim h96853 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109395 (p2177 p2255 p2311 p2341 p2641 p2651 p2667 p3193 p3233 p3276 p3707 p4116 p4276 p4635 : Prop)
    (h105367 : p2255)
    (h105516 : p4276)
    (h99487 : (¬ p3707) ∨ p3276 ∨ (¬ p4116) ∨ p2641 ∨ (¬ p3233) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2667) ∨ (¬ p2651) ∨ p2341 ∨ (¬ p4276) ∨ (¬ p2255) ∨ (¬ p4635))
    (h96853 : p3233 ∨ p3193)
    : p3193 ∨ p3276 ∨ p2341 ∨ p2641 ∨ (¬ p4635) ∨ (¬ p3707) ∨ (¬ p2667) ∨ (¬ p2651) ∨ (¬ p2177) ∨ (¬ p4116) ∨ (¬ p2311) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2255 := h105367;
    let u12 : p4276 := h105516;
    let u13 : (¬ p3233) := (Or.elim h99487 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u2 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u12))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (False.elim (r11 u4))))))))))))))))))))))))));
    (Or.elim h96853 (fun q0 => (False.elim (u13 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109396 (p2088 p2166 p2220 p2532 p2972 p4529 : Prop)
    (h76101 : (¬ p2972) ∨ p2088 ∨ (¬ p2532) ∨ (¬ p4529) ∨ p2166)
    (h96462 : p4529 ∨ p2220)
    : p2220 ∨ p2166 ∨ (¬ p2532) ∨ (¬ p2972) ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4529) := (Or.elim h76101 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96462 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109397 (p2088 p2220 p2373 p2532 p2982 p4529 : Prop)
    (h78908 : p2088 ∨ (¬ p2532) ∨ (¬ p4529) ∨ (¬ p2982) ∨ p2373)
    (h96462 : p4529 ∨ p2220)
    : p2220 ∨ p2373 ∨ (¬ p2532) ∨ p2088 ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4529) := (Or.elim h78908 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96462 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109401 (p2088 p2220 p2532 p3115 p3156 p4529 : Prop)
    (h96686 : (¬ p3115) ∨ p2088 ∨ (¬ p4529) ∨ (¬ p2532) ∨ p3156)
    (h96462 : p4529 ∨ p2220)
    : p2220 ∨ (¬ p2532) ∨ (¬ p3115) ∨ p2088 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4529) := (Or.elim h96686 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96462 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109402 (p2088 p2220 p2533 p3266 p3680 p4529 : Prop)
    (h98453 : (¬ p3680) ∨ p3266 ∨ (¬ p4529) ∨ p2088 ∨ (¬ p2533))
    (h96462 : p4529 ∨ p2220)
    : p2220 ∨ p3266 ∨ (¬ p3680) ∨ p2088 ∨ (¬ p2533) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4529) := (Or.elim h98453 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96462 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109411 (p2252 p2264 p2459 p2727 p2807 p3093 p3319 p3379 p4330 p4810 : Prop)
    (h106329 : p4330)
    (h84220 : (¬ p3319) ∨ p3379 ∨ p2459 ∨ (¬ p4330) ∨ (¬ p4810) ∨ (¬ p2252) ∨ (¬ p3093) ∨ p2807 ∨ p2264)
    (h102565 : p4810 ∨ p2727)
    : p2727 ∨ (¬ p3319) ∨ p2459 ∨ p2807 ∨ p2264 ∨ p3379 ∨ (¬ p3093) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4330 := h106329;
    let u9 : (¬ p4810) := (Or.elim h84220 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (False.elim (u4 r7))))))))))))))))));
    (Or.elim h102565 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109414 (p2252 p2264 p2459 p2504 p2727 p2807 p3093 p3379 p3564 p4330 p4810 : Prop)
    (h106329 : p4330)
    (h99351 : (¬ p3564) ∨ (¬ p2504) ∨ p2459 ∨ (¬ p4810) ∨ p2807 ∨ (¬ p3093) ∨ (¬ p2252) ∨ p3379 ∨ (¬ p4330) ∨ p2264)
    (h102565 : p4810 ∨ p2727)
    : p2727 ∨ (¬ p3564) ∨ p2264 ∨ p2807 ∨ p2459 ∨ p3379 ∨ (¬ p3093) ∨ (¬ p2252) ∨ (¬ p2504) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4330 := h106329;
    let u10 : (¬ p4810) := (Or.elim h99351 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u2 r8))))))))))))))))))));
    (Or.elim h102565 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109420 (p2132 p2619 p2881 p3425 p4344 p4901 : Prop)
    (h84634 : p2132 ∨ p2619 ∨ p3425 ∨ (¬ p4901) ∨ (¬ p4344))
    (h102591 : p4901 ∨ p2881)
    : p2881 ∨ p3425 ∨ p2619 ∨ (¬ p4344) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4901) := (Or.elim h84634 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102591 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109421 (p2373 p2406 p2881 p2922 p3569 p4901 : Prop)
    (h88806 : (¬ p2922) ∨ (¬ p3569) ∨ p2406 ∨ (¬ p4901) ∨ p2373)
    (h102591 : p4901 ∨ p2881)
    : p2881 ∨ p2373 ∨ p2406 ∨ (¬ p3569) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4901) := (Or.elim h88806 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h102591 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109422 (p2406 p2427 p2509 p2881 p3693 p4901 : Prop)
    (h62784 : (¬ p2406) ∨ (¬ p2427) ∨ (¬ p2509) ∨ (¬ p3693) ∨ (¬ p4901))
    (h102591 : p4901 ∨ p2881)
    : p2881 ∨ (¬ p2509) ∨ (¬ p2406) ∨ (¬ p3693) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4901) := (Or.elim h62784 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h102591 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109423 (p2839 p2870 p2881 p3537 p4740 p4901 : Prop)
    (h93751 : p3537 ∨ (¬ p4740) ∨ (¬ p2839) ∨ (¬ p4901) ∨ (¬ p2870))
    (h102591 : p4901 ∨ p2881)
    : p2881 ∨ (¬ p4740) ∨ p3537 ∨ (¬ p2839) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p4740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4901) := (Or.elim h93751 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102591 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109425 (p2881 p2992 p2996 p3156 p4333 p4901 : Prop)
    (h96066 : p3156 ∨ p2992 ∨ (¬ p4901) ∨ p2996 ∨ (¬ p4333))
    (h102591 : p4901 ∨ p2881)
    : p2881 ∨ (¬ p4333) ∨ p3156 ∨ p2996 ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4901) := (Or.elim h96066 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102591 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109426 (p2881 p2995 p3156 p3931 p4901 p5660 : Prop)
    (h99094 : (¬ p5660) ∨ (¬ p3931) ∨ (¬ p2995) ∨ (¬ p4901) ∨ p3156)
    (h102591 : p4901 ∨ p2881)
    : p2881 ∨ (¬ p3931) ∨ (¬ p5660) ∨ (¬ p2995) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4901) := (Or.elim h99094 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h102591 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109429 (p2870 p2881 p3073 p3146 p4243 p4492 p4901 : Prop)
    (h92993 : p3073 ∨ (¬ p3146) ∨ (¬ p4901) ∨ (¬ p2870) ∨ (¬ p4243) ∨ (¬ p4492))
    (h102591 : p4901 ∨ p2881)
    : p2881 ∨ p3073 ∨ (¬ p4492) ∨ (¬ p4243) ∨ (¬ p3146) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4901) := (Or.elim h92993 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h102591 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109432 (p2143 p3105 p4032 p5030 : Prop)
    (h109165 : (¬ p3105) ∨ (¬ p2143) ∨ (¬ p4032) ∨ (¬ p5030))
    (h102668 : p5030 ∨ (¬ p3105))
    : (¬ p3105) ∨ (¬ p2143) ∨ (¬ p4032) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5030) := (Or.elim h109165 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h102668 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109434 (p2839 p2982 p3105 p3599 p4885 p5030 : Prop)
    (h96653 : (¬ p3599) ∨ (¬ p5030) ∨ p2982 ∨ (¬ p4885) ∨ p2839)
    (h102668 : p5030 ∨ (¬ p3105))
    : (¬ p3105) ∨ (¬ p3599) ∨ p2982 ∨ (¬ p4885) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5030) := (Or.elim h96653 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h102668 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109439 (p2563 p2972 p3105 p3461 p3670 p4210 p5030 : Prop)
    (h91509 : p3670 ∨ (¬ p5030) ∨ (¬ p2563) ∨ (¬ p3461) ∨ p2972 ∨ (¬ p4210))
    (h102668 : p5030 ∨ (¬ p3105))
    : (¬ p3105) ∨ (¬ p3461) ∨ p2972 ∨ (¬ p4210) ∨ p3670 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5030) := (Or.elim h91509 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h102668 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109442 (p2136 p2241 p2417 p2744 p2933 p3105 p3366 p3399 p3461 p3670 p4032 p4625 p5030 : Prop)
    (h106503 : p2744)
    (h106455 : p4625)
    (h76730 : p3670 ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p5030) ∨ (¬ p2417) ∨ (¬ p2744) ∨ (¬ p4032) ∨ (¬ p2933) ∨ (¬ p2136) ∨ p2241 ∨ (¬ p4625) ∨ (¬ p3461))
    (h102668 : p5030 ∨ (¬ p3105))
    : (¬ p3105) ∨ p3670 ∨ (¬ p2933) ∨ (¬ p2417) ∨ (¬ p3461) ∨ (¬ p3366) ∨ (¬ p4032) ∨ p2241 ∨ (¬ p3399) ∨ (¬ p2136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    let u11 : p4625 := h106455;
    let u12 : (¬ p5030) := (Or.elim h76730 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u7 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (False.elim (r10 u4))))))))))))))))))))))));
    (Or.elim h102668 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109444 (p2341 p3516 p3945 p5294 p5295 : Prop)
    (h15511 : (¬ p2341) ∨ (¬ p3945) ∨ (¬ p5294) ∨ (¬ p5295))
    (h102645 : p5294 ∨ p3516)
    : p3516 ∨ (¬ p3945) ∨ (¬ p2341) ∨ (¬ p5295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5294) := (Or.elim h15511 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h102645 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109445 (p2341 p2761 p3516 p3773 p4666 p5294 : Prop)
    (h105658 : p4666)
    (h55952 : (¬ p2341) ∨ (¬ p2761) ∨ (¬ p3773) ∨ (¬ p4666) ∨ (¬ p5294))
    (h102645 : p5294 ∨ p3516)
    : p3516 ∨ (¬ p3773) ∨ (¬ p2341) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4666 := h105658;
    let u5 : (¬ p5294) := (Or.elim h55952 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h102645 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109447 (p2707 p2761 p3367 p3516 p3773 p3959 p5294 : Prop)
    (h88407 : (¬ p3773) ∨ (¬ p2761) ∨ (¬ p3367) ∨ p2707 ∨ (¬ p3959) ∨ (¬ p5294))
    (h102645 : p5294 ∨ p3516)
    : p3516 ∨ (¬ p2761) ∨ (¬ p3959) ∨ (¬ p3367) ∨ p2707 ∨ (¬ p3773) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5294) := (Or.elim h88407 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => r4))))))))));
    (Or.elim h102645 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109454 (p2192 p2255 p2761 p2946 p2996 p3125 p3412 p3516 p3773 p4155 p4621 p5294 : Prop)
    (h105367 : p2255)
    (h105407 : p4621)
    (h49670 : (¬ p2192) ∨ (¬ p2255) ∨ (¬ p2761) ∨ (¬ p2946) ∨ (¬ p2996) ∨ (¬ p3125) ∨ (¬ p3412) ∨ (¬ p3773) ∨ (¬ p4155) ∨ (¬ p4621) ∨ (¬ p5294))
    (h102645 : p5294 ∨ p3516)
    : p3516 ∨ (¬ p2996) ∨ (¬ p3773) ∨ (¬ p2192) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p4155) ∨ (¬ p2761) ∨ (¬ p3412) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2255 := h105367;
    let u10 : p4621 := h105407;
    let u11 : (¬ p5294) := (Or.elim h49670 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => r9))))))))))))))))))));
    (Or.elim h102645 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109456 (p3537 p3599 p3609 p5344 : Prop)
    (h94118 : (¬ p3537) ∨ p3599 ∨ (¬ p5344))
    (h96255 : p5344 ∨ (¬ p3609))
    : (¬ p3609) ∨ (¬ p3537) ∨ p3599 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5344) := (Or.elim h94118 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96255 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109457 (p3073 p3609 p5315 p5343 p5344 : Prop)
    (h94116 : (¬ p5315) ∨ p3073 ∨ (¬ p5343) ∨ (¬ p5344))
    (h96255 : p5344 ∨ (¬ p3609))
    : (¬ p3609) ∨ (¬ p5343) ∨ p3073 ∨ (¬ p5315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5344) := (Or.elim h94116 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    (Or.elim h96255 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109458 (p2098 p3609 p4234 p4398 p5344 : Prop)
    (h21094 : (¬ p2098) ∨ (¬ p4234) ∨ (¬ p4398) ∨ (¬ p5344))
    (h96255 : p5344 ∨ (¬ p3609))
    : (¬ p3609) ∨ (¬ p4234) ∨ (¬ p4398) ∨ (¬ p2098) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4234 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4398 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5344) := (Or.elim h21094 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h96255 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109459 (p3266 p3367 p3537 p3609 p3670 p5344 : Prop)
    (h89766 : p3266 ∨ (¬ p3537) ∨ (¬ p5344) ∨ p3367 ∨ (¬ p3670))
    (h96255 : p5344 ∨ (¬ p3609))
    : (¬ p3609) ∨ (¬ p3670) ∨ (¬ p3537) ∨ p3266 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5344) := (Or.elim h89766 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96255 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109460 (p2608 p3266 p3537 p3609 p3670 p5344 : Prop)
    (h89781 : (¬ p3670) ∨ p3266 ∨ (¬ p3537) ∨ (¬ p2608) ∨ (¬ p5344))
    (h96255 : p5344 ∨ (¬ p3609))
    : (¬ p3609) ∨ (¬ p3670) ∨ (¬ p3537) ∨ (¬ p2608) ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5344) := (Or.elim h89781 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h96255 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109461 (p2737 p3266 p3537 p3609 p3670 p5344 : Prop)
    (h89794 : (¬ p3670) ∨ p3266 ∨ p2737 ∨ (¬ p3537) ∨ (¬ p5344))
    (h96255 : p5344 ∨ (¬ p3609))
    : (¬ p3609) ∨ (¬ p3670) ∨ (¬ p3537) ∨ p3266 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5344) := (Or.elim h89794 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h96255 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109462 (p3146 p3266 p3609 p3670 p4746 p5344 : Prop)
    (h96676 : (¬ p3670) ∨ p3266 ∨ (¬ p4746) ∨ (¬ p5344) ∨ p3146)
    (h96255 : p5344 ∨ (¬ p3609))
    : (¬ p3609) ∨ (¬ p3670) ∨ p3146 ∨ p3266 ∨ (¬ p4746) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5344) := (Or.elim h96676 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96255 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109464 (p2850 p3232 p3609 p3670 p3707 p4354 p4953 p5344 : Prop)
    (h94120 : p3707 ∨ (¬ p3670) ∨ (¬ p5344) ∨ (¬ p4354) ∨ p2850 ∨ (¬ p4953) ∨ (¬ p3232))
    (h96255 : p5344 ∨ (¬ p3609))
    : (¬ p3609) ∨ (¬ p3232) ∨ (¬ p3670) ∨ p3707 ∨ p2850 ∨ (¬ p4354) ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4354 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5344) := (Or.elim h94120 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h96255 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109468 (p2696 p3619 p3755 p5453 : Prop)
    (h82930 : (¬ p3619) ∨ (¬ p5453) ∨ p2696)
    (h95229 : p5453 ∨ p3755)
    : p3755 ∨ (¬ p3619) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5453) := (Or.elim h82930 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h95229 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109469 (p2737 p3599 p3755 p5453 : Prop)
    (h96831 : (¬ p3599) ∨ (¬ p5453) ∨ p2737)
    (h95229 : p5453 ∨ p3755)
    : p3755 ∨ (¬ p3599) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5453) := (Or.elim h96831 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h95229 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109470 (p2685 p3286 p3506 p3670 p3755 p5453 : Prop)
    (h94249 : p3670 ∨ (¬ p3506) ∨ (¬ p3286) ∨ (¬ p5453) ∨ (¬ p2685))
    (h95229 : p5453 ∨ p3755)
    : p3755 ∨ (¬ p2685) ∨ (¬ p3506) ∨ (¬ p3286) ∨ p3670 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5453) := (Or.elim h94249 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h95229 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109476 (p3367 p3670 p3707 p3755 p4351 p4749 p5316 p5453 : Prop)
    (h105432 : p4749)
    (h91636 : p3670 ∨ (¬ p3707) ∨ (¬ p5316) ∨ (¬ p5453) ∨ (¬ p4351) ∨ (¬ p4749) ∨ p3367)
    (h95229 : p5453 ∨ p3755)
    : p3755 ∨ (¬ p3707) ∨ p3670 ∨ (¬ p4351) ∨ p3367 ∨ (¬ p5316) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4351 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4749 := h105432;
    let u7 : (¬ p5453) := (Or.elim h91636 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (u4 r5))))))))))))));
    (Or.elim h95229 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109480 (p3276 p4952 p5401 p5402 : Prop)
    (h108743 : (¬ p5401) ∨ p3276 ∨ (¬ p5402) ∨ (¬ p4952))
    (h9312 : (¬ p5401) ∨ p5402)
    : (¬ p5401) ∨ p3276 ∨ (¬ p4952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5401 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5402) := (Or.elim h108743 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h9312 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step109491 (p2497 p3193 p3226 p5153 : Prop)
    (h22388 : p2497 ∨ (¬ p3226) ∨ (¬ p5153))
    (h102813 : p3226 ∨ (¬ p3193))
    : (¬ p3193) ∨ p2497 ∨ (¬ p5153) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2497) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3226) := (Or.elim h22388 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h102813 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109503 (p2946 p3115 p3286 p4314 : Prop)
    (h93234 : (¬ p3286) ∨ (¬ p4314) ∨ p2946)
    (h96323 : p4314 ∨ p3115)
    : p3115 ∨ (¬ p3286) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4314) := (Or.elim h93234 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96323 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109504 (p2992 p3115 p3842 p4314 : Prop)
    (h94377 : (¬ p3842) ∨ p2992 ∨ (¬ p4314))
    (h96323 : p4314 ∨ p3115)
    : p3115 ∨ (¬ p3842) ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4314) := (Or.elim h94377 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96323 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109505 (p3115 p3136 p3755 p4314 : Prop)
    (h94992 : (¬ p3755) ∨ (¬ p4314) ∨ p3136)
    (h96323 : p4314 ∨ p3115)
    : p3115 ∨ (¬ p3755) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4314) := (Or.elim h94992 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96323 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109509 (p2972 p3115 p3680 p4314 p4960 p5284 : Prop)
    (h106209 : p4960)
    (h41854 : (¬ p2972) ∨ (¬ p3680) ∨ (¬ p4314) ∨ (¬ p4960) ∨ (¬ p5284))
    (h96323 : p4314 ∨ p3115)
    : p3115 ∨ (¬ p3680) ∨ (¬ p5284) ∨ (¬ p2972) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4960 := h106209;
    let u5 : (¬ p4314) := (Or.elim h41854 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96323 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109510 (p2241 p3115 p3707 p3830 p4314 p5284 : Prop)
    (h100439 : (¬ p5284) ∨ (¬ p3707) ∨ p2241 ∨ (¬ p3830) ∨ (¬ p4314))
    (h96323 : p4314 ∨ p3115)
    : p3115 ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p5284) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4314) := (Or.elim h100439 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h96323 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109514 (p2254 p2363 p2946 p3063 p3093 p3115 p3680 p4314 p5059 p5284 : Prop)
    (h105366 : p2254)
    (h93269 : (¬ p5284) ∨ (¬ p3063) ∨ p2946 ∨ (¬ p2363) ∨ (¬ p2254) ∨ (¬ p4314) ∨ (¬ p3093) ∨ (¬ p3680) ∨ (¬ p5059))
    (h96323 : p4314 ∨ p3115)
    : p3115 ∨ (¬ p3093) ∨ (¬ p5059) ∨ (¬ p3063) ∨ (¬ p3680) ∨ (¬ p5284) ∨ p2946 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2254 := h105366;
    let u9 : (¬ p4314) := (Or.elim h93269 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u2))))))))))))))))));
    (Or.elim h96323 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109516 (p2509 p3453 p4370 p4683 p4685 p5866 : Prop)
    (h108687 : (¬ p4683) ∨ (¬ p5866) ∨ (¬ p4370) ∨ (¬ p3453) ∨ (¬ p2509) ∨ (¬ p4685))
    (h7552 : (¬ p4683) ∨ p4685)
    : (¬ p4683) ∨ (¬ p5866) ∨ (¬ p4370) ∨ (¬ p3453) ∨ (¬ p2509) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4683 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4685) := (Or.elim h108687 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h7552 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step109517 (p2509 p3453 p4370 p4683 p4685 p5866 : Prop)
    (h108690 : p5866 ∨ p4683 ∨ (¬ p4370) ∨ (¬ p3453) ∨ (¬ p2509) ∨ (¬ p4685))
    (h12189 : p4685 ∨ p5866)
    : p5866 ∨ p4683 ∨ (¬ p4370) ∨ (¬ p3453) ∨ (¬ p2509) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5866) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4683) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4685) := (Or.elim h108690 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h12189 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109520 (p3105 p3670 p3680 p5026 : Prop)
    (h30310 : (¬ p3670) ∨ p3680 ∨ (¬ p5026))
    (h96326 : p5026 ∨ p3105)
    : p3105 ∨ (¬ p3670) ∨ p3680 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3105) := (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3680) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5026) := (Or.elim h30310 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96326 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109523 (p2132 p2982 p3105 p4232 p4882 p5026 : Prop)
    (h105453 : p4882)
    (h57440 : (¬ p2132) ∨ (¬ p2982) ∨ (¬ p4232) ∨ (¬ p4882) ∨ (¬ p5026))
    (h96326 : p5026 ∨ p3105)
    : p3105 ∨ (¬ p4232) ∨ (¬ p2982) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3105) := (fun h => hn (Or.inl h));
    let u1 : p4232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4882 := h105453;
    let u5 : (¬ p5026) := (Or.elim h57440 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96326 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109524 (p2132 p2860 p3105 p4232 p5026 p5043 : Prop)
    (h105471 : p5043)
    (h54389 : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p4232) ∨ (¬ p5026) ∨ (¬ p5043))
    (h96326 : p5026 ∨ p3105)
    : p3105 ∨ (¬ p4232) ∨ (¬ p2860) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3105) := (fun h => hn (Or.inl h));
    let u1 : p4232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5043 := h105471;
    let u5 : (¬ p5026) := (Or.elim h54389 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96326 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109531 (p2497 p3193 p3319 p5153 : Prop)
    (h109491 : (¬ p3193) ∨ p2497 ∨ (¬ p5153))
    (h96061 : p5153 ∨ (¬ p3319))
    : (¬ p3319) ∨ (¬ p3193) ∨ p2497 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2497) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5153) := (Or.elim h109491 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96061 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109532 (p3093 p3319 p3830 p5153 p5487 : Prop)
    (h108915 : p3830 ∨ (¬ p5153) ∨ (¬ p5487) ∨ (¬ p3093))
    (h96061 : p5153 ∨ (¬ p3319))
    : (¬ p3319) ∨ p3830 ∨ (¬ p5487) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5153) := (Or.elim h108915 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h96061 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109533 (p3319 p3461 p3707 p3923 p4025 p5153 : Prop)
    (h92330 : (¬ p3707) ∨ p3461 ∨ (¬ p3923) ∨ (¬ p5153) ∨ (¬ p4025))
    (h96061 : p5153 ∨ (¬ p3319))
    : (¬ p3319) ∨ (¬ p3707) ∨ (¬ p3923) ∨ p3461 ∨ (¬ p4025) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5153) := (Or.elim h92330 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96061 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109538 (p2751 p3319 p3707 p3755 p4759 p5153 p5284 : Prop)
    (h106343 : p2751)
    (h100415 : (¬ p5284) ∨ (¬ p3707) ∨ p3755 ∨ (¬ p2751) ∨ (¬ p4759) ∨ (¬ p5153))
    (h96061 : p5153 ∨ (¬ p3319))
    : (¬ p3319) ∨ (¬ p3707) ∨ p3755 ∨ (¬ p5284) ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    let u6 : (¬ p5153) := (Or.elim h100415 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h96061 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109542 (p3309 p3319 p3707 p4349 p4405 p4417 p5153 p5284 : Prop)
    (h105512 : p4405)
    (h94564 : (¬ p5284) ∨ (¬ p3707) ∨ p3309 ∨ (¬ p4349) ∨ (¬ p4405) ∨ (¬ p5153) ∨ (¬ p4417))
    (h96061 : p5153 ∨ (¬ p3319))
    : (¬ p3319) ∨ (¬ p4417) ∨ p3309 ∨ (¬ p3707) ∨ (¬ p4349) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4349 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4405 := h105512;
    let u7 : (¬ p5153) := (Or.elim h94564 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h96061 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109544 (p2761 p3516 p3773 p5299 : Prop)
    (h19866 : (¬ p2761) ∨ (¬ p3773) ∨ (¬ p5299))
    (h96270 : p5299 ∨ (¬ p3516))
    : (¬ p3516) ∨ (¬ p2761) ∨ (¬ p3773) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5299) := (Or.elim h19866 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96270 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109545 (p2122 p2449 p3483 p3516 p5299 p5379 : Prop)
    (h90251 : (¬ p5299) ∨ (¬ p3483) ∨ p2122 ∨ p2449 ∨ (¬ p5379))
    (h96270 : p5299 ∨ (¬ p3516))
    : (¬ p3516) ∨ p2122 ∨ p2449 ∨ (¬ p5379) ∨ (¬ p3483) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5299) := (Or.elim h90251 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96270 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109551 (p2295 p3246 p3323 p3516 p4556 p5299 p5379 : Prop)
    (h105399 : p4556)
    (h91761 : (¬ p3323) ∨ (¬ p5379) ∨ p3246 ∨ p2295 ∨ (¬ p4556) ∨ (¬ p5299))
    (h96270 : p5299 ∨ (¬ p3516))
    : (¬ p3516) ∨ p2295 ∨ (¬ p3323) ∨ (¬ p5379) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4556 := h105399;
    let u6 : (¬ p5299) := (Or.elim h91761 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h96270 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109552 (p2449 p3201 p3333 p3516 p4327 p5182 p5299 : Prop)
    (h105381 : p4327)
    (h95586 : (¬ p5299) ∨ (¬ p3333) ∨ (¬ p5182) ∨ p3201 ∨ (¬ p4327) ∨ p2449)
    (h96270 : p5299 ∨ (¬ p3516))
    : (¬ p3516) ∨ (¬ p5182) ∨ (¬ p3333) ∨ p2449 ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5182 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4327 := h105381;
    let u6 : (¬ p5299) := (Or.elim h95586 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h96270 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109553 (p2437 p3246 p3343 p3516 p4647 p5182 p5299 : Prop)
    (h105412 : p4647)
    (h95842 : (¬ p3343) ∨ (¬ p5182) ∨ (¬ p4647) ∨ (¬ p5299) ∨ p2437 ∨ p3246)
    (h96270 : p5299 ∨ (¬ p3516))
    : (¬ p3516) ∨ (¬ p5182) ∨ p2437 ∨ (¬ p3343) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5182 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4647 := h105412;
    let u6 : (¬ p5299) := (Or.elim h95842 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h96270 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109554 (p2417 p2870 p3105 p3516 p4277 p4323 p5299 : Prop)
    (h105380 : p4277)
    (h96748 : (¬ p5299) ∨ p2417 ∨ (¬ p3105) ∨ (¬ p4323) ∨ (¬ p4277) ∨ p2870)
    (h96270 : p5299 ∨ (¬ p3516))
    : (¬ p3516) ∨ (¬ p4323) ∨ p2417 ∨ p2870 ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4277 := h105380;
    let u6 : (¬ p5299) := (Or.elim h96748 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h96270 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109555 (p2498 p2553 p3246 p3319 p3516 p4556 p5299 p5379 : Prop)
    (h105399 : p4556)
    (h84173 : (¬ p5379) ∨ (¬ p5299) ∨ (¬ p3319) ∨ p2553 ∨ (¬ p4556) ∨ (¬ p2498) ∨ p3246)
    (h96270 : p5299 ∨ (¬ p3516))
    : (¬ p3516) ∨ (¬ p5379) ∨ (¬ p3319) ∨ p3246 ∨ p2553 ∨ (¬ p2498) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4556 := h105399;
    let u7 : (¬ p5299) := (Or.elim h84173 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (u3 r5))))))))))))));
    (Or.elim h96270 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109561 (p2210 p2972 p3830 p4942 p5487 : Prop)
    (h108914 : p3830 ∨ (¬ p5487) ∨ (¬ p2210) ∨ (¬ p4942))
    (h100455 : p4942 ∨ (¬ p2972))
    : (¬ p2972) ∨ p3830 ∨ (¬ p5487) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4942) := (Or.elim h108914 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h100455 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109562 (p2972 p3115 p3707 p4322 p4942 p4960 : Prop)
    (h106209 : p4960)
    (h83390 : (¬ p3707) ∨ (¬ p4322) ∨ (¬ p4942) ∨ p3115 ∨ (¬ p4960))
    (h100455 : p4942 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p3707) ∨ p3115 ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4960 := h106209;
    let u5 : (¬ p4942) := (Or.elim h83390 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h100455 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109563 (p2192 p2972 p3707 p4322 p4942 p5046 : Prop)
    (h105472 : p5046)
    (h83391 : (¬ p3707) ∨ (¬ p4322) ∨ (¬ p4942) ∨ (¬ p5046) ∨ p2192)
    (h100455 : p4942 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p3707) ∨ p2192 ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5046 := h105472;
    let u5 : (¬ p4942) := (Or.elim h83391 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h100455 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109564 (p2972 p3105 p3707 p4322 p4878 p4942 : Prop)
    (h105452 : p4878)
    (h84524 : (¬ p4322) ∨ (¬ p3707) ∨ (¬ p4942) ∨ p3105 ∨ (¬ p4878))
    (h100455 : p4942 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p3707) ∨ (¬ p4322) ∨ p3105 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4878 := h105452;
    let u5 : (¬ p4942) := (Or.elim h84524 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h100455 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109567 (p2563 p2972 p3707 p4039 p4205 p4632 p4942 p5284 : Prop)
    (h106257 : p4632)
    (h83389 : (¬ p4039) ∨ (¬ p5284) ∨ (¬ p4632) ∨ (¬ p4942) ∨ p2563 ∨ (¬ p4205) ∨ (¬ p3707))
    (h100455 : p4942 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p5284) ∨ p2563 ∨ (¬ p3707) ∨ (¬ p4205) ∨ (¬ p4039) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4205 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4039 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4632 := h106257;
    let u7 : (¬ p4942) := (Or.elim h83389 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u3))))))))))))));
    (Or.elim h100455 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109573 (p2210 p2417 p2598 p2972 p3201 p3707 p4322 p4395 p4736 p4942 : Prop)
    (h105431 : p4736)
    (h100078 : (¬ p3707) ∨ (¬ p4322) ∨ (¬ p4942) ∨ p3201 ∨ (¬ p2210) ∨ p2417 ∨ (¬ p4395) ∨ p2598 ∨ (¬ p4736))
    (h100455 : p4942 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p4395) ∨ (¬ p2210) ∨ p2417 ∨ p3201 ∨ (¬ p4322) ∨ (¬ p3707) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    let u9 : (¬ p4942) := (Or.elim h100078 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h100455 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109578 (p2470 p2717 p3201 p3389 p4383 p5087 : Prop)
    (h95967 : (¬ p5087) ∨ (¬ p2717) ∨ (¬ p4383) ∨ (¬ p3389) ∨ p2470)
    (h96305 : p5087 ∨ (¬ p3201))
    : (¬ p3201) ∨ (¬ p2717) ∨ p2470 ∨ (¬ p4383) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5087) := (Or.elim h95967 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96305 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109583 (p2341 p2509 p2922 p3201 p3577 p4383 p5087 : Prop)
    (h41067 : (¬ p2341) ∨ (¬ p2509) ∨ (¬ p2922) ∨ (¬ p3577) ∨ (¬ p4383) ∨ (¬ p5087))
    (h96305 : p5087 ∨ (¬ p3201))
    : (¬ p3201) ∨ (¬ p3577) ∨ (¬ p2341) ∨ (¬ p2509) ∨ (¬ p4383) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5087) := (Or.elim h41067 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h96305 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109584 (p2437 p2481 p2717 p3083 p3201 p3960 p5087 : Prop)
    (h95968 : (¬ p2481) ∨ (¬ p3960) ∨ (¬ p2437) ∨ p3083 ∨ (¬ p2717) ∨ (¬ p5087))
    (h96305 : p5087 ∨ (¬ p3201))
    : (¬ p3201) ∨ (¬ p2717) ∨ p3083 ∨ (¬ p3960) ∨ (¬ p2481) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2481 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5087) := (Or.elim h95968 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => r4))))))))));
    (Or.elim h96305 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109589 (p2459 p3266 p3941 p5116 : Prop)
    (h85052 : (¬ p3941) ∨ (¬ p5116) ∨ p2459)
    (h96295 : p5116 ∨ p3266)
    : p3266 ∨ (¬ p3941) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5116) := (Or.elim h85052 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96295 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109591 (p3146 p3266 p3969 p5116 : Prop)
    (h98690 : (¬ p3969) ∨ (¬ p5116) ∨ p3146)
    (h96295 : p5116 ∨ p3266)
    : p3266 ∨ (¬ p3969) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5116) := (Or.elim h98690 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96295 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109604 (p2396 p2707 p3434 p3599 p4477 p5233 : Prop)
    (h95954 : (¬ p3599) ∨ (¬ p5233) ∨ p2707 ∨ p2396 ∨ (¬ p4477))
    (h96173 : p5233 ∨ (¬ p3434))
    : (¬ p3434) ∨ p2707 ∨ (¬ p3599) ∨ (¬ p4477) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5233) := (Or.elim h95954 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96173 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109605 (p2707 p3246 p3434 p3599 p4898 p5233 : Prop)
    (h105455 : p4898)
    (h96610 : (¬ p3599) ∨ (¬ p5233) ∨ p2707 ∨ p3246 ∨ (¬ p4898))
    (h96173 : p5233 ∨ (¬ p3434))
    : (¬ p3434) ∨ p3246 ∨ p2707 ∨ (¬ p3599) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4898 := h105455;
    let u5 : (¬ p5233) := (Or.elim h96610 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96173 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109606 (p2449 p2685 p2707 p3434 p3599 p5233 : Prop)
    (h108315 : (¬ p2685) ∨ p2707 ∨ p2449 ∨ (¬ p3599) ∨ (¬ p5233))
    (h96173 : p5233 ∨ (¬ p3434))
    : (¬ p3434) ∨ (¬ p2685) ∨ p2707 ∨ p2449 ∨ (¬ p3599) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5233) := (Or.elim h108315 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96173 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109609 (p2807 p3246 p3286 p3434 p4362 p5233 p5454 : Prop)
    (h106173 : p4362)
    (h93223 : (¬ p5233) ∨ (¬ p5454) ∨ (¬ p3286) ∨ (¬ p4362) ∨ p3246 ∨ p2807)
    (h96173 : p5233 ∨ (¬ p3434))
    : (¬ p3434) ∨ (¬ p5454) ∨ p3246 ∨ p2807 ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5454 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4362 := h106173;
    let u6 : (¬ p5233) := (Or.elim h93223 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h96173 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109615 (p2284 p2761 p2946 p3361 p3425 p3434 p3619 p4393 p4778 p5233 p5254 : Prop)
    (h94126 : (¬ p3619) ∨ (¬ p4393) ∨ (¬ p3425) ∨ (¬ p3361) ∨ p2946 ∨ p2284 ∨ (¬ p4778) ∨ (¬ p5233) ∨ (¬ p5254) ∨ (¬ p2761))
    (h96173 : p5233 ∨ (¬ p3434))
    : (¬ p3434) ∨ (¬ p5254) ∨ (¬ p3425) ∨ (¬ p2761) ∨ (¬ p3361) ∨ (¬ p3619) ∨ (¬ p4393) ∨ p2946 ∨ p2284 ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p5233) := (Or.elim h94126 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u3))))))))))))))))))));
    (Or.elim h96173 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109621 (p2274 p2307 p2630 p2651 p2787 p3125 p3323 p3755 p4117 p5276 : Prop)
    (h105374 : p2787)
    (h94978 : (¬ p3755) ∨ (¬ p5276) ∨ p3125 ∨ p2630 ∨ (¬ p2651) ∨ (¬ p4117) ∨ p2307 ∨ (¬ p2787) ∨ (¬ p2274))
    (h102540 : p5276 ∨ p3323)
    : p3323 ∨ (¬ p3755) ∨ p2307 ∨ (¬ p4117) ∨ p2630 ∨ (¬ p2274) ∨ (¬ p2651) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2787 := h105374;
    let u9 : (¬ p5276) := (Or.elim h94978 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u5))))))))))))))))));
    (Or.elim h102540 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109624 (p2230 p2563 p2685 p2807 p3125 p3323 p3755 p4117 p4729 p5276 : Prop)
    (h105429 : p4729)
    (h95041 : (¬ p3755) ∨ (¬ p5276) ∨ (¬ p2807) ∨ (¬ p4729) ∨ p2685 ∨ p2563 ∨ (¬ p4117) ∨ p3125 ∨ p2230)
    (h102540 : p5276 ∨ p3323)
    : p3323 ∨ (¬ p3755) ∨ (¬ p2807) ∨ p2230 ∨ p3125 ∨ p2685 ∨ p2563 ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4729 := h105429;
    let u9 : (¬ p5276) := (Or.elim h95041 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (u3 r7))))))))))))))))));
    (Or.elim h102540 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109631 (p5597 p5598 p5600 p6157 : Prop)
    (h108530 : (¬ p5597) ∨ (¬ p5600) ∨ (¬ p6157) ∨ (¬ p5598))
    (h9862 : (¬ p5597) ∨ p5598)
    : (¬ p5597) ∨ (¬ p5600) ∨ (¬ p6157) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5597 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5598) := (Or.elim h108530 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h9862 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step109632 (p5597 p5598 p5600 p6157 : Prop)
    (h108531 : p6157 ∨ (¬ p5600) ∨ p5597 ∨ (¬ p5598))
    (h14521 : p5598 ∨ p6157)
    : p6157 ∨ (¬ p5600) ∨ p5597 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6157) := (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5597) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5598) := (Or.elim h108531 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h14521 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109640 (p2946 p3115 p3286 p5038 : Prop)
    (h24468 : (¬ p2946) ∨ p3286 ∨ (¬ p5038))
    (h102578 : p5038 ∨ (¬ p3115))
    : (¬ p3115) ∨ p3286 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5038) := (Or.elim h24468 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h102578 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109644 (p2982 p3115 p3506 p4322 p4705 p5038 : Prop)
    (h106238 : p4705)
    (h95943 : (¬ p4322) ∨ (¬ p5038) ∨ (¬ p3506) ∨ (¬ p4705) ∨ p2982)
    (h102578 : p5038 ∨ (¬ p3115))
    : (¬ p3115) ∨ (¬ p3506) ∨ (¬ p4322) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4705 := h106238;
    let u5 : (¬ p5038) := (Or.elim h95943 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102578 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109647 (p2284 p3115 p3276 p3506 p4952 p5038 p5046 : Prop)
    (h105472 : p5046)
    (h95942 : p3276 ∨ (¬ p5038) ∨ p2284 ∨ (¬ p5046) ∨ (¬ p3506) ∨ (¬ p4952))
    (h102578 : p5038 ∨ (¬ p3115))
    : (¬ p3115) ∨ p3276 ∨ p2284 ∨ (¬ p3506) ∨ (¬ p4952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5046 := h105472;
    let u6 : (¬ p5038) := (Or.elim h95942 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h102578 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109651 (p2249 p2331 p2396 p2992 p3115 p3309 p3506 p3922 p4322 p4395 p5038 : Prop)
    (h106513 : p2249)
    (h100921 : (¬ p4322) ∨ (¬ p3506) ∨ (¬ p4395) ∨ p3309 ∨ p2331 ∨ (¬ p5038) ∨ (¬ p2249) ∨ (¬ p2992) ∨ (¬ p3922) ∨ p2396)
    (h102578 : p5038 ∨ (¬ p3115))
    : (¬ p3115) ∨ p3309 ∨ (¬ p3506) ∨ p2331 ∨ (¬ p2992) ∨ (¬ p4322) ∨ p2396 ∨ (¬ p3922) ∨ (¬ p4395) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2249 := h106513;
    let u10 : (¬ p5038) := (Or.elim h100921 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (u6 r8))))))))))))))))))));
    (Or.elim h102578 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109652 (p2246 p2352 p2363 p2573 p2749 p2946 p3115 p3347 p3506 p4322 p4450 p5038 : Prop)
    (h88900 : (¬ p5038) ∨ p2363 ∨ (¬ p3347) ∨ p2352 ∨ p2573 ∨ (¬ p2246) ∨ (¬ p4450) ∨ (¬ p2749) ∨ (¬ p2946) ∨ (¬ p4322) ∨ (¬ p3506))
    (h102578 : p5038 ∨ (¬ p3115))
    : (¬ p3115) ∨ p2573 ∨ (¬ p3506) ∨ p2352 ∨ p2363 ∨ (¬ p2946) ∨ (¬ p4322) ∨ (¬ p2246) ∨ (¬ p3347) ∨ (¬ p2749) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p5038) := (Or.elim h88900 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u2))))))))))))))))))))));
    (Or.elim h102578 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109662 (p3146 p3266 p3461 p3969 p4330 p5121 : Prop)
    (h106329 : p4330)
    (h96647 : (¬ p3969) ∨ (¬ p5121) ∨ p3461 ∨ (¬ p4330) ∨ p3146)
    (h102658 : p5121 ∨ (¬ p3266))
    : (¬ p3266) ∨ p3461 ∨ (¬ p3969) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4330 := h106329;
    let u5 : (¬ p5121) := (Or.elim h96647 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102658 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109671 (p2753 p3425 p3434 p3599 p5234 : Prop)
    (h96608 : p3599 ∨ (¬ p2753) ∨ p3425 ∨ (¬ p5234))
    (h96174 : p5234 ∨ (¬ p3434))
    : (¬ p3434) ∨ p3599 ∨ p3425 ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5234) := (Or.elim h96608 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h96174 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109672 (p2707 p2737 p2761 p3434 p3670 p5234 : Prop)
    (h81307 : (¬ p2707) ∨ p2737 ∨ (¬ p5234) ∨ p2761 ∨ (¬ p3670))
    (h96174 : p5234 ∨ (¬ p3434))
    : (¬ p3434) ∨ (¬ p2707) ∨ p2737 ∨ p2761 ∨ (¬ p3670) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5234) := (Or.elim h81307 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96174 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109674 (p2717 p2761 p3434 p3670 p4668 p5234 : Prop)
    (h105414 : p4668)
    (h97045 : (¬ p3670) ∨ p2761 ∨ p2717 ∨ (¬ p5234) ∨ (¬ p4668))
    (h96174 : p5234 ∨ (¬ p3434))
    : (¬ p3434) ∨ p2761 ∨ (¬ p3670) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4668 := h105414;
    let u5 : (¬ p5234) := (Or.elim h97045 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96174 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109677 (p2246 p2749 p2807 p3434 p3599 p4777 p5234 : Prop)
    (h102409 : p3599 ∨ (¬ p2246) ∨ (¬ p2749) ∨ (¬ p5234) ∨ (¬ p2807) ∨ (¬ p4777))
    (h96174 : p5234 ∨ (¬ p3434))
    : (¬ p3434) ∨ (¬ p4777) ∨ p3599 ∨ (¬ p2246) ∨ (¬ p2749) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5234) := (Or.elim h102409 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h96174 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109685 (p3537 p4288 p4967 p5315 : Prop)
    (h33040 : p4288 ∨ (¬ p4967) ∨ (¬ p5315))
    (h96264 : p5315 ∨ (¬ p3537))
    : (¬ p3537) ∨ p4288 ∨ (¬ p4967) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4288) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4967 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5315) := (Or.elim h33040 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96264 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109688 (p3073 p3537 p3609 p5315 p5343 : Prop)
    (h109457 : (¬ p3609) ∨ (¬ p5343) ∨ p3073 ∨ (¬ p5315))
    (h96264 : p5315 ∨ (¬ p3537))
    : (¬ p3537) ∨ (¬ p3609) ∨ (¬ p5343) ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5315) := (Or.elim h109457 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => r2))))));
    (Or.elim h96264 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109691 (p2528 p2608 p3449 p3537 p3609 p5315 : Prop)
    (h95928 : (¬ p5315) ∨ (¬ p3609) ∨ p2608 ∨ (¬ p3449) ∨ p2528)
    (h96264 : p5315 ∨ (¬ p3537))
    : (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3449) ∨ p2608 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5315) := (Or.elim h95928 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96264 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109692 (p3537 p3858 p4967 p5315 p5590 p5600 : Prop)
    (h36241 : (¬ p3858) ∨ (¬ p4967) ∨ (¬ p5315) ∨ (¬ p5590) ∨ p5600)
    (h96264 : p5315 ∨ (¬ p3537))
    : (¬ p3537) ∨ (¬ p4967) ∨ (¬ p5590) ∨ p5600 ∨ (¬ p3858) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4967 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p5600) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3858 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5315) := (Or.elim h36241 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96264 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109697 (p2088 p2578 p2870 p3073 p3096 p3537 p4114 p4359 p4558 p5315 : Prop)
    (h105400 : p4558)
    (h95927 : (¬ p4114) ∨ (¬ p5315) ∨ (¬ p2088) ∨ (¬ p2578) ∨ p3073 ∨ (¬ p4558) ∨ (¬ p2870) ∨ (¬ p3096) ∨ (¬ p4359))
    (h96264 : p5315 ∨ (¬ p3537))
    : (¬ p3537) ∨ p3073 ∨ (¬ p2088) ∨ (¬ p4359) ∨ (¬ p3096) ∨ (¬ p2578) ∨ (¬ p4114) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4558 := h105400;
    let u9 : (¬ p5315) := (Or.elim h95927 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u3))))))))))))))))));
    (Or.elim h96264 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109700 (p3791 p4139 p4140 p5659 : Prop)
    (h108362 : (¬ p5659) ∨ (¬ p3791) ∨ (¬ p4139) ∨ (¬ p4140))
    (h10118 : p4139 ∨ (¬ p5659))
    : (¬ p5659) ∨ (¬ p3791) ∨ (¬ p4140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5659 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4139) := (Or.elim h108362 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h10118 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109701 (p4139 p5659 p5660 p6172 : Prop)
    (h108568 : (¬ p5659) ∨ (¬ p5660) ∨ (¬ p6172) ∨ (¬ p4139))
    (h10118 : p4139 ∨ (¬ p5659))
    : (¬ p5659) ∨ (¬ p5660) ∨ (¬ p6172) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5659 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4139) := (Or.elim h108568 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h10118 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109703 (p4139 p5659 p5660 p6172 : Prop)
    (h108569 : p6172 ∨ (¬ p5660) ∨ p5659 ∨ (¬ p4139))
    (h15000 : p4139 ∨ p6172)
    : p6172 ∨ (¬ p5660) ∨ p5659 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5659) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4139) := (Or.elim h108569 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h15000 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109714 (p3093 p3319 p3830 p5487 : Prop)
    (h109532 : (¬ p3319) ∨ p3830 ∨ (¬ p5487) ∨ (¬ p3093))
    (h96232 : p5487 ∨ p3830)
    : (¬ p3319) ∨ p3830 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5487) := (Or.elim h109532 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96232 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step109715 (p2210 p2972 p3830 p5487 : Prop)
    (h109561 : (¬ p2972) ∨ p3830 ∨ (¬ p5487) ∨ (¬ p2210))
    (h96232 : p5487 ∨ p3830)
    : (¬ p2972) ∨ p3830 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5487) := (Or.elim h109561 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96232 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step109718 (p3707 p3767 p3830 p5487 : Prop)
    (h96537 : p3707 ∨ (¬ p5487) ∨ (¬ p3767))
    (h96232 : p5487 ∨ p3830)
    : p3830 ∨ p3707 ∨ (¬ p3767) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5487) := (Or.elim h96537 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96232 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109737 (p2088 p2459 p3322 p3461 p3767 p4133 p4456 : Prop)
    (h105712 : p4133)
    (h82456 : (¬ p3767) ∨ (¬ p3322) ∨ p3461 ∨ (¬ p4133) ∨ (¬ p2459) ∨ (¬ p4456))
    (h102704 : p4456 ∨ p2088)
    : p2088 ∨ (¬ p3767) ∨ p3461 ∨ (¬ p2459) ∨ (¬ p3322) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4133 := h105712;
    let u6 : (¬ p4456) := (Or.elim h82456 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => r4))))))))));
    (Or.elim h102704 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109738 (p2088 p2373 p2982 p3256 p4043 p4209 p4456 : Prop)
    (h92059 : (¬ p4209) ∨ (¬ p4456) ∨ (¬ p2373) ∨ (¬ p3256) ∨ (¬ p4043) ∨ p2982)
    (h102704 : p4456 ∨ p2088)
    : p2088 ∨ (¬ p4043) ∨ (¬ p2373) ∨ (¬ p4209) ∨ (¬ p3256) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : p4043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4209 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4456) := (Or.elim h92059 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h102704 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109741 (p2088 p2761 p3146 p3657 p3767 p4456 p4905 : Prop)
    (h105995 : p4905)
    (h96688 : (¬ p3767) ∨ (¬ p4456) ∨ p2761 ∨ (¬ p3657) ∨ (¬ p4905) ∨ (¬ p3146))
    (h102704 : p4456 ∨ p2088)
    : p2088 ∨ p2761 ∨ (¬ p3767) ∨ (¬ p3146) ∨ (¬ p3657) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4905 := h105995;
    let u6 : (¬ p4456) := (Or.elim h96688 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h102704 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109742 (p2088 p3005 p3146 p3297 p3755 p4456 p5063 : Prop)
    (h105474 : p5063)
    (h96689 : p3755 ∨ (¬ p4456) ∨ (¬ p3297) ∨ (¬ p3005) ∨ (¬ p3146) ∨ (¬ p5063))
    (h102704 : p4456 ∨ p2088)
    : p2088 ∨ p3755 ∨ (¬ p3005) ∨ (¬ p3146) ∨ (¬ p3297) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3297 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5063 := h105474;
    let u6 : (¬ p4456) := (Or.elim h96689 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102704 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109744 (p2088 p3146 p3322 p3461 p3767 p4134 p4456 : Prop)
    (h105379 : p4134)
    (h96691 : (¬ p3767) ∨ (¬ p3322) ∨ (¬ p3146) ∨ (¬ p4134) ∨ (¬ p4456) ∨ p3461)
    (h102704 : p4456 ∨ p2088)
    : p2088 ∨ (¬ p3767) ∨ p3461 ∨ (¬ p3146) ∨ (¬ p3322) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4134 := h105379;
    let u6 : (¬ p4456) := (Or.elim h96691 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u2 r4))))))))))));
    (Or.elim h102704 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109749 (p3343 p4636 p4656 p5171 : Prop)
    (h27279 : (¬ p4636) ∨ p4656 ∨ (¬ p5171))
    (h96282 : p5171 ∨ p3343)
    : p3343 ∨ p4656 ∨ (¬ p4636) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4656) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5171) := (Or.elim h27279 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h96282 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109750 (p3276 p3343 p3506 p5171 : Prop)
    (h96629 : p3276 ∨ (¬ p3506) ∨ (¬ p5171))
    (h96282 : p5171 ∨ p3343)
    : p3343 ∨ p3276 ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5171) := (Or.elim h96629 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96282 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109751 (p2663 p3286 p3343 p3355 p5171 : Prop)
    (h96626 : (¬ p5171) ∨ (¬ p3355) ∨ (¬ p2663) ∨ p3286)
    (h96282 : p5171 ∨ p3343)
    : p3343 ∨ p3286 ∨ (¬ p2663) ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5171) := (Or.elim h96626 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u1 r2))))))));
    (Or.elim h96282 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109752 (p3343 p3422 p4343 p4422 p5170 p5171 : Prop)
    (h21566 : (¬ p3422) ∨ (¬ p4343) ∨ (¬ p4422) ∨ (¬ p5170) ∨ (¬ p5171))
    (h96282 : p5171 ∨ p3343)
    : p3343 ∨ (¬ p4422) ∨ (¬ p4343) ∨ (¬ p5170) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5171) := (Or.elim h21566 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h96282 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109753 (p2440 p2727 p3343 p3848 p4949 p5171 : Prop)
    (h105463 : p4949)
    (h82312 : (¬ p3848) ∨ (¬ p2727) ∨ (¬ p4949) ∨ p2440 ∨ (¬ p5171))
    (h96282 : p5171 ∨ p3343)
    : p3343 ∨ (¬ p3848) ∨ (¬ p2727) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4949 := h105463;
    let u5 : (¬ p5171) := (Or.elim h82312 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h96282 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109756 (p2651 p2727 p3276 p3286 p3343 p5171 : Prop)
    (h96627 : p3276 ∨ p3286 ∨ (¬ p2651) ∨ (¬ p5171) ∨ p2727)
    (h96282 : p5171 ∨ p3343)
    : p3343 ∨ p3286 ∨ (¬ p2651) ∨ p2727 ∨ p3276 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5171) := (Or.elim h96627 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96282 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109757 (p2630 p2651 p3276 p3343 p3755 p5171 : Prop)
    (h98189 : p3276 ∨ p3755 ∨ (¬ p5171) ∨ (¬ p2630) ∨ p2651)
    (h96282 : p5171 ∨ p3343)
    : p3343 ∨ p3755 ∨ (¬ p2630) ∨ p3276 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5171) := (Or.elim h98189 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96282 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109758 (p2630 p2651 p3276 p3286 p3343 p5171 : Prop)
    (h100576 : p3286 ∨ p3276 ∨ p2630 ∨ (¬ p2651) ∨ (¬ p5171))
    (h96282 : p5171 ∨ p3343)
    : p3343 ∨ p3286 ∨ p3276 ∨ (¬ p2651) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5171) := (Or.elim h100576 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h96282 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109759 (p2331 p3286 p3319 p3343 p4319 p5171 p5325 : Prop)
    (h84205 : (¬ p3319) ∨ p3286 ∨ (¬ p5171) ∨ (¬ p4319) ∨ (¬ p5325) ∨ (¬ p2331))
    (h96282 : p5171 ∨ p3343)
    : p3343 ∨ (¬ p5325) ∨ (¬ p2331) ∨ (¬ p3319) ∨ (¬ p4319) ∨ p3286 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p5325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5171) := (Or.elim h84205 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96282 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109761 (p2245 p2406 p3286 p3343 p3379 p4949 p5171 : Prop)
    (h105463 : p4949)
    (h91101 : (¬ p2245) ∨ p3286 ∨ (¬ p5171) ∨ (¬ p3379) ∨ (¬ p4949) ∨ (¬ p2406))
    (h96282 : p5171 ∨ p3343)
    : p3343 ∨ p3286 ∨ (¬ p2245) ∨ (¬ p2406) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4949 := h105463;
    let u6 : (¬ p5171) := (Or.elim h91101 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h96282 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109764 (p2630 p2651 p3212 p3266 p3343 p3366 p3370 p3680 p3755 p4236 p4377 p4697 p5171 : Prop)
    (h106170 : p4377)
    (h86958 : (¬ p3370) ∨ p3266 ∨ (¬ p2630) ∨ (¬ p4377) ∨ (¬ p3680) ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p4697) ∨ p3755 ∨ p2651 ∨ (¬ p5171) ∨ (¬ p3212))
    (h96282 : p5171 ∨ p3343)
    : p3343 ∨ (¬ p3680) ∨ (¬ p4697) ∨ p3266 ∨ (¬ p3366) ∨ p3755 ∨ (¬ p4236) ∨ (¬ p3212) ∨ p2651 ∨ (¬ p3370) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4377 := h106170;
    let u12 : (¬ p5171) := (Or.elim h86958 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u8 q9))) (fun r9 => (Or.elim r9 (fun q10 => q10) (fun r10 => (False.elim (r10 u7))))))))))))))))))))))));
    (Or.elim h96282 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109765 (p2156 p2252 p2274 p2396 p2630 p2651 p2741 p3343 p3370 p3755 p4377 p4641 p5171 : Prop)
    (h106170 : p4377)
    (h87052 : (¬ p2396) ∨ p3755 ∨ (¬ p4377) ∨ (¬ p2156) ∨ (¬ p5171) ∨ (¬ p2274) ∨ (¬ p2252) ∨ p2651 ∨ (¬ p4641) ∨ (¬ p2630) ∨ (¬ p2741) ∨ (¬ p3370))
    (h96282 : p5171 ∨ p3343)
    : p3343 ∨ (¬ p2396) ∨ p3755 ∨ (¬ p2274) ∨ (¬ p4641) ∨ (¬ p2156) ∨ (¬ p3370) ∨ (¬ p2252) ∨ (¬ p2741) ∨ p2651 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4377 := h106170;
    let u12 : (¬ p5171) := (Or.elim h87052 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u9 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u8))) (fun r10 => (False.elim (r10 u6))))))))))))))))))))))));
    (Or.elim h96282 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109768 (p2284 p3115 p3125 p4205 : Prop)
    (h95343 : (¬ p3115) ∨ (¬ p4205) ∨ p2284)
    (h102546 : p4205 ∨ p3125)
    : p3125 ∨ p2284 ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4205) := (Or.elim h95343 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h102546 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109770 (p2156 p3125 p3212 p4205 : Prop)
    (h95349 : (¬ p3212) ∨ (¬ p4205) ∨ p2156)
    (h102546 : p4205 ∨ p3125)
    : p3125 ∨ p2156 ∨ (¬ p3212) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4205) := (Or.elim h95349 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h102546 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109771 (p2563 p2982 p3125 p4205 : Prop)
    (h95353 : (¬ p2982) ∨ (¬ p4205) ∨ p2563)
    (h102546 : p4205 ∨ p3125)
    : p3125 ∨ p2563 ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4205) := (Or.elim h95353 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h102546 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109773 (p2156 p2972 p3125 p3645 p4205 : Prop)
    (h95348 : (¬ p2972) ∨ (¬ p4205) ∨ (¬ p3645) ∨ p2156)
    (h102546 : p4205 ∨ p3125)
    : p3125 ∨ p2156 ∨ (¬ p3645) ∨ (¬ p2972) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4205) := (Or.elim h95348 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u1 r2))))))));
    (Or.elim h102546 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109776 (p2274 p3125 p3461 p4205 p4322 p4620 : Prop)
    (h41197 : (¬ p2274) ∨ (¬ p3461) ∨ (¬ p4205) ∨ (¬ p4322) ∨ (¬ p4620))
    (h102546 : p4205 ∨ p3125)
    : p3125 ∨ (¬ p4322) ∨ (¬ p3461) ∨ (¬ p4620) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4205) := (Or.elim h41197 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102546 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109781 (p2563 p2972 p3125 p3707 p4039 p4205 p5284 : Prop)
    (h109567 : (¬ p2972) ∨ (¬ p5284) ∨ p2563 ∨ (¬ p3707) ∨ (¬ p4205) ∨ (¬ p4039))
    (h102546 : p4205 ∨ p3125)
    : p3125 ∨ (¬ p2972) ∨ (¬ p5284) ∨ p2563 ∨ (¬ p3707) ∨ (¬ p4039) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4039 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4205) := (Or.elim h109567 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102546 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109785 (p2156 p2696 p3125 p3425 p3434 p3461 p3645 p4030 p4202 p4205 p4322 p4625 p4752 : Prop)
    (h105434 : p4752)
    (h106455 : p4625)
    (h85558 : p3425 ∨ (¬ p4322) ∨ (¬ p4202) ∨ (¬ p4752) ∨ (¬ p4625) ∨ (¬ p3434) ∨ (¬ p3645) ∨ p2156 ∨ (¬ p4030) ∨ (¬ p3461) ∨ (¬ p4205) ∨ p2696)
    (h102546 : p4205 ∨ p3125)
    : p3125 ∨ (¬ p3461) ∨ (¬ p3434) ∨ p3425 ∨ (¬ p4202) ∨ (¬ p4322) ∨ (¬ p3645) ∨ (¬ p4030) ∨ p2156 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4752 := h105434;
    let u11 : p4625 := h106455;
    let u12 : (¬ p4205) := (Or.elim h85558 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (Or.elim r9 (fun q10 => q10) (fun r10 => (False.elim (u9 r10))))))))))))))))))))))));
    (Or.elim h102546 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109786 (p3073 p3266 p3707 p4352 : Prop)
    (h84055 : p3707 ∨ (¬ p3266) ∨ (¬ p4352))
    (h96330 : p4352 ∨ (¬ p3073))
    : (¬ p3073) ∨ p3707 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4352) := (Or.elim h84055 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96330 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109788 (p3073 p3256 p4351 p4352 p5074 : Prop)
    (h95068 : (¬ p5074) ∨ p3256 ∨ (¬ p4351) ∨ (¬ p4352))
    (h96330 : p4352 ∨ (¬ p3073))
    : (¬ p3073) ∨ (¬ p5074) ∨ p3256 ∨ (¬ p4351) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5074 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4351 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4352) := (Or.elim h95068 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h96330 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109789 (p3073 p3609 p4351 p4352 p4353 : Prop)
    (h96214 : (¬ p4353) ∨ p3609 ∨ (¬ p4352) ∨ (¬ p4351))
    (h96330 : p4352 ∨ (¬ p3073))
    : (¬ p3073) ∨ (¬ p4351) ∨ p3609 ∨ (¬ p4353) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4351 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4353 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4352) := (Or.elim h96214 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h96330 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109791 (p2363 p3073 p3449 p3830 p4352 p4998 : Prop)
    (h95767 : (¬ p4352) ∨ p3449 ∨ (¬ p3830) ∨ (¬ p4998) ∨ p2363)
    (h96330 : p4352 ∨ (¬ p3073))
    : (¬ p3073) ∨ p2363 ∨ (¬ p3830) ∨ p3449 ∨ (¬ p4998) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4352) := (Or.elim h95767 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96330 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109793 (p3073 p3146 p3449 p3830 p4352 p4498 : Prop)
    (h95770 : p3146 ∨ (¬ p4352) ∨ p3449 ∨ (¬ p4498) ∨ (¬ p3830))
    (h96330 : p4352 ∨ (¬ p3073))
    : (¬ p3073) ∨ p3146 ∨ (¬ p3830) ∨ p3449 ∨ (¬ p4498) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4352) := (Or.elim h95770 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96330 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109808 (p2088 p3178 p3755 p3767 p4461 p4790 p5284 : Prop)
    (h106424 : p4790)
    (h102509 : (¬ p5284) ∨ (¬ p3767) ∨ (¬ p4790) ∨ (¬ p3178) ∨ p3755 ∨ (¬ p4461))
    (h96487 : p4461 ∨ (¬ p2088))
    : (¬ p2088) ∨ p3755 ∨ (¬ p5284) ∨ (¬ p3767) ∨ (¬ p3178) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3178 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4790 := h106424;
    let u6 : (¬ p4461) := (Or.elim h102509 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => r4))))))))));
    (Or.elim h96487 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109811 (p2088 p2177 p2563 p3707 p3767 p3960 p4430 p4461 p4516 : Prop)
    (h84060 : p3707 ∨ (¬ p3767) ∨ (¬ p4430) ∨ (¬ p4516) ∨ (¬ p3960) ∨ (¬ p2177) ∨ p2563 ∨ (¬ p4461))
    (h96487 : p4461 ∨ (¬ p2088))
    : (¬ p2088) ∨ (¬ p4516) ∨ (¬ p3767) ∨ p2563 ∨ p3707 ∨ (¬ p2177) ∨ (¬ p3960) ∨ (¬ p4430) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4430 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4461) := (Or.elim h84060 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => r6))))))))))))));
    (Or.elim h96487 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109813 (p2088 p3005 p3136 p3171 p3266 p3680 p4374 p4387 p4461 : Prop)
    (h95314 : p3266 ∨ (¬ p3680) ∨ (¬ p4461) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p4374) ∨ p3136 ∨ (¬ p4387))
    (h96487 : p4461 ∨ (¬ p2088))
    : (¬ p2088) ∨ p3266 ∨ (¬ p3005) ∨ (¬ p3680) ∨ (¬ p3171) ∨ p3136 ∨ (¬ p4374) ∨ (¬ p4387) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4374 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4461) := (Or.elim h95314 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h96487 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109815 (p2088 p2441 p3156 p3276 p3696 p3767 p4461 p4635 p4705 : Prop)
    (h106238 : p4705)
    (h99488 : p3276 ∨ (¬ p3767) ∨ (¬ p3156) ∨ (¬ p4705) ∨ (¬ p2441) ∨ (¬ p3696) ∨ (¬ p4635) ∨ (¬ p4461))
    (h96487 : p4461 ∨ (¬ p2088))
    : (¬ p2088) ∨ (¬ p3767) ∨ (¬ p2441) ∨ p3276 ∨ (¬ p4635) ∨ (¬ p3156) ∨ (¬ p3696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4705 := h106238;
    let u8 : (¬ p4461) := (Or.elim h99488 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => r6))))))))))))));
    (Or.elim h96487 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109824 (p3425 p3434 p4232 p5228 : Prop)
    (h28001 : (¬ p3425) ∨ p4232 ∨ (¬ p5228))
    (h102624 : p5228 ∨ p3434)
    : p3434 ∨ p4232 ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4232) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5228) := (Or.elim h28001 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h102624 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109826 (p2396 p2761 p3434 p3670 p4473 p5228 : Prop)
    (h94242 : p3670 ∨ (¬ p4473) ∨ (¬ p5228) ∨ (¬ p2761) ∨ (¬ p2396))
    (h102624 : p5228 ∨ p3434)
    : p3434 ∨ (¬ p2761) ∨ (¬ p2396) ∨ p3670 ∨ (¬ p4473) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5228) := (Or.elim h94242 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102624 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109827 (p2707 p2737 p2761 p3434 p3670 p5228 : Prop)
    (h94253 : p3670 ∨ (¬ p2761) ∨ (¬ p5228) ∨ p2707 ∨ (¬ p2737))
    (h102624 : p5228 ∨ p3434)
    : p3434 ∨ (¬ p2761) ∨ p3670 ∨ (¬ p2737) ∨ p2707 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5228) := (Or.elim h94253 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102624 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109828 (p2608 p2707 p2761 p3434 p3670 p5228 : Prop)
    (h94255 : p3670 ∨ p2608 ∨ p2707 ∨ (¬ p5228) ∨ (¬ p2761))
    (h102624 : p5228 ∨ p3434)
    : p3434 ∨ (¬ p2761) ∨ p3670 ∨ p2707 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5228) := (Or.elim h94255 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102624 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109829 (p3425 p3434 p3670 p3767 p4439 p4736 p5228 : Prop)
    (h105431 : p4736)
    (h94238 : p3670 ∨ (¬ p5228) ∨ (¬ p4736) ∨ (¬ p3425) ∨ (¬ p3767) ∨ (¬ p4439))
    (h102624 : p5228 ∨ p3434)
    : p3434 ∨ (¬ p4439) ∨ p3670 ∨ (¬ p3767) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p4439 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4736 := h105431;
    let u6 : (¬ p5228) := (Or.elim h94238 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h102624 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109830 (p2761 p3276 p3366 p3367 p3425 p3434 p5159 p5228 : Prop)
    (h88620 : p3276 ∨ (¬ p2761) ∨ (¬ p3366) ∨ (¬ p5159) ∨ (¬ p3425) ∨ (¬ p3367) ∨ (¬ p5228))
    (h102624 : p5228 ∨ p3434)
    : p3434 ∨ p3276 ∨ (¬ p3367) ∨ (¬ p2761) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p5159) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5159 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5228) := (Or.elim h88620 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => r5))))))))))));
    (Or.elim h102624 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109834 (p2518 p2528 p3379 p3425 p3434 p3461 p3670 p4604 p4736 p5228 : Prop)
    (h105431 : p4736)
    (h106293 : p4604)
    (h96225 : p3670 ∨ (¬ p2518) ∨ (¬ p4604) ∨ (¬ p5228) ∨ (¬ p4736) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3461) ∨ (¬ p3425))
    (h102624 : p5228 ∨ p3434)
    : p3434 ∨ (¬ p3461) ∨ p3670 ∨ (¬ p2528) ∨ (¬ p3425) ∨ (¬ p2518) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : p4604 := h106293;
    let u9 : (¬ p5228) := (Or.elim h96225 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u4))))))))))))))))));
    (Or.elim h102624 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109840 (p2331 p3286 p3319 p3343 p3564 p4319 p5325 : Prop)
    (h109759 : p3343 ∨ (¬ p5325) ∨ (¬ p2331) ∨ (¬ p3319) ∨ (¬ p4319) ∨ p3286)
    (h96144 : p5325 ∨ (¬ p3564))
    : (¬ p3564) ∨ p3343 ∨ (¬ p2331) ∨ (¬ p3319) ∨ (¬ p4319) ∨ p3286 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5325) := (Or.elim h109759 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h96144 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109845 (p2187 p2383 p2781 p3125 p3276 p3286 p3564 p4236 p5284 p5325 : Prop)
    (h93253 : (¬ p5284) ∨ (¬ p3276) ∨ (¬ p2383) ∨ (¬ p2781) ∨ p2187 ∨ (¬ p4236) ∨ (¬ p5325) ∨ p3286 ∨ (¬ p3125))
    (h96144 : p5325 ∨ (¬ p3564))
    : (¬ p3564) ∨ (¬ p5284) ∨ (¬ p2383) ∨ (¬ p3125) ∨ p3286 ∨ (¬ p3276) ∨ (¬ p4236) ∨ (¬ p2781) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5325) := (Or.elim h93253 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (r7 u3))))))))))))))))));
    (Or.elim h96144 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109846 (p2274 p2307 p2598 p2696 p2779 p3125 p3564 p3985 p5160 p5325 : Prop)
    (h95704 : (¬ p2779) ∨ (¬ p5160) ∨ (¬ p2696) ∨ p2274 ∨ (¬ p3985) ∨ (¬ p2307) ∨ (¬ p5325) ∨ (¬ p3125) ∨ p2598)
    (h96144 : p5325 ∨ (¬ p3564))
    : (¬ p3564) ∨ (¬ p2696) ∨ p2274 ∨ p2598 ∨ (¬ p3125) ∨ (¬ p5160) ∨ (¬ p3985) ∨ (¬ p2779) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5325) := (Or.elim h95704 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (u3 r7))))))))))))))))));
    (Or.elim h96144 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109853 (p2470 p3083 p3212 p3343 p3366 p3370 p3371 p3461 p3564 p3680 p4729 p5325 : Prop)
    (h105429 : p4729)
    (h89545 : p3461 ∨ (¬ p5325) ∨ (¬ p3371) ∨ (¬ p3680) ∨ p3343 ∨ p2470 ∨ (¬ p3366) ∨ (¬ p3212) ∨ (¬ p3083) ∨ (¬ p4729) ∨ (¬ p3370))
    (h96144 : p5325 ∨ (¬ p3564))
    : (¬ p3564) ∨ p3461 ∨ (¬ p3083) ∨ (¬ p3680) ∨ p3343 ∨ (¬ p3366) ∨ (¬ p3212) ∨ (¬ p3370) ∨ (¬ p3371) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4729 := h105429;
    let u11 : (¬ p5325) := (Or.elim h89545 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u9 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u7))))))))))))))))))))));
    (Or.elim h96144 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109856 (p2144 p2252 p2437 p2655 p2750 p3212 p3343 p3366 p3389 p3461 p3564 p3680 p5325 : Prop)
    (h106345 : p2750)
    (h91869 : p3366 ∨ p3461 ∨ (¬ p3212) ∨ p3389 ∨ (¬ p2750) ∨ (¬ p2655) ∨ (¬ p2144) ∨ (¬ p2437) ∨ (¬ p5325) ∨ (¬ p3680) ∨ p3343 ∨ (¬ p2252))
    (h96144 : p5325 ∨ (¬ p3564))
    : (¬ p3564) ∨ p3343 ∨ (¬ p2437) ∨ p3461 ∨ (¬ p3680) ∨ (¬ p3212) ∨ (¬ p2655) ∨ (¬ p2144) ∨ (¬ p2252) ∨ p3366 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3366) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2750 := h106345;
    let u12 : (¬ p5325) := (Or.elim h91869 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u10 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u1 q10))) (fun r10 => (False.elim (r10 u8))))))))))))))))))))))));
    (Or.elim h96144 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109859 (p3399 p3631 p3830 p5357 : Prop)
    (h36229 : p3399 ∨ (¬ p3830) ∨ (¬ p5357))
    (h102129 : p5357 ∨ p3631)
    : p3631 ∨ (¬ p3830) ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5357) := (Or.elim h36229 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h102129 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109860 (p2396 p2761 p3631 p3707 p5357 : Prop)
    (h107140 : (¬ p2761) ∨ p3707 ∨ (¬ p2396) ∨ (¬ p5357))
    (h102129 : p5357 ∨ p3631)
    : p3631 ∨ p3707 ∨ (¬ p2396) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5357) := (Or.elim h107140 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h102129 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109861 (p3246 p3571 p3631 p5357 p5358 : Prop)
    (h16922 : (¬ p3246) ∨ (¬ p3571) ∨ (¬ p5357) ∨ (¬ p5358))
    (h102129 : p5357 ∨ p3631)
    : p3631 ∨ (¬ p3246) ∨ (¬ p3571) ∨ (¬ p5358) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5357) := (Or.elim h16922 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h102129 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109864 (p2761 p3527 p3631 p3707 p4666 p5357 : Prop)
    (h105658 : p4666)
    (h90001 : p3707 ∨ (¬ p5357) ∨ (¬ p3527) ∨ (¬ p2761) ∨ (¬ p4666))
    (h102129 : p5357 ∨ p3631)
    : p3631 ∨ (¬ p2761) ∨ p3707 ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4666 := h105658;
    let u5 : (¬ p5357) := (Or.elim h90001 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102129 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109866 (p2396 p2761 p3571 p3631 p3707 p4556 p5357 : Prop)
    (h105399 : p4556)
    (h90002 : p3707 ∨ (¬ p2761) ∨ (¬ p5357) ∨ (¬ p2396) ∨ (¬ p4556) ∨ (¬ p3571))
    (h102129 : p5357 ∨ p3631)
    : p3631 ∨ (¬ p2396) ∨ (¬ p2761) ∨ p3707 ∨ (¬ p3571) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4556 := h105399;
    let u6 : (¬ p5357) := (Or.elim h90002 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h102129 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109869 (p2427 p3105 p3571 p3631 p3670 p3707 p5357 : Prop)
    (h109169 : (¬ p3105) ∨ (¬ p3670) ∨ (¬ p3571) ∨ p3707 ∨ p2427 ∨ (¬ p5357))
    (h102129 : p5357 ∨ p3631)
    : p3631 ∨ (¬ p3105) ∨ (¬ p3670) ∨ (¬ p3571) ∨ p3707 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5357) := (Or.elim h109169 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => r4))))))))));
    (Or.elim h102129 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109884 (p2373 p3979 p4199 p4433 p5433 p5567 : Prop)
    (h106150 : p4433)
    (h49026 : (¬ p2373) ∨ (¬ p3979) ∨ (¬ p4199) ∨ (¬ p4433) ∨ (¬ p5433))
    (h9790 : p4199 ∨ (¬ p5567))
    : (¬ p5567) ∨ (¬ p5433) ∨ (¬ p3979) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4433 := h106150;
    let u5 : (¬ p4199) := (Or.elim h49026 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h9790 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109903 (p2088 p2819 p3146 p3483 p4433 p4460 p5379 : Prop)
    (h106150 : p4433)
    (h90210 : (¬ p3483) ∨ p3146 ∨ p2819 ∨ (¬ p4460) ∨ (¬ p5379) ∨ (¬ p4433))
    (h96490 : p4460 ∨ (¬ p2088))
    : (¬ p2088) ∨ (¬ p3483) ∨ p2819 ∨ (¬ p5379) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4433 := h106150;
    let u6 : (¬ p4460) := (Or.elim h90210 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96490 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109915 (p2088 p2459 p3005 p3291 p3755 p4437 p4438 p4460 : Prop)
    (h94982 : (¬ p3755) ∨ (¬ p3291) ∨ (¬ p4460) ∨ p3005 ∨ (¬ p4438) ∨ p2459 ∨ (¬ p4437))
    (h96490 : p4460 ∨ (¬ p2088))
    : (¬ p2088) ∨ (¬ p3755) ∨ (¬ p4437) ∨ p2459 ∨ (¬ p3291) ∨ (¬ p4438) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3291 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4460) := (Or.elim h94982 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (False.elim (r5 u2))))))))))))));
    (Or.elim h96490 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109916 (p2717 p4746 p4800 p4902 : Prop)
    (h105456 : p4902)
    (h38909 : p4746 ∨ (¬ p4800) ∨ (¬ p4902))
    (h97920 : p4800 ∨ p2717)
    : p2717 ∨ p4746 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4746) := (fun h => hn (Or.inr h));
    let u2 : p4902 := h105456;
    let u3 : (¬ p4800) := (Or.elim h38909 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h97920 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109917 (p2717 p3542 p4353 p4800 : Prop)
    (h36143 : p3542 ∨ (¬ p4353) ∨ (¬ p4800))
    (h97920 : p4800 ∨ p2717)
    : p2717 ∨ p3542 ∨ (¬ p4353) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3542) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4353 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4800) := (Or.elim h36143 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h97920 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109919 (p2341 p2707 p2717 p3537 p4800 p5261 : Prop)
    (h89835 : p3537 ∨ (¬ p2707) ∨ (¬ p2341) ∨ (¬ p4800) ∨ (¬ p5261))
    (h97920 : p4800 ∨ p2717)
    : p2717 ∨ (¬ p5261) ∨ (¬ p2341) ∨ p3537 ∨ (¬ p2707) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p5261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4800) := (Or.elim h89835 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h97920 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109920 (p2098 p2717 p2911 p3425 p4800 p5083 : Prop)
    (h89838 : p2098 ∨ (¬ p2911) ∨ (¬ p4800) ∨ p3425 ∨ (¬ p5083))
    (h97920 : p4800 ∨ p2717)
    : p2717 ∨ p2098 ∨ (¬ p5083) ∨ (¬ p2911) ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4800) := (Or.elim h89838 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h97920 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109923 (p2707 p2717 p3434 p3537 p4668 p4800 : Prop)
    (h105414 : p4668)
    (h101880 : p3537 ∨ (¬ p3434) ∨ (¬ p4800) ∨ (¬ p4668) ∨ (¬ p2707))
    (h97920 : p4800 ∨ p2717)
    : p2717 ∨ (¬ p3434) ∨ (¬ p2707) ∨ p3537 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4668 := h105414;
    let u5 : (¬ p4800) := (Or.elim h101880 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h97920 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109935 (p3343 p3422 p4343 p4422 p5170 : Prop)
    (h109752 : p3343 ∨ (¬ p4422) ∨ (¬ p4343) ∨ (¬ p5170) ∨ (¬ p3422))
    (h96283 : p5170 ∨ p3343)
    : p3343 ∨ (¬ p4422) ∨ (¬ p4343) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5170) := (Or.elim h109752 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96283 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109936 (p2727 p3343 p3842 p5170 : Prop)
    (h94385 : (¬ p3842) ∨ (¬ p5170) ∨ p2727)
    (h96283 : p5170 ∨ p3343)
    : p3343 ∨ (¬ p3842) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5170) := (Or.elim h94385 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96283 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109937 (p2630 p3343 p3755 p5170 : Prop)
    (h94959 : (¬ p3755) ∨ (¬ p5170) ∨ p2630)
    (h96283 : p5170 ∨ p3343)
    : p3343 ∨ (¬ p3755) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5170) := (Or.elim h94959 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96283 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109938 (p2651 p3286 p3343 p5170 : Prop)
    (h95998 : (¬ p3286) ∨ (¬ p5170) ∨ p2651)
    (h96283 : p5170 ∨ p3343)
    : p3343 ∨ (¬ p3286) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5170) := (Or.elim h95998 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96283 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109939 (p2331 p2651 p3343 p4421 p5170 : Prop)
    (h96001 : (¬ p4421) ∨ (¬ p2331) ∨ p2651 ∨ (¬ p5170))
    (h96283 : p5170 ∨ p3343)
    : p3343 ∨ (¬ p4421) ∨ (¬ p2331) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5170) := (Or.elim h96001 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => r2))))));
    (Or.elim h96283 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109940 (p2440 p3276 p3343 p4949 p5170 p5284 : Prop)
    (h105463 : p4949)
    (h74547 : (¬ p5284) ∨ (¬ p3276) ∨ p2440 ∨ (¬ p5170) ∨ (¬ p4949))
    (h96283 : p5170 ∨ p3343)
    : p3343 ∨ (¬ p5284) ∨ (¬ p3276) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4949 := h105463;
    let u5 : (¬ p5170) := (Or.elim h74547 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96283 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109944 (p2630 p3343 p3707 p3830 p5170 p5284 : Prop)
    (h100408 : (¬ p3707) ∨ (¬ p5284) ∨ p2630 ∨ (¬ p3830) ∨ (¬ p5170))
    (h96283 : p5170 ∨ p3343)
    : p3343 ∨ (¬ p3707) ∨ (¬ p3830) ∨ p2630 ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5170) := (Or.elim h100408 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h96283 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109950 (p2156 p2274 p2396 p2651 p3276 p3343 p4236 p4641 p5170 p5284 : Prop)
    (h107637 : (¬ p5284) ∨ (¬ p3276) ∨ p2651 ∨ (¬ p2274) ∨ (¬ p5170) ∨ (¬ p2156) ∨ (¬ p4236) ∨ (¬ p2396) ∨ (¬ p4641))
    (h96283 : p5170 ∨ p3343)
    : p3343 ∨ (¬ p5284) ∨ (¬ p2156) ∨ p2651 ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3276) ∨ (¬ p4236) ∨ (¬ p4641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5170) := (Or.elim h107637 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h96283 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109954 (p2406 p2982 p3193 p3237 : Prop)
    (h81665 : p3193 ∨ (¬ p3237) ∨ p2406)
    (h96343 : p3237 ∨ p2982)
    : p2982 ∨ p3193 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3237) := (Or.elim h81665 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96343 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109955 (p2230 p2982 p3237 p3355 : Prop)
    (h85036 : (¬ p3355) ∨ (¬ p3237) ∨ p2230)
    (h96343 : p3237 ∨ p2982)
    : p2982 ∨ (¬ p3355) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3237) := (Or.elim h85036 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96343 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109956 (p2440 p2982 p3237 p3343 : Prop)
    (h91402 : (¬ p3343) ∨ (¬ p3237) ∨ (¬ p2440))
    (h96343 : p3237 ∨ p2982)
    : p2982 ∨ (¬ p3343) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3237) := (Or.elim h91402 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96343 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109959 (p2563 p2982 p3237 p3276 p3680 p5043 : Prop)
    (h105471 : p5043)
    (h91407 : (¬ p3237) ∨ p3276 ∨ (¬ p5043) ∨ (¬ p3680) ∨ (¬ p2563))
    (h96343 : p3237 ∨ p2982)
    : p2982 ∨ (¬ p3680) ∨ p3276 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5043 := h105471;
    let u5 : (¬ p3237) := (Or.elim h91407 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96343 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109961 (p2427 p2972 p2982 p3237 p3276 p3680 : Prop)
    (h97724 : p3276 ∨ (¬ p3680) ∨ (¬ p2972) ∨ (¬ p3237) ∨ (¬ p2427))
    (h96343 : p3237 ∨ p2982)
    : p2982 ∨ p3276 ∨ (¬ p3680) ∨ (¬ p2972) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3237) := (Or.elim h97724 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96343 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109962 (p2982 p3105 p3237 p3276 p3680 p4885 : Prop)
    (h102072 : p3276 ∨ (¬ p3680) ∨ (¬ p3237) ∨ (¬ p3105) ∨ (¬ p4885))
    (h96343 : p3237 ∨ p2982)
    : p2982 ∨ p3276 ∨ (¬ p3680) ∨ (¬ p3105) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3237) := (Or.elim h102072 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96343 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109965 (p2230 p2598 p2982 p3237 p3333 p3589 p5193 : Prop)
    (h105488 : p5193)
    (h81783 : (¬ p3333) ∨ (¬ p3237) ∨ (¬ p5193) ∨ (¬ p2598) ∨ (¬ p3589) ∨ p2230)
    (h96343 : p3237 ∨ p2982)
    : p2982 ∨ (¬ p2598) ∨ (¬ p3333) ∨ (¬ p3589) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5193 := h105488;
    let u6 : (¬ p3237) := (Or.elim h81783 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h96343 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109967 (p2427 p2982 p3237 p3276 p3680 p4334 p4558 : Prop)
    (h105400 : p4558)
    (h91403 : p3276 ∨ (¬ p3680) ∨ (¬ p3237) ∨ (¬ p4334) ∨ (¬ p2427) ∨ (¬ p4558))
    (h96343 : p3237 ∨ p2982)
    : p2982 ∨ (¬ p4334) ∨ (¬ p3680) ∨ p3276 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p4334 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4558 := h105400;
    let u6 : (¬ p3237) := (Or.elim h91403 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96343 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109969 (p2901 p2982 p3237 p3276 p3680 p4192 p4705 : Prop)
    (h106238 : p4705)
    (h91405 : p3276 ∨ (¬ p3680) ∨ (¬ p3237) ∨ (¬ p4192) ∨ (¬ p2901) ∨ (¬ p4705))
    (h96343 : p3237 ∨ p2982)
    : p2982 ∨ (¬ p4192) ∨ (¬ p3680) ∨ p3276 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    let u6 : (¬ p3237) := (Or.elim h91405 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96343 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109970 (p2563 p2630 p2651 p2982 p3237 p3286 p5175 : Prop)
    (h91409 : (¬ p3237) ∨ (¬ p3286) ∨ (¬ p5175) ∨ (¬ p2630) ∨ (¬ p2563) ∨ p2651)
    (h96343 : p3237 ∨ p2982)
    : p2982 ∨ (¬ p3286) ∨ (¬ p2630) ∨ p2651 ∨ (¬ p2563) ∨ (¬ p5175) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3237) := (Or.elim h91409 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h96343 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109975 (p3286 p3291 p3506 p3767 : Prop)
    (h33366 : (¬ p3291) ∨ p3506 ∨ (¬ p3767))
    (h102534 : p3291 ∨ p3286)
    : p3286 ∨ (¬ p3767) ∨ p3506 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3506) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3291) := (Or.elim h33366 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h102534 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109977 (p2797 p3125 p3286 p3291 p3755 p4038 : Prop)
    (h94954 : (¬ p3755) ∨ p2797 ∨ (¬ p3291) ∨ p3125 ∨ (¬ p4038))
    (h102534 : p3291 ∨ p3286)
    : p3286 ∨ (¬ p4038) ∨ p3125 ∨ (¬ p3755) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p4038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3291) := (Or.elim h94954 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102534 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109990 (p2088 p2459 p3005 p3286 p3291 p3755 p4437 p4438 : Prop)
    (h109915 : (¬ p2088) ∨ (¬ p3755) ∨ (¬ p4437) ∨ p2459 ∨ (¬ p3291) ∨ (¬ p4438) ∨ p3005)
    (h102534 : p3291 ∨ p3286)
    : p3286 ∨ (¬ p2088) ∨ (¬ p3755) ∨ (¬ p4437) ∨ p2459 ∨ (¬ p4438) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3291) := (Or.elim h109915 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (u6 r5))))))))))))));
    (Or.elim h102534 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109994 (p2230 p2982 p3346 p4449 : Prop)
    (h26193 : (¬ p2230) ∨ (¬ p3346) ∨ (¬ p4449))
    (h95997 : p4449 ∨ (¬ p2982))
    : (¬ p2982) ∨ (¬ p3346) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4449) := (Or.elim h26193 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h95997 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109996 (p2440 p2982 p3343 p4449 : Prop)
    (h89550 : p3343 ∨ (¬ p4449) ∨ p2440)
    (h95997 : p4449 ∨ (¬ p2982))
    : (¬ p2982) ∨ p3343 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4449) := (Or.elim h89550 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h95997 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110001 (p2982 p3276 p4032 p4322 p4449 p4533 : Prop)
    (h105394 : p4533)
    (h41614 : (¬ p3276) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4449) ∨ (¬ p4533))
    (h95997 : p4449 ∨ (¬ p2982))
    : (¬ p2982) ∨ (¬ p4322) ∨ (¬ p3276) ∨ (¬ p4032) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4533 := h105394;
    let u5 : (¬ p4449) := (Or.elim h41614 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h95997 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110002 (p2563 p2982 p3276 p4322 p4449 p5046 : Prop)
    (h105472 : p5046)
    (h100283 : (¬ p4322) ∨ (¬ p3276) ∨ p2563 ∨ (¬ p5046) ∨ (¬ p4449))
    (h95997 : p4449 ∨ (¬ p2982))
    : (¬ p2982) ∨ (¬ p4322) ∨ (¬ p3276) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5046 := h105472;
    let u5 : (¬ p4449) := (Or.elim h100283 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h95997 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110003 (p2982 p3115 p3276 p3707 p4387 p4449 p4702 : Prop)
    (h106079 : p4702)
    (h93067 : p3707 ∨ (¬ p3276) ∨ p3115 ∨ (¬ p4387) ∨ (¬ p4702) ∨ (¬ p4449))
    (h95997 : p4449 ∨ (¬ p2982))
    : (¬ p2982) ∨ p3707 ∨ (¬ p3276) ∨ p3115 ∨ (¬ p4387) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4702 := h106079;
    let u6 : (¬ p4449) := (Or.elim h93067 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h95997 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110014 (p2166 p2220 p2241 p2992 p4172 p4959 : Prop)
    (h76094 : p2241 ∨ (¬ p4959) ∨ p2166 ∨ (¬ p2220) ∨ (¬ p4172))
    (h96338 : p4959 ∨ (¬ p2992))
    : (¬ p2992) ∨ p2166 ∨ (¬ p2220) ∨ (¬ p4172) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4959) := (Or.elim h76094 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96338 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110015 (p2156 p2192 p2241 p2992 p4172 p4959 : Prop)
    (h79983 : (¬ p2156) ∨ (¬ p4959) ∨ p2241 ∨ p2192 ∨ (¬ p4172))
    (h96338 : p4959 ∨ (¬ p2992))
    : (¬ p2992) ∨ p2192 ∨ (¬ p2156) ∨ (¬ p4172) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4959) := (Or.elim h79983 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96338 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110016 (p2210 p2245 p2651 p2727 p2992 p4959 : Prop)
    (h82203 : (¬ p2727) ∨ (¬ p2245) ∨ (¬ p4959) ∨ (¬ p2210) ∨ p2651)
    (h96338 : p4959 ∨ (¬ p2992))
    : (¬ p2992) ∨ (¬ p2210) ∨ p2651 ∨ (¬ p2727) ∨ (¬ p2245) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4959) := (Or.elim h82203 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96338 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110017 (p2210 p2922 p2992 p3389 p4108 p4281 p4959 : Prop)
    (h88711 : (¬ p2922) ∨ (¬ p4959) ∨ p3389 ∨ (¬ p4108) ∨ (¬ p2210) ∨ (¬ p4281))
    (h96338 : p4959 ∨ (¬ p2992))
    : (¬ p2992) ∨ (¬ p4281) ∨ (¬ p2922) ∨ (¬ p4108) ∨ (¬ p2210) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4959) := (Or.elim h88711 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h96338 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110018 (p2210 p2992 p3038 p3516 p3631 p4959 p5206 : Prop)
    (h91532 : (¬ p3631) ∨ (¬ p5206) ∨ p3516 ∨ (¬ p3038) ∨ (¬ p4959) ∨ (¬ p2210))
    (h96338 : p4959 ∨ (¬ p2992))
    : (¬ p2992) ∨ (¬ p5206) ∨ p3516 ∨ (¬ p3631) ∨ (¬ p3038) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4959) := (Or.elim h91532 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96338 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110020 (p2210 p2246 p2651 p2992 p3016 p3073 p3449 p3564 p4330 p4959 : Prop)
    (h106329 : p4330)
    (h80578 : p3073 ∨ p3449 ∨ (¬ p4330) ∨ (¬ p3564) ∨ (¬ p3016) ∨ (¬ p2210) ∨ (¬ p4959) ∨ (¬ p2246) ∨ (¬ p2651))
    (h96338 : p4959 ∨ (¬ p2992))
    : (¬ p2992) ∨ (¬ p3564) ∨ p3449 ∨ (¬ p3016) ∨ (¬ p2210) ∨ (¬ p2651) ∨ (¬ p2246) ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4330 := h106329;
    let u9 : (¬ p4959) := (Or.elim h80578 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u5))))))))))))))))));
    (Or.elim h96338 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110021 (p2156 p2187 p2241 p2992 p3506 p3645 p3830 p3853 p4959 p5580 : Prop)
    (h107624 : (¬ p3506) ∨ (¬ p5580) ∨ (¬ p3645) ∨ (¬ p3853) ∨ p2241 ∨ (¬ p3830) ∨ p2187 ∨ p2156 ∨ (¬ p4959))
    (h96338 : p4959 ∨ (¬ p2992))
    : (¬ p2992) ∨ (¬ p5580) ∨ (¬ p3853) ∨ p2187 ∨ (¬ p3830) ∨ (¬ p3506) ∨ (¬ p3645) ∨ p2156 ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4959) := (Or.elim h107624 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => r7))))))))))))))));
    (Or.elim h96338 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110023 (p2156 p2187 p2241 p2363 p2992 p3449 p3645 p4181 p4959 p5122 : Prop)
    (h105483 : p5122)
    (h102305 : (¬ p4181) ∨ p2363 ∨ p2156 ∨ (¬ p3645) ∨ (¬ p3449) ∨ (¬ p5122) ∨ (¬ p4959) ∨ p2241 ∨ p2187)
    (h96338 : p4959 ∨ (¬ p2992))
    : (¬ p2992) ∨ p2363 ∨ p2156 ∨ p2187 ∨ (¬ p3449) ∨ (¬ p3645) ∨ (¬ p4181) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5122 := h105483;
    let u9 : (¬ p4959) := (Or.elim h102305 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (False.elim (u3 r7))))))))))))))))));
    (Or.elim h96338 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110025 (p2156 p2246 p2264 p2807 p2992 p3125 p3461 p3645 p3941 p4959 p5119 : Prop)
    (h85568 : p3461 ∨ (¬ p2246) ∨ (¬ p4959) ∨ (¬ p3941) ∨ (¬ p3645) ∨ p3125 ∨ (¬ p5119) ∨ p2156 ∨ (¬ p2807) ∨ (¬ p2264))
    (h96338 : p4959 ∨ (¬ p2992))
    : (¬ p2992) ∨ p3461 ∨ p3125 ∨ (¬ p5119) ∨ (¬ p2264) ∨ p2156 ∨ (¬ p3941) ∨ (¬ p2246) ∨ (¬ p3645) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4959) := (Or.elim h85568 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u4))))))))))))))))))));
    (Or.elim h96338 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110028 (p2187 p2210 p2246 p2264 p2363 p2651 p2911 p2992 p3093 p3580 p3957 p4959 : Prop)
    (h91568 : p2911 ∨ (¬ p2264) ∨ p2363 ∨ (¬ p4959) ∨ p2187 ∨ (¬ p2210) ∨ (¬ p3580) ∨ p3093 ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p3957))
    (h96338 : p4959 ∨ (¬ p2992))
    : (¬ p2992) ∨ p2363 ∨ p2911 ∨ (¬ p2210) ∨ p2187 ∨ p3093 ∨ (¬ p2264) ∨ (¬ p2246) ∨ (¬ p3957) ∨ (¬ p3580) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p4959) := (Or.elim h91568 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (r9 u8))))))))))))))))))))));
    (Or.elim h96338 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110037 (p2187 p2241 p2383 p2727 p3125 p3343 p3564 p4198 p5322 : Prop)
    (h82239 : (¬ p3343) ∨ (¬ p2187) ∨ (¬ p5322) ∨ (¬ p2241) ∨ p2383 ∨ (¬ p4198) ∨ p3125 ∨ (¬ p2727))
    (h102595 : p5322 ∨ p3564)
    : p3564 ∨ p3125 ∨ (¬ p2727) ∨ (¬ p2187) ∨ p2383 ∨ (¬ p2241) ∨ (¬ p3343) ∨ (¬ p4198) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5322) := (Or.elim h82239 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u2))))))))))))))));
    (Or.elim h102595 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110039 (p2241 p2274 p2307 p2727 p3125 p3343 p3564 p5021 p5322 : Prop)
    (h98357 : (¬ p3343) ∨ p2307 ∨ (¬ p2241) ∨ (¬ p2274) ∨ p3125 ∨ (¬ p5021) ∨ (¬ p2727) ∨ (¬ p5322))
    (h102595 : p5322 ∨ p3564)
    : p3564 ∨ (¬ p2241) ∨ (¬ p2727) ∨ p2307 ∨ p3125 ∨ (¬ p3343) ∨ (¬ p5021) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5322) := (Or.elim h98357 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => r6))))))))))))));
    (Or.elim h102595 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110041 (p2383 p2668 p2787 p3201 p3323 p3333 p3362 p3389 p3564 p5322 : Prop)
    (h105374 : p2787)
    (h74780 : p3323 ∨ (¬ p3333) ∨ (¬ p2787) ∨ (¬ p3362) ∨ p3201 ∨ (¬ p2668) ∨ (¬ p5322) ∨ (¬ p3389) ∨ p2383)
    (h102595 : p5322 ∨ p3564)
    : p3564 ∨ (¬ p2668) ∨ p2383 ∨ p3323 ∨ p3201 ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2787 := h105374;
    let u9 : (¬ p5322) := (Or.elim h74780 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u2 r7))))))))))))))))));
    (Or.elim h102595 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110046 (p2187 p2437 p2753 p3125 p3343 p3362 p3389 p3564 p3923 p4870 p5322 : Prop)
    (h81559 : (¬ p3343) ∨ (¬ p3389) ∨ (¬ p5322) ∨ (¬ p2753) ∨ p2437 ∨ (¬ p3362) ∨ (¬ p4870) ∨ (¬ p2187) ∨ p3125 ∨ (¬ p3923))
    (h102595 : p5322 ∨ p3564)
    : p3564 ∨ p3125 ∨ (¬ p2753) ∨ (¬ p3389) ∨ (¬ p3923) ∨ p2437 ∨ (¬ p4870) ∨ (¬ p3362) ∨ (¬ p3343) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p5322) := (Or.elim h81559 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (False.elim (r8 u4))))))))))))))))))));
    (Or.elim h102595 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110047 (p2274 p2307 p2787 p3125 p3276 p3286 p3564 p3670 p4117 p5322 p5454 : Prop)
    (h105374 : p2787)
    (h95932 : p3276 ∨ (¬ p3670) ∨ p3125 ∨ (¬ p4117) ∨ (¬ p2787) ∨ (¬ p5454) ∨ (¬ p2274) ∨ p2307 ∨ (¬ p3286) ∨ (¬ p5322))
    (h102595 : p5322 ∨ p3564)
    : p3564 ∨ p3276 ∨ (¬ p5454) ∨ (¬ p2274) ∨ p3125 ∨ (¬ p3286) ∨ (¬ p4117) ∨ (¬ p3670) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5454 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2787 := h105374;
    let u10 : (¬ p5322) := (Or.elim h95932 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => r8))))))))))))))))));
    (Or.elim h102595 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110049 (p2470 p3083 p3343 p3461 p3519 p3564 p3645 p4032 p4322 p4376 p4874 p5322 : Prop)
    (h106320 : p4376)
    (h76731 : (¬ p4322) ∨ (¬ p3343) ∨ (¬ p3645) ∨ p3083 ∨ (¬ p4032) ∨ (¬ p3461) ∨ (¬ p4874) ∨ (¬ p5322) ∨ (¬ p4376) ∨ (¬ p2470) ∨ (¬ p3519))
    (h102595 : p5322 ∨ p3564)
    : p3564 ∨ (¬ p3461) ∨ p3083 ∨ (¬ p4322) ∨ (¬ p3343) ∨ (¬ p4032) ∨ (¬ p3519) ∨ (¬ p2470) ∨ (¬ p4874) ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4376 := h106320;
    let u11 : (¬ p5322) := (Or.elim h76731 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (r9 u6))))))))))))))))))))));
    (Or.elim h102595 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110050 (p2241 p2750 p2753 p3093 p3201 p3323 p3333 p3362 p3389 p3564 p4319 p5322 : Prop)
    (h106345 : p2750)
    (h95626 : p3093 ∨ (¬ p2241) ∨ (¬ p3362) ∨ (¬ p2753) ∨ (¬ p4319) ∨ (¬ p2750) ∨ p3323 ∨ (¬ p3389) ∨ (¬ p3333) ∨ (¬ p5322) ∨ p3201)
    (h102595 : p5322 ∨ p3564)
    : p3564 ∨ p3323 ∨ (¬ p2753) ∨ p3093 ∨ (¬ p3389) ∨ p3201 ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p2241) ∨ (¬ p4319) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2750 := h106345;
    let u11 : (¬ p5322) := (Or.elim h95626 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => q9) (fun r9 => (False.elim (u5 r9))))))))))))))))))))));
    (Or.elim h102595 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110053 (p2136 p2383 p2437 p2663 p2819 p3125 p3343 p3389 p3564 p4198 p4428 p4786 p5322 : Prop)
    (h106425 : p4786)
    (h86282 : p2437 ∨ (¬ p3389) ∨ (¬ p2819) ∨ (¬ p4786) ∨ (¬ p3343) ∨ (¬ p2136) ∨ p3125 ∨ (¬ p5322) ∨ (¬ p4198) ∨ (¬ p4428) ∨ (¬ p2663) ∨ p2383)
    (h102595 : p5322 ∨ p3564)
    : p3564 ∨ p3125 ∨ (¬ p2819) ∨ p2383 ∨ p2437 ∨ (¬ p3389) ∨ (¬ p3343) ∨ (¬ p2663) ∨ (¬ p4198) ∨ (¬ p2136) ∨ (¬ p4428) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4786 := h106425;
    let u12 : (¬ p5322) := (Or.elim h86282 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (False.elim (u3 r10))))))))))))))))))))))));
    (Or.elim h102595 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110056 (p3073 p3537 p3609 p5343 : Prop)
    (h109688 : (¬ p3537) ∨ (¬ p3609) ∨ (¬ p5343) ∨ p3073)
    (h96254 : p5343 ∨ (¬ p3609))
    : (¬ p3537) ∨ (¬ p3609) ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5343) := (Or.elim h109688 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h96254 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step110058 (p2761 p3631 p3707 p5362 : Prop)
    (h93342 : p3707 ∨ (¬ p5362) ∨ (¬ p2761))
    (h96250 : p5362 ∨ (¬ p3631))
    : (¬ p3631) ∨ (¬ p2761) ∨ p3707 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5362) := (Or.elim h93342 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h96250 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110061 (p2449 p3032 p3631 p5362 p5363 : Prop)
    (h97767 : (¬ p5363) ∨ (¬ p5362) ∨ p2449 ∨ (¬ p3032))
    (h96250 : p5362 ∨ (¬ p3631))
    : (¬ p3631) ∨ (¬ p5363) ∨ p2449 ∨ (¬ p3032) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5362) := (Or.elim h97767 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h96250 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110062 (p3246 p3399 p3631 p3830 p4914 p5362 : Prop)
    (h93335 : (¬ p5362) ∨ p3399 ∨ (¬ p4914) ∨ p3246 ∨ (¬ p3830))
    (h96250 : p5362 ∨ (¬ p3631))
    : (¬ p3631) ∨ (¬ p3830) ∨ p3399 ∨ (¬ p4914) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5362) := (Or.elim h93335 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96250 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110064 (p2707 p3399 p3434 p3631 p3830 p5362 : Prop)
    (h108321 : (¬ p2707) ∨ (¬ p3830) ∨ p3434 ∨ p3399 ∨ (¬ p5362))
    (h96250 : p5362 ∨ (¬ p3631))
    : (¬ p3631) ∨ (¬ p2707) ∨ (¬ p3830) ∨ p3434 ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5362) := (Or.elim h108321 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h96250 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110065 (p2396 p3309 p3399 p3631 p3830 p5362 : Prop)
    (h108655 : (¬ p3309) ∨ (¬ p3830) ∨ (¬ p5362) ∨ p3399 ∨ p2396)
    (h96250 : p5362 ∨ (¬ p3631))
    : (¬ p3631) ∨ (¬ p3309) ∨ (¬ p3830) ∨ p3399 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5362) := (Or.elim h108655 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96250 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110066 (p2417 p2922 p3399 p3631 p3830 p5362 : Prop)
    (h108925 : (¬ p2922) ∨ (¬ p5362) ∨ p2417 ∨ p3399 ∨ (¬ p3830))
    (h96250 : p5362 ∨ (¬ p3631))
    : (¬ p3631) ∨ (¬ p2922) ∨ p2417 ∨ p3399 ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5362) := (Or.elim h108925 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96250 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110069 (p2396 p3032 p3399 p3631 p3830 p4361 p5362 : Prop)
    (h105382 : p4361)
    (h93337 : (¬ p5362) ∨ p3399 ∨ (¬ p3032) ∨ (¬ p3830) ∨ p2396 ∨ (¬ p4361))
    (h96250 : p5362 ∨ (¬ p3631))
    : (¬ p3631) ∨ (¬ p3032) ∨ (¬ p3830) ∨ p3399 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4361 := h105382;
    let u6 : (¬ p5362) := (Or.elim h93337 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96250 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110070 (p2396 p3227 p3355 p3389 p3631 p4712 p5362 : Prop)
    (h105422 : p4712)
    (h93340 : (¬ p5362) ∨ (¬ p3355) ∨ (¬ p3227) ∨ p2396 ∨ p3389 ∨ (¬ p4712))
    (h96250 : p5362 ∨ (¬ p3631))
    : (¬ p3631) ∨ (¬ p3227) ∨ (¬ p3355) ∨ p2396 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3227 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4712 := h105422;
    let u6 : (¬ p5362) := (Or.elim h93340 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96250 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110073 (p2396 p3425 p3599 p3619 p3631 p4477 p5362 : Prop)
    (h108936 : p3599 ∨ (¬ p5362) ∨ (¬ p3619) ∨ p2396 ∨ (¬ p3425) ∨ (¬ p4477))
    (h96250 : p5362 ∨ (¬ p3631))
    : (¬ p3631) ∨ p3599 ∨ (¬ p3619) ∨ p2396 ∨ (¬ p3425) ∨ (¬ p4477) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5362) := (Or.elim h108936 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96250 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110078 (p2363 p2819 p3609 p4857 : Prop)
    (h74992 : (¬ p3609) ∨ p2363 ∨ (¬ p4857))
    (h93122 : p4857 ∨ p2819)
    : p2819 ∨ p2363 ∨ (¬ p3609) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4857) := (Or.elim h74992 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h93122 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110079 (p2122 p2819 p2829 p3537 p4857 : Prop)
    (h102038 : p3537 ∨ (¬ p2122) ∨ (¬ p2829) ∨ (¬ p4857))
    (h93122 : p4857 ∨ p2819)
    : p2819 ∨ p3537 ∨ (¬ p2829) ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4857) := (Or.elim h102038 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h93122 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110081 (p2098 p2668 p2774 p2819 p4843 p4857 : Prop)
    (h105449 : p4843)
    (h101509 : (¬ p2668) ∨ (¬ p4843) ∨ (¬ p4857) ∨ p2098 ∨ (¬ p2774))
    (h93122 : p4857 ∨ p2819)
    : p2819 ∨ p2098 ∨ (¬ p2668) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4843 := h105449;
    let u5 : (¬ p4857) := (Or.elim h101509 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h93122 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110083 (p2363 p2774 p2819 p2829 p3537 p4857 : Prop)
    (h102036 : p3537 ∨ p2363 ∨ p2774 ∨ (¬ p4857) ∨ (¬ p2829))
    (h93122 : p4857 ∨ p2819)
    : p2819 ∨ p2363 ∨ p3537 ∨ (¬ p2829) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4857) := (Or.elim h102036 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h93122 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110084 (p2668 p2819 p2829 p3537 p4843 p4857 : Prop)
    (h105449 : p4843)
    (h102041 : (¬ p2668) ∨ (¬ p4843) ∨ (¬ p4857) ∨ p3537 ∨ (¬ p2829))
    (h93122 : p4857 ∨ p2819)
    : p2819 ∨ (¬ p2668) ∨ p3537 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4843 := h105449;
    let u5 : (¬ p4857) := (Or.elim h102041 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h93122 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110093 (p2248 p2774 p2819 p2829 p2881 p2901 p2946 p3537 p3873 p4503 p4857 : Prop)
    (h105365 : p2248)
    (h106530 : p4503)
    (h102047 : (¬ p2901) ∨ (¬ p2881) ∨ (¬ p4857) ∨ p2774 ∨ (¬ p2248) ∨ (¬ p2829) ∨ p3537 ∨ (¬ p2946) ∨ (¬ p3873) ∨ (¬ p4503))
    (h93122 : p4857 ∨ p2819)
    : p2819 ∨ (¬ p2881) ∨ (¬ p2901) ∨ p2774 ∨ (¬ p2829) ∨ p3537 ∨ (¬ p3873) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2248 := h105365;
    let u9 : p4503 := h106530;
    let u10 : (¬ p4857) := (Or.elim h102047 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h93122 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110099 (p2341 p3516 p3945 p5295 : Prop)
    (h109444 : p3516 ∨ (¬ p3945) ∨ (¬ p2341) ∨ (¬ p5295))
    (h102648 : p5295 ∨ p3516)
    : p3516 ∨ (¬ p3945) ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5295) := (Or.elim h109444 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h102648 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110103 (p2396 p2996 p3297 p3516 p3848 p5295 : Prop)
    (h96597 : (¬ p3848) ∨ (¬ p3297) ∨ p2996 ∨ (¬ p2396) ∨ (¬ p5295))
    (h102648 : p5295 ∨ p3516)
    : p3516 ∨ (¬ p3848) ∨ (¬ p2396) ∨ p2996 ∨ (¬ p3297) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3297 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5295) := (Or.elim h96597 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h102648 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110107 (p3516 p3631 p3767 p4322 p4402 p4914 p5295 : Prop)
    (h41759 : (¬ p3631) ∨ (¬ p3767) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4914) ∨ (¬ p5295))
    (h102648 : p5295 ∨ p3516)
    : p3516 ∨ (¬ p3631) ∨ (¬ p3767) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4914) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5295) := (Or.elim h41759 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h102648 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110108 (p2922 p3193 p3246 p3516 p4264 p4277 p5295 : Prop)
    (h105380 : p4277)
    (h54680 : (¬ p2922) ∨ (¬ p3193) ∨ (¬ p3246) ∨ (¬ p4264) ∨ (¬ p4277) ∨ (¬ p5295))
    (h102648 : p5295 ∨ p3516)
    : p3516 ∨ (¬ p3246) ∨ (¬ p4264) ∨ (¬ p2922) ∨ (¬ p3193) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4277 := h105380;
    let u6 : (¬ p5295) := (Or.elim h54680 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h102648 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110109 (p2685 p3246 p3297 p3516 p3755 p4280 p5295 : Prop)
    (h105599 : p4280)
    (h89113 : p3755 ∨ (¬ p3297) ∨ (¬ p5295) ∨ (¬ p2685) ∨ (¬ p4280) ∨ (¬ p3246))
    (h102648 : p5295 ∨ p3516)
    : p3516 ∨ (¬ p2685) ∨ p3755 ∨ (¬ p3246) ∨ (¬ p3297) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3297 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4280 := h105599;
    let u6 : (¬ p5295) := (Or.elim h89113 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h102648 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110124 (p3073 p3266 p3438 p3707 : Prop)
    (h96838 : (¬ p3438) ∨ p3266 ∨ (¬ p3707))
    (h102672 : p3438 ∨ p3073)
    : p3073 ∨ (¬ p3707) ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3438) := (Or.elim h96838 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h102672 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110126 (p3073 p3438 p3449 p3830 p4181 p5122 : Prop)
    (h105483 : p5122)
    (h91349 : (¬ p4181) ∨ p3830 ∨ (¬ p5122) ∨ (¬ p3438) ∨ (¬ p3449))
    (h102672 : p3438 ∨ p3073)
    : p3073 ∨ (¬ p4181) ∨ (¬ p3449) ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5122 := h105483;
    let u5 : (¬ p3438) := (Or.elim h91349 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102672 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110127 (p2459 p3073 p3438 p3449 p3830 p4832 : Prop)
    (h91350 : p3830 ∨ (¬ p3438) ∨ (¬ p3449) ∨ (¬ p4832) ∨ (¬ p2459))
    (h102672 : p3438 ∨ p3073)
    : p3073 ∨ p3830 ∨ (¬ p3449) ∨ (¬ p2459) ∨ (¬ p4832) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4832 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3438) := (Or.elim h91350 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102672 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110128 (p2363 p3073 p3438 p3449 p3830 p4995 : Prop)
    (h91351 : p3830 ∨ (¬ p3438) ∨ (¬ p4995) ∨ (¬ p2363) ∨ (¬ p3449))
    (h102672 : p3438 ∨ p3073)
    : p3073 ∨ (¬ p4995) ∨ p3830 ∨ (¬ p3449) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3438) := (Or.elim h91351 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102672 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110129 (p3073 p3146 p3438 p3449 p3830 p4494 : Prop)
    (h105391 : p4494)
    (h91352 : p3830 ∨ (¬ p3438) ∨ (¬ p3146) ∨ (¬ p3449) ∨ (¬ p4494))
    (h102672 : p3438 ∨ p3073)
    : p3073 ∨ (¬ p3449) ∨ p3830 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4494 := h105391;
    let u5 : (¬ p3438) := (Or.elim h91352 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102672 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110133 (p3073 p3146 p3166 p3286 p3438 p3853 p5063 : Prop)
    (h105474 : p5063)
    (h96837 : p3286 ∨ (¬ p3853) ∨ (¬ p3438) ∨ (¬ p5063) ∨ (¬ p3146) ∨ (¬ p3166))
    (h102672 : p3438 ∨ p3073)
    : p3073 ∨ p3286 ∨ (¬ p3166) ∨ (¬ p3146) ∨ (¬ p3853) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5063 := h105474;
    let u6 : (¬ p3438) := (Or.elim h96837 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h102672 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110137 (p2383 p2528 p3073 p3438 p3654 p4384 p5152 : Prop)
    (h106167 : p4384)
    (h96840 : (¬ p5152) ∨ p3654 ∨ (¬ p4384) ∨ (¬ p2383) ∨ (¬ p3438) ∨ (¬ p2528))
    (h102672 : p3438 ∨ p3073)
    : p3073 ∨ (¬ p5152) ∨ (¬ p2383) ∨ (¬ p2528) ∨ p3654 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4384 := h106167;
    let u6 : (¬ p3438) := (Or.elim h96840 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h102672 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110146 (p3461 p3654 p3767 p4038 : Prop)
    (h27570 : (¬ p3461) ∨ p3767 ∨ (¬ p4038))
    (h96243 : p4038 ∨ (¬ p3654))
    : (¬ p3654) ∨ p3767 ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3767) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4038) := (Or.elim h27570 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h96243 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110147 (p3125 p3654 p3743 p4036 p4038 : Prop)
    (h78642 : (¬ p4036) ∨ (¬ p4038) ∨ (¬ p3743) ∨ p3125)
    (h96243 : p4038 ∨ (¬ p3654))
    : (¬ p3654) ∨ (¬ p4036) ∨ p3125 ∨ (¬ p3743) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4036 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4038) := (Or.elim h78642 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h96243 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110148 (p2578 p3564 p3654 p4036 p4038 : Prop)
    (h98489 : (¬ p4036) ∨ (¬ p4038) ∨ p3564 ∨ (¬ p2578))
    (h96243 : p4038 ∨ (¬ p3654))
    : (¬ p3654) ∨ (¬ p4036) ∨ (¬ p2578) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4036 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4038) := (Or.elim h98489 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96243 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110150 (p3286 p3654 p3987 p4036 p4038 p4190 : Prop)
    (h84986 : p3286 ∨ (¬ p4036) ∨ (¬ p3987) ∨ (¬ p4038) ∨ (¬ p4190))
    (h96243 : p4038 ∨ (¬ p3654))
    : (¬ p3654) ∨ (¬ p4190) ∨ p3286 ∨ (¬ p4036) ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4036 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4038) := (Or.elim h84986 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96243 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110152 (p2797 p3125 p3286 p3654 p3755 p4038 : Prop)
    (h109977 : p3286 ∨ (¬ p4038) ∨ p3125 ∨ (¬ p3755) ∨ p2797)
    (h96243 : p4038 ∨ (¬ p3654))
    : (¬ p3654) ∨ p3286 ∨ p3125 ∨ (¬ p3755) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4038) := (Or.elim h109977 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96243 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110168 (p2563 p2946 p4117 p4272 p5433 p5740 : Prop)
    (h54879 : (¬ p2563) ∨ (¬ p2946) ∨ (¬ p4117) ∨ (¬ p4272) ∨ (¬ p5433))
    (h108244 : p4272 ∨ p5740)
    : p5740 ∨ (¬ p5433) ∨ (¬ p2946) ∨ (¬ p2563) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5740) := (fun h => hn (Or.inl h));
    let u1 : p5433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4272) := (Or.elim h54879 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h108244 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110169 (p3016 p3413 p4272 p4715 p5433 p5740 : Prop)
    (h105423 : p4715)
    (h96092 : (¬ p4272) ∨ (¬ p5433) ∨ p3016 ∨ (¬ p4715) ∨ (¬ p3413))
    (h108244 : p4272 ∨ p5740)
    : p5740 ∨ (¬ p5433) ∨ (¬ p3413) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5740) := (fun h => hn (Or.inl h));
    let u1 : p5433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    let u5 : (¬ p4272) := (Or.elim h96092 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h108244 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110170 (p2946 p2982 p4117 p4272 p5433 p5740 : Prop)
    (h55460 : (¬ p2946) ∨ (¬ p2982) ∨ (¬ p4117) ∨ (¬ p4272) ∨ (¬ p5433))
    (h108244 : p4272 ∨ p5740)
    : p5740 ∨ (¬ p5433) ∨ (¬ p4117) ∨ (¬ p2946) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5740) := (fun h => hn (Or.inl h));
    let u1 : p5433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4272) := (Or.elim h55460 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h108244 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110171 (p2797 p3136 p3745 p4272 p5740 p6119 : Prop)
    (h109214 : p6119 ∨ (¬ p4272) ∨ (¬ p3136) ∨ (¬ p3745) ∨ p2797)
    (h108244 : p4272 ∨ p5740)
    : p5740 ∨ p6119 ∨ (¬ p3136) ∨ (¬ p3745) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5740) := (fun h => hn (Or.inl h));
    let u1 : (¬ p6119) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4272) := (Or.elim h109214 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h108244 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110179 (p2241 p2363 p2383 p2992 p3266 p4272 p5400 p5740 : Prop)
    (h107514 : (¬ p4272) ∨ (¬ p5400) ∨ p3266 ∨ (¬ p2241) ∨ p2363 ∨ p2383 ∨ (¬ p2992))
    (h108244 : p4272 ∨ p5740)
    : p5740 ∨ p2363 ∨ p2383 ∨ (¬ p2992) ∨ (¬ p2241) ∨ p3266 ∨ (¬ p5400) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5740) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4272) := (Or.elim h107514 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (False.elim (r5 u3))))))))))))));
    (Or.elim h108244 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110180 (p2241 p2307 p2396 p2761 p2992 p4272 p5400 p5740 : Prop)
    (h107519 : (¬ p4272) ∨ (¬ p5400) ∨ (¬ p2241) ∨ (¬ p2992) ∨ p2396 ∨ p2761 ∨ p2307)
    (h108244 : p4272 ∨ p5740)
    : p5740 ∨ p2761 ∨ (¬ p2992) ∨ (¬ p2241) ∨ p2307 ∨ p2396 ∨ (¬ p5400) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5740) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4272) := (Or.elim h107519 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (False.elim (u4 r5))))))))))))));
    (Or.elim h108244 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110190 (p2972 p3707 p4322 p4388 : Prop)
    (h19863 : (¬ p3707) ∨ (¬ p4322) ∨ (¬ p4388))
    (h96346 : p4388 ∨ p2972)
    : p2972 ∨ (¬ p3707) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4388) := (Or.elim h19863 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96346 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110192 (p2210 p2972 p2982 p3830 p4388 : Prop)
    (h107197 : p3830 ∨ (¬ p4388) ∨ (¬ p2982) ∨ (¬ p2210))
    (h96346 : p4388 ∨ p2972)
    : p2972 ∨ p3830 ∨ (¬ p2982) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4388) := (Or.elim h107197 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h96346 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110193 (p2608 p2860 p2972 p3105 p3830 p4388 : Prop)
    (h83241 : (¬ p3105) ∨ p2860 ∨ p3830 ∨ (¬ p2608) ∨ (¬ p4388))
    (h96346 : p4388 ∨ p2972)
    : p2972 ∨ p3830 ∨ p2860 ∨ (¬ p2608) ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4388) := (Or.elim h83241 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h96346 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110194 (p2608 p2619 p2972 p3105 p3830 p4388 : Prop)
    (h84840 : (¬ p3105) ∨ p3830 ∨ (¬ p2608) ∨ (¬ p4388) ∨ p2619)
    (h96346 : p4388 ∨ p2972)
    : p2972 ∨ p2619 ∨ p3830 ∨ (¬ p3105) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4388) := (Or.elim h84840 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96346 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110197 (p2192 p2210 p2972 p3830 p4388 p5043 : Prop)
    (h105471 : p5043)
    (h91332 : (¬ p4388) ∨ p3830 ∨ (¬ p5043) ∨ (¬ p2192) ∨ (¬ p2210))
    (h96346 : p4388 ∨ p2972)
    : p2972 ∨ (¬ p2192) ∨ p3830 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5043 := h105471;
    let u5 : (¬ p4388) := (Or.elim h91332 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96346 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110199 (p2427 p2972 p2982 p3379 p3830 p4388 : Prop)
    (h91376 : p3830 ∨ (¬ p4388) ∨ (¬ p3379) ∨ p2427 ∨ (¬ p2982))
    (h96346 : p4388 ∨ p2972)
    : p2972 ∨ p2427 ∨ (¬ p2982) ∨ p3830 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4388) := (Or.elim h91376 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96346 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110200 (p2210 p2972 p3115 p3830 p4388 p4957 : Prop)
    (h96047 : p3830 ∨ (¬ p3115) ∨ (¬ p4388) ∨ (¬ p2210) ∨ (¬ p4957))
    (h96346 : p4388 ∨ p2972)
    : p2972 ∨ p3830 ∨ (¬ p2210) ∨ (¬ p3115) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4388) := (Or.elim h96047 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96346 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110204 (p2440 p2619 p2972 p3105 p3232 p3343 p4388 : Prop)
    (h84684 : (¬ p3105) ∨ (¬ p3232) ∨ p2619 ∨ (¬ p4388) ∨ p3343 ∨ p2440)
    (h96346 : p4388 ∨ p2972)
    : p2972 ∨ p3343 ∨ (¬ p3232) ∨ p2619 ∨ (¬ p3105) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4388) := (Or.elim h84684 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h96346 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110208 (p2972 p2982 p3707 p4386 p4388 p4429 p4702 p5284 : Prop)
    (h106079 : p4702)
    (h63697 : (¬ p2982) ∨ (¬ p3707) ∨ (¬ p4386) ∨ (¬ p4388) ∨ (¬ p4429) ∨ (¬ p4702) ∨ (¬ p5284))
    (h96346 : p4388 ∨ p2972)
    : p2972 ∨ (¬ p3707) ∨ (¬ p4386) ∨ (¬ p5284) ∨ (¬ p4429) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4429 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4702 := h106079;
    let u7 : (¬ p4388) := (Or.elim h63697 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u3))))))))))))));
    (Or.elim h96346 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110211 (p2284 p2972 p3105 p3564 p3958 p4316 p4388 p5152 : Prop)
    (h105378 : p3958)
    (h100657 : (¬ p5152) ∨ p3564 ∨ (¬ p3958) ∨ p2284 ∨ (¬ p4316) ∨ (¬ p3105) ∨ (¬ p4388))
    (h96346 : p4388 ∨ p2972)
    : p2972 ∨ (¬ p5152) ∨ (¬ p3105) ∨ p2284 ∨ p3564 ∨ (¬ p4316) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3958 := h105378;
    let u7 : (¬ p4388) := (Or.elim h100657 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => r5))))))))))));
    (Or.elim h96346 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110213 (p2177 p2341 p2396 p2598 p2850 p2982 p3951 p5257 : Prop)
    (h106536 : p3951)
    (h81059 : (¬ p2396) ∨ (¬ p3951) ∨ p2598 ∨ (¬ p5257) ∨ p2982 ∨ p2850 ∨ (¬ p2341) ∨ p2177)
    (h106357 : p5257 ∨ p2598)
    : (¬ p2396) ∨ (¬ p2341) ∨ p2982 ∨ p2177 ∨ p2850 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3951 := h106536;
    let u7 : (¬ p5257) := (Or.elim h81059 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (u3 r6))))))))))))))));
    (Or.elim h106357 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step110214 (p2264 p2341 p2449 p2598 p3422 p3564 p4625 p5257 : Prop)
    (h106455 : p4625)
    (h86536 : (¬ p2341) ∨ (¬ p2449) ∨ p3564 ∨ p2598 ∨ p3422 ∨ p2264 ∨ (¬ p4625) ∨ (¬ p5257))
    (h106357 : p5257 ∨ p2598)
    : p3422 ∨ p2264 ∨ (¬ p2341) ∨ p2598 ∨ (¬ p2449) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4625 := h106455;
    let u7 : (¬ p5257) := (Or.elim h86536 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => r6))))))))))))));
    (Or.elim h106357 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step110215 (p2860 p2870 p3737 p4228 p5717 : Prop)
    (h86635 : (¬ p3737) ∨ (¬ p5717) ∨ (¬ p2860) ∨ p2870)
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p3737) ∨ p2870 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5717) := (Or.elim h86635 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110216 (p2331 p2553 p3888 p4228 p5717 : Prop)
    (h94674 : (¬ p3888) ∨ (¬ p5717) ∨ p2331 ∨ p2553)
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p3888) ∨ p2553 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5717) := (Or.elim h94674 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110217 (p2668 p3969 p4228 p5577 p5717 : Prop)
    (h109230 : (¬ p5577) ∨ (¬ p5717) ∨ (¬ p3969) ∨ (¬ p2668))
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p5577) ∨ (¬ p3969) ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p5577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5717) := (Or.elim h109230 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110219 (p2331 p2630 p3914 p4228 p4426 p5717 : Prop)
    (h94677 : (¬ p3914) ∨ (¬ p5717) ∨ (¬ p4426) ∨ p2331 ∨ p2630)
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p3914) ∨ (¬ p4426) ∨ p2630 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p3914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5717) := (Or.elim h94677 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110220 (p2797 p3755 p4228 p4367 p5249 p5717 : Prop)
    (h105496 : p5249)
    (h94682 : (¬ p3755) ∨ (¬ p5717) ∨ p2797 ∨ (¬ p4367) ∨ (¬ p5249))
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p3755) ∨ (¬ p4367) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5249 := h105496;
    let u5 : (¬ p5717) := (Or.elim h94682 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110221 (p2751 p2797 p4053 p4228 p4759 p5717 : Prop)
    (h106343 : p2751)
    (h94683 : (¬ p5717) ∨ (¬ p4053) ∨ (¬ p2751) ∨ (¬ p4759) ∨ p2797)
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p4053) ∨ (¬ p4759) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p4053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    let u5 : (¬ p5717) := (Or.elim h94683 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110222 (p2440 p3888 p4194 p4228 p4715 p5717 : Prop)
    (h105423 : p4715)
    (h94684 : (¬ p3888) ∨ (¬ p5717) ∨ (¬ p4194) ∨ (¬ p4715) ∨ p2440)
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p3888) ∨ p2440 ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4715 := h105423;
    let u5 : (¬ p5717) := (Or.elim h94684 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110223 (p2774 p2901 p3914 p4153 p4228 p5717 : Prop)
    (h46104 : (¬ p2774) ∨ (¬ p2901) ∨ (¬ p3914) ∨ (¬ p4153) ∨ (¬ p5717))
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p3914) ∨ (¬ p4153) ∨ (¬ p2774) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p3914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5717) := (Or.elim h46104 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110225 (p3422 p3888 p4153 p4228 p4700 p4753 p5717 : Prop)
    (h105514 : p4753)
    (h59286 : (¬ p3422) ∨ (¬ p3888) ∨ (¬ p4153) ∨ (¬ p4700) ∨ (¬ p4753) ∨ (¬ p5717))
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p3888) ∨ (¬ p4153) ∨ (¬ p4700) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4753 := h105514;
    let u6 : (¬ p5717) := (Or.elim h59286 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110229 (p2241 p2641 p2761 p3051 p3246 p4228 p4521 p5254 p5717 : Prop)
    (h94675 : (¬ p5717) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ p2241 ∨ p2641 ∨ (¬ p5254) ∨ (¬ p4521))
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p5254) ∨ (¬ p3246) ∨ (¬ p3051) ∨ p2241 ∨ p2641 ∨ (¬ p4521) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5717) := (Or.elim h94675 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110230 (p2241 p2641 p2761 p3425 p3434 p4228 p4733 p5254 p5717 : Prop)
    (h105430 : p4733)
    (h94685 : p2641 ∨ p2241 ∨ (¬ p2761) ∨ (¬ p4733) ∨ (¬ p3434) ∨ p3425 ∨ (¬ p5254) ∨ (¬ p5717))
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p2761) ∨ p2641 ∨ p3425 ∨ (¬ p3434) ∨ p2241 ∨ (¬ p5254) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4733 := h105430;
    let u8 : (¬ p5717) := (Or.elim h94685 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => r6))))))))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110232 (p2696 p2761 p2797 p3073 p3449 p4228 p4445 p4736 p5254 p5717 : Prop)
    (h105431 : p4736)
    (h94681 : (¬ p5717) ∨ (¬ p4445) ∨ (¬ p5254) ∨ p2797 ∨ (¬ p3449) ∨ (¬ p3073) ∨ p2696 ∨ (¬ p4736) ∨ (¬ p2761))
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p5254) ∨ (¬ p2761) ∨ (¬ p3449) ∨ p2797 ∨ (¬ p4445) ∨ p2696 ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    let u9 : (¬ p5717) := (Or.elim h94681 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u2))))))))))))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110233 (p2417 p2696 p2761 p2797 p3366 p3389 p3519 p4228 p4376 p5254 p5717 : Prop)
    (h106320 : p4376)
    (h74757 : (¬ p5717) ∨ p2797 ∨ (¬ p5254) ∨ p2696 ∨ (¬ p3389) ∨ (¬ p3366) ∨ (¬ p2417) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2761))
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p2417) ∨ (¬ p3519) ∨ p2797 ∨ (¬ p2761) ∨ p2696 ∨ (¬ p3389) ∨ (¬ p3366) ∨ (¬ p5254) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    let u10 : (¬ p5717) := (Or.elim h74757 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u4))))))))))))))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110234 (p2470 p2528 p2696 p2797 p3266 p3366 p3519 p4228 p4376 p5254 p5717 : Prop)
    (h106320 : p4376)
    (h82732 : (¬ p5717) ∨ (¬ p3519) ∨ p2797 ∨ (¬ p2528) ∨ (¬ p5254) ∨ (¬ p3366) ∨ (¬ p2470) ∨ (¬ p3266) ∨ (¬ p4376) ∨ p2696)
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p5254) ∨ p2797 ∨ (¬ p2470) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3519) ∨ p2696 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    let u10 : (¬ p5717) := (Or.elim h82732 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u7 r8))))))))))))))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110236 (p2696 p2761 p2797 p3051 p3246 p3366 p3370 p4228 p4377 p5254 p5717 : Prop)
    (h106170 : p4377)
    (h94688 : (¬ p3051) ∨ (¬ p3246) ∨ (¬ p2761) ∨ (¬ p5717) ∨ (¬ p4377) ∨ p2797 ∨ (¬ p3366) ∨ p2696 ∨ (¬ p3370) ∨ (¬ p5254))
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p2761) ∨ (¬ p3051) ∨ p2696 ∨ p2797 ∨ (¬ p3246) ∨ (¬ p3370) ∨ (¬ p3366) ∨ (¬ p5254) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4377 := h106170;
    let u10 : (¬ p5717) := (Or.elim h94688 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110237 (p2341 p2696 p2797 p3146 p3266 p3366 p3370 p4132 p4228 p4377 p4988 p5254 p5717 : Prop)
    (h106170 : p4377)
    (h94703 : (¬ p5717) ∨ (¬ p3370) ∨ (¬ p4132) ∨ (¬ p3366) ∨ (¬ p5254) ∨ (¬ p3266) ∨ (¬ p3146) ∨ (¬ p2341) ∨ (¬ p4377) ∨ p2797 ∨ (¬ p4988) ∨ p2696)
    (h108606 : p5717 ∨ p4228)
    : p4228 ∨ (¬ p3146) ∨ (¬ p5254) ∨ p2797 ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p2341) ∨ (¬ p4132) ∨ (¬ p4988) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4377 := h106170;
    let u12 : (¬ p5717) := (Or.elim h94703 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u3 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (u10 r10))))))))))))))))))))))));
    (Or.elim h108606 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110238 (p2241 p3189 p3449 p4262 : Prop)
    (h85053 : (¬ p4262) ∨ (¬ p3449) ∨ p2241)
    (h101048 : p4262 ∨ p3189)
    : p3189 ∨ (¬ p3449) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4262) := (Or.elim h85053 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h101048 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110239 (p2741 p3189 p4262 p4436 : Prop)
    (h40182 : (¬ p2741) ∨ (¬ p4262) ∨ p4436)
    (h101048 : p4262 ∨ p3189)
    : p3189 ∨ p4436 ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4436) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4262) := (Or.elim h40182 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h101048 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110240 (p2750 p3189 p4262 p5317 : Prop)
    (h106345 : p2750)
    (h40333 : (¬ p2750) ∨ (¬ p4262) ∨ p5317)
    (h101048 : p4262 ∨ p3189)
    : p3189 ∨ p5317 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5317) := (fun h => hn (Or.inr h));
    let u2 : p2750 := h106345;
    let u3 : (¬ p4262) := (Or.elim h40333 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h101048 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110243 (p2255 p2946 p3073 p3189 p3256 p4237 p4262 : Prop)
    (h105367 : p2255)
    (h84960 : p3073 ∨ (¬ p3256) ∨ (¬ p2946) ∨ (¬ p2255) ∨ (¬ p4262) ∨ (¬ p4237))
    (h101048 : p4262 ∨ p3189)
    : p3189 ∨ p3073 ∨ (¬ p3256) ∨ (¬ p2946) ∨ (¬ p4237) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2255 := h105367;
    let u6 : (¬ p4262) := (Or.elim h84960 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h101048 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110248 (p2630 p2748 p3073 p3189 p3256 p4262 p5008 : Prop)
    (h105469 : p5008)
    (h87092 : p3073 ∨ (¬ p4262) ∨ (¬ p5008) ∨ (¬ p3256) ∨ (¬ p2748) ∨ (¬ p2630))
    (h101048 : p4262 ∨ p3189)
    : p3189 ∨ p3073 ∨ (¬ p2748) ∨ (¬ p3256) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5008 := h105469;
    let u6 : (¬ p4262) := (Or.elim h87092 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h101048 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110249 (p2088 p2482 p2656 p2992 p3073 p3189 p4262 : Prop)
    (h99080 : p3073 ∨ (¬ p2992) ∨ (¬ p2482) ∨ (¬ p2656) ∨ (¬ p4262) ∨ (¬ p2088))
    (h101048 : p4262 ∨ p3189)
    : p3189 ∨ (¬ p2088) ∨ (¬ p2482) ∨ (¬ p2656) ∨ p3073 ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2482 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4262) := (Or.elim h99080 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h101048 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110251 (p2088 p2727 p3073 p3189 p4066 p4262 p4590 p4650 : Prop)
    (h82272 : p3073 ∨ (¬ p4066) ∨ (¬ p2727) ∨ (¬ p4650) ∨ (¬ p2088) ∨ (¬ p4590) ∨ (¬ p4262))
    (h101048 : p4262 ∨ p3189)
    : p3189 ∨ (¬ p2088) ∨ p3073 ∨ (¬ p4066) ∨ (¬ p4590) ∨ (¬ p2727) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4262) := (Or.elim h82272 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => r5))))))))))));
    (Or.elim h101048 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110252 (p2088 p2745 p2951 p3073 p3136 p3189 p4238 p4262 : Prop)
    (h105523 : p2745)
    (h84373 : p3073 ∨ (¬ p3136) ∨ (¬ p2088) ∨ (¬ p2745) ∨ (¬ p2951) ∨ (¬ p4262) ∨ (¬ p4238))
    (h101048 : p4262 ∨ p3189)
    : p3189 ∨ p3073 ∨ (¬ p2088) ∨ (¬ p3136) ∨ (¬ p2951) ∨ (¬ p4238) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2745 := h105523;
    let u7 : (¬ p4262) := (Or.elim h84373 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h101048 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110255 (p2088 p2745 p2797 p3073 p3189 p3567 p4114 p4262 : Prop)
    (h105523 : p2745)
    (h92263 : (¬ p4114) ∨ p3073 ∨ (¬ p2088) ∨ (¬ p3567) ∨ (¬ p2745) ∨ (¬ p4262) ∨ (¬ p2797))
    (h101048 : p4262 ∨ p3189)
    : p3189 ∨ (¬ p2088) ∨ p3073 ∨ (¬ p3567) ∨ (¬ p4114) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2745 := h105523;
    let u7 : (¬ p4262) := (Or.elim h92263 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h101048 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110257 (p2088 p2745 p2951 p3073 p3136 p3189 p4262 p4590 p4988 : Prop)
    (h105523 : p2745)
    (h85065 : p3073 ∨ (¬ p3136) ∨ (¬ p4590) ∨ (¬ p2951) ∨ (¬ p2745) ∨ (¬ p4988) ∨ (¬ p4262) ∨ (¬ p2088))
    (h101048 : p4262 ∨ p3189)
    : p3189 ∨ (¬ p2088) ∨ p3073 ∨ (¬ p2951) ∨ (¬ p4988) ∨ (¬ p4590) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2745 := h105523;
    let u8 : (¬ p4262) := (Or.elim h85065 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (r6 u1))))))))))))))));
    (Or.elim h101048 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110262 (p2449 p2685 p3755 p4661 : Prop)
    (h25512 : (¬ p2685) ∨ p3755 ∨ (¬ p4661))
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p2685) ∨ p3755 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4661) := (Or.elim h25512 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96421 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110263 (p2449 p3580 p4661 p5176 : Prop)
    (h17468 : (¬ p3580) ∨ (¬ p4661) ∨ p5176)
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ p5176 ∨ (¬ p3580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5176) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4661) := (Or.elim h17468 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h96421 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110265 (p2449 p2807 p3286 p4661 : Prop)
    (h95970 : p3286 ∨ (¬ p4661) ∨ (¬ p2807))
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ p3286 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4661) := (Or.elim h95970 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96421 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110266 (p2417 p2449 p2761 p3506 p4653 p4661 : Prop)
    (h81923 : p2761 ∨ (¬ p3506) ∨ p2417 ∨ (¬ p4661) ∨ (¬ p4653))
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p3506) ∨ p2761 ∨ (¬ p4653) ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4661) := (Or.elim h81923 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96421 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110267 (p2241 p2449 p2761 p2996 p3506 p4661 : Prop)
    (h82081 : (¬ p4661) ∨ p2761 ∨ p2996 ∨ (¬ p3506) ∨ (¬ p2241))
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ p2761 ∨ (¬ p3506) ∨ (¬ p2241) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4661) := (Or.elim h82081 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96421 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110268 (p2449 p2685 p2737 p2761 p3506 p4661 : Prop)
    (h89081 : (¬ p3506) ∨ p2761 ∨ (¬ p2685) ∨ (¬ p4661) ∨ (¬ p2737))
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ p2761 ∨ (¬ p2685) ∨ (¬ p2737) ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4661) := (Or.elim h89081 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96421 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110274 (p2396 p2449 p3276 p3506 p4361 p4451 p4661 : Prop)
    (h105382 : p4361)
    (h100904 : p3276 ∨ (¬ p4661) ∨ (¬ p4451) ∨ p2396 ∨ (¬ p3506) ∨ (¬ p4361))
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ p3276 ∨ (¬ p4451) ∨ (¬ p3506) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4361 := h105382;
    let u6 : (¬ p4661) := (Or.elim h100904 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96421 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110278 (p2132 p2449 p2619 p2761 p2807 p3146 p3506 p3950 p4661 p4786 : Prop)
    (h106425 : p4786)
    (h84804 : p2761 ∨ (¬ p3950) ∨ (¬ p4661) ∨ p3146 ∨ (¬ p4786) ∨ (¬ p3506) ∨ p2132 ∨ p2619 ∨ (¬ p2807))
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ p2619 ∨ (¬ p2807) ∨ p2761 ∨ p2132 ∨ (¬ p3506) ∨ (¬ p3950) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4786 := h106425;
    let u9 : (¬ p4661) := (Or.elim h84804 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (False.elim (r7 u2))))))))))))))))));
    (Or.elim h96421 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110279 (p2449 p2528 p2651 p2685 p2761 p3506 p3641 p3683 p3950 p4661 : Prop)
    (h89028 : (¬ p3506) ∨ p2761 ∨ (¬ p3950) ∨ p2651 ∨ (¬ p3683) ∨ p2528 ∨ (¬ p2685) ∨ (¬ p4661) ∨ p3641)
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ p2528 ∨ p2761 ∨ (¬ p2685) ∨ p3641 ∨ p2651 ∨ (¬ p3683) ∨ (¬ p3950) ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4661) := (Or.elim h89028 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (u4 r7))))))))))))))))));
    (Or.elim h96421 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110280 (p2249 p2449 p2493 p2651 p2761 p2996 p3487 p3506 p3564 p4625 p4661 : Prop)
    (h106513 : p2249)
    (h106455 : p4625)
    (h82100 : (¬ p3506) ∨ p2761 ∨ (¬ p3487) ∨ p2493 ∨ p2996 ∨ (¬ p2249) ∨ p3564 ∨ p2651 ∨ (¬ p4661) ∨ (¬ p4625))
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ p2761 ∨ (¬ p3506) ∨ p2493 ∨ p3564 ∨ p2996 ∨ p2651 ∨ (¬ p3487) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2249 := h106513;
    let u9 : p4625 := h106455;
    let u10 : (¬ p4661) := (Or.elim h82100 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h96421 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110281 (p2449 p2753 p2761 p2807 p3093 p3319 p3379 p3506 p4117 p4625 p4661 : Prop)
    (h106455 : p4625)
    (h100742 : (¬ p2753) ∨ p2761 ∨ (¬ p2807) ∨ (¬ p3506) ∨ (¬ p3379) ∨ p3093 ∨ (¬ p4117) ∨ (¬ p4625) ∨ p3319 ∨ (¬ p4661))
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ p2761 ∨ p3319 ∨ (¬ p2807) ∨ (¬ p3379) ∨ p3093 ∨ (¬ p2753) ∨ (¬ p4117) ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4625 := h106455;
    let u10 : (¬ p4661) := (Or.elim h100742 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u2 q8))) (fun r8 => r8))))))))))))))))));
    (Or.elim h96421 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110282 (p2145 p2156 p2449 p2563 p2761 p2807 p2982 p3506 p3951 p4117 p4661 : Prop)
    (h106536 : p3951)
    (h100766 : p2761 ∨ (¬ p3506) ∨ (¬ p3951) ∨ (¬ p4661) ∨ p2156 ∨ p2982 ∨ (¬ p4117) ∨ (¬ p2807) ∨ (¬ p2563) ∨ (¬ p2145))
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ p2156 ∨ (¬ p2807) ∨ (¬ p2145) ∨ (¬ p2563) ∨ p2982 ∨ p2761 ∨ (¬ p3506) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3951 := h106536;
    let u10 : (¬ p4661) := (Or.elim h100766 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u3))))))))))))))))))));
    (Or.elim h96421 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110285 (p2246 p2352 p2383 p2449 p2749 p2761 p2807 p3096 p3125 p3506 p3645 p4198 p4202 p4625 p4661 : Prop)
    (h106455 : p4625)
    (h102373 : (¬ p4661) ∨ (¬ p2352) ∨ (¬ p4625) ∨ (¬ p4198) ∨ p2383 ∨ p2761 ∨ (¬ p2246) ∨ p3125 ∨ (¬ p3506) ∨ (¬ p3096) ∨ (¬ p3645) ∨ (¬ p2807) ∨ (¬ p2749) ∨ (¬ p4202))
    (h96421 : p4661 ∨ (¬ p2449))
    : (¬ p2449) ∨ p2761 ∨ (¬ p2352) ∨ p2383 ∨ p3125 ∨ (¬ p3096) ∨ (¬ p3506) ∨ (¬ p2246) ∨ (¬ p4198) ∨ (¬ p3645) ∨ (¬ p2807) ∨ (¬ p4202) ∨ (¬ p2749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p4625 := h106455;
    let u14 : (¬ p4661) := (Or.elim h102373 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u12))) (fun r12 => (False.elim (r12 u11))))))))))))))))))))))))))));
    (Or.elim h96421 (fun q0 => (False.elim (u14 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110286 (p2619 p3146 p3609 p4740 : Prop)
    (h25468 : p3146 ∨ (¬ p3609) ∨ (¬ p4740))
    (h96149 : p4740 ∨ p2619)
    : p2619 ∨ p3146 ∨ (¬ p3609) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4740) := (Or.elim h25468 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96149 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110288 (p2220 p2619 p2839 p3537 p4740 : Prop)
    (h83854 : p3537 ∨ (¬ p4740) ∨ (¬ p2839) ∨ (¬ p2220))
    (h96149 : p4740 ∨ p2619)
    : p2619 ∨ p3537 ∨ (¬ p2839) ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4740) := (Or.elim h83854 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h96149 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110289 (p2098 p2132 p2619 p2860 p4740 : Prop)
    (h93749 : (¬ p4740) ∨ p2098 ∨ (¬ p2860) ∨ (¬ p2132))
    (h96149 : p4740 ∨ p2619)
    : p2619 ∨ p2098 ∨ (¬ p2860) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4740) := (Or.elim h93749 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h96149 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110290 (p2619 p2839 p2860 p3537 p4740 : Prop)
    (h93750 : p3537 ∨ (¬ p4740) ∨ (¬ p2860) ∨ (¬ p2839))
    (h96149 : p4740 ∨ p2619)
    : p2619 ∨ p3537 ∨ (¬ p2860) ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4740) := (Or.elim h93750 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h96149 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110291 (p2098 p2132 p2619 p2839 p3146 p4740 : Prop)
    (h90807 : p2098 ∨ p3146 ∨ p2839 ∨ (¬ p4740) ∨ (¬ p2132))
    (h96149 : p4740 ∨ p2619)
    : p2619 ∨ p3146 ∨ p2839 ∨ (¬ p2132) ∨ p2098 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4740) := (Or.elim h90807 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96149 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110292 (p2098 p2132 p2619 p3156 p4740 p4906 : Prop)
    (h105632 : p4906)
    (h93752 : p2098 ∨ (¬ p4740) ∨ (¬ p2132) ∨ (¬ p4906) ∨ (¬ p3156))
    (h96149 : p4740 ∨ p2619)
    : p2619 ∨ p2098 ∨ (¬ p2132) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4906 := h105632;
    let u5 : (¬ p4740) := (Or.elim h93752 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96149 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110293 (p2619 p2839 p2870 p2881 p3537 p4740 : Prop)
    (h109423 : p2881 ∨ (¬ p4740) ∨ p3537 ∨ (¬ p2839) ∨ (¬ p2870))
    (h96149 : p4740 ∨ p2619)
    : p2619 ∨ p2881 ∨ p3537 ∨ (¬ p2839) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4740) := (Or.elim h109423 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96149 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110297 (p2098 p2132 p2166 p2619 p4740 p4960 p5051 : Prop)
    (h106209 : p4960)
    (h90806 : p2098 ∨ (¬ p5051) ∨ (¬ p2166) ∨ (¬ p2132) ∨ (¬ p4740) ∨ (¬ p4960))
    (h96149 : p4740 ∨ p2619)
    : p2619 ∨ p2098 ∨ (¬ p2132) ∨ (¬ p5051) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4960 := h106209;
    let u6 : (¬ p4740) := (Or.elim h90806 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96149 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110310 (p3319 p3461 p3707 p5148 : Prop)
    (h22326 : p3461 ∨ (¬ p3707) ∨ (¬ p5148))
    (h102471 : p5148 ∨ p3319)
    : p3319 ∨ p3461 ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3319) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5148) := (Or.elim h22326 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h102471 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110312 (p2501 p3093 p3319 p3564 p3830 p5148 : Prop)
    (h91335 : (¬ p5148) ∨ p3830 ∨ (¬ p3564) ∨ (¬ p2501) ∨ (¬ p3093))
    (h102471 : p5148 ∨ p3319)
    : p3319 ∨ (¬ p3564) ∨ p3830 ∨ (¬ p3093) ∨ (¬ p2501) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3319) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5148) := (Or.elim h91335 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102471 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110314 (p3093 p3309 p3319 p3323 p3830 p5148 : Prop)
    (h91340 : p3830 ∨ (¬ p3323) ∨ (¬ p3093) ∨ (¬ p5148) ∨ (¬ p3309))
    (h102471 : p5148 ∨ p3319)
    : p3319 ∨ (¬ p3309) ∨ p3830 ∨ (¬ p3323) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3319) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5148) := (Or.elim h91340 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102471 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110315 (p3093 p3319 p3483 p3830 p4867 p5148 : Prop)
    (h106410 : p4867)
    (h91341 : p3830 ∨ (¬ p3483) ∨ (¬ p5148) ∨ (¬ p4867) ∨ (¬ p3093))
    (h102471 : p5148 ∨ p3319)
    : p3319 ∨ p3830 ∨ (¬ p3483) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3319) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4867 := h106410;
    let u5 : (¬ p5148) := (Or.elim h91341 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102471 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110318 (p3093 p3319 p3323 p3830 p4024 p4843 p5148 : Prop)
    (h105449 : p4843)
    (h91334 : p3830 ∨ (¬ p5148) ∨ (¬ p4843) ∨ (¬ p4024) ∨ (¬ p3323) ∨ (¬ p3093))
    (h102471 : p5148 ∨ p3319)
    : p3319 ∨ (¬ p3323) ∨ p3830 ∨ (¬ p4024) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3319) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4843 := h105449;
    let u6 : (¬ p5148) := (Or.elim h91334 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h102471 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110320 (p2295 p3093 p3319 p3830 p3922 p4620 p5148 : Prop)
    (h93189 : p3830 ∨ (¬ p3922) ∨ (¬ p3093) ∨ (¬ p2295) ∨ (¬ p5148) ∨ (¬ p4620))
    (h102471 : p5148 ∨ p3319)
    : p3319 ∨ (¬ p2295) ∨ p3830 ∨ (¬ p3093) ∨ (¬ p3922) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3319) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5148) := (Or.elim h93189 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102471 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110334 (p3193 p3227 p3276 p3707 : Prop)
    (h109268 : p3276 ∨ (¬ p3707) ∨ (¬ p3227))
    (h102252 : p3227 ∨ (¬ p3193))
    : (¬ p3193) ∨ p3276 ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3227) := (Or.elim h109268 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h102252 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110337 (p3193 p3227 p3343 p3379 p3830 p4811 : Prop)
    (h105633 : p4811)
    (h91355 : p3830 ∨ (¬ p3343) ∨ (¬ p4811) ∨ (¬ p3379) ∨ (¬ p3227))
    (h102252 : p3227 ∨ (¬ p3193))
    : (¬ p3193) ∨ p3830 ∨ (¬ p3379) ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4811 := h105633;
    let u5 : (¬ p3227) := (Or.elim h91355 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h102252 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110339 (p3193 p3227 p3333 p3379 p3830 p5214 : Prop)
    (h105492 : p5214)
    (h91390 : p3830 ∨ (¬ p3333) ∨ (¬ p3227) ∨ (¬ p3379) ∨ (¬ p5214))
    (h102252 : p3227 ∨ (¬ p3193))
    : (¬ p3193) ∨ p3830 ∨ (¬ p3379) ∨ (¬ p3333) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5214 := h105492;
    let u5 : (¬ p3227) := (Or.elim h91390 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102252 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110342 (p2396 p3193 p3227 p3355 p3389 p3631 : Prop)
    (h110070 : (¬ p3631) ∨ (¬ p3227) ∨ (¬ p3355) ∨ p2396 ∨ p3389)
    (h102252 : p3227 ∨ (¬ p3193))
    : (¬ p3193) ∨ (¬ p3631) ∨ (¬ p3355) ∨ p2396 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3227) := (Or.elim h110070 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h102252 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110353 (p2122 p2753 p2774 p3193 p3227 p3276 p3379 p3791 p3830 p4826 : Prop)
    (h105444 : p4826)
    (h91385 : p3276 ∨ (¬ p3791) ∨ (¬ p4826) ∨ (¬ p2122) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p2774) ∨ p3830 ∨ (¬ p3227))
    (h102252 : p3227 ∨ (¬ p3193))
    : (¬ p3193) ∨ (¬ p3791) ∨ p3276 ∨ (¬ p3379) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p2753) ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4826 := h105444;
    let u9 : (¬ p3227) := (Or.elim h91385 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => r7))))))))))))))));
    (Or.elim h102252 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110360 (p3707 p3847 p3852 p5284 : Prop)
    (h96805 : (¬ p5284) ∨ (¬ p3847) ∨ (¬ p3707))
    (h108931 : p3852 ∨ p3847)
    : p3852 ∨ (¬ p3707) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3852) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3847) := (Or.elim h96805 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h108931 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step110364 (p2608 p3266 p3830 p3847 p3852 p5284 : Prop)
    (h91328 : (¬ p5284) ∨ p3830 ∨ (¬ p3266) ∨ (¬ p3847) ∨ (¬ p2608))
    (h108931 : p3852 ∨ p3847)
    : p3852 ∨ (¬ p5284) ∨ p3830 ∨ (¬ p2608) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3852) := (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3847) := (Or.elim h91328 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h108931 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step110366 (p2608 p2630 p3755 p3830 p3847 p3852 : Prop)
    (h94966 : p3830 ∨ (¬ p3755) ∨ (¬ p3847) ∨ p2630 ∨ (¬ p2608))
    (h108931 : p3852 ∨ p3847)
    : p3852 ∨ (¬ p3755) ∨ p2630 ∨ p3830 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3852) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3847) := (Or.elim h94966 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h108931 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step110367 (p2608 p3136 p3755 p3830 p3847 p3852 : Prop)
    (h96803 : (¬ p3755) ∨ p3830 ∨ (¬ p3847) ∨ (¬ p2608) ∨ p3136)
    (h108931 : p3852 ∨ p3847)
    : p3852 ∨ (¬ p3755) ∨ (¬ p2608) ∨ p3136 ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3852) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3847) := (Or.elim h96803 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h108931 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step110376 (p2553 p2573 p2608 p3519 p3791 p3830 p3847 p3852 p4376 p4826 p5284 : Prop)
    (h106320 : p4376)
    (h105444 : p4826)
    (h91382 : p3830 ∨ (¬ p3847) ∨ (¬ p4376) ∨ (¬ p4826) ∨ (¬ p5284) ∨ (¬ p2573) ∨ (¬ p3519) ∨ (¬ p3791) ∨ (¬ p2608) ∨ (¬ p2553))
    (h108931 : p3852 ∨ p3847)
    : p3852 ∨ (¬ p3791) ∨ (¬ p2573) ∨ (¬ p5284) ∨ (¬ p2608) ∨ (¬ p2553) ∨ (¬ p3519) ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3852) := (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p4826 := h105444;
    let u10 : (¬ p3847) := (Or.elim h91382 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u5))))))))))))))))))));
    (Or.elim h108931 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step110379 (p2255 p2957 p2992 p3051 p3246 p3286 p3461 p3707 p3847 p3852 p4621 : Prop)
    (h105367 : p2255)
    (h105407 : p4621)
    (h96804 : (¬ p3707) ∨ p2992 ∨ (¬ p2957) ∨ (¬ p3286) ∨ p3051 ∨ p3461 ∨ (¬ p3847) ∨ (¬ p2255) ∨ p3246 ∨ (¬ p4621))
    (h108931 : p3852 ∨ p3847)
    : p3852 ∨ p3461 ∨ (¬ p3707) ∨ (¬ p2957) ∨ p3246 ∨ (¬ p3286) ∨ p3051 ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3852) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2255 := h105367;
    let u9 : p4621 := h105407;
    let u10 : (¬ p3847) := (Or.elim h96804 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h108931 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step110380 (p2255 p2573 p2662 p2727 p2761 p3286 p3564 p3707 p3847 p3852 p4625 : Prop)
    (h105367 : p2255)
    (h106455 : p4625)
    (h99124 : p2761 ∨ (¬ p3707) ∨ p2573 ∨ (¬ p3847) ∨ (¬ p2662) ∨ (¬ p4625) ∨ (¬ p3286) ∨ p3564 ∨ p2727 ∨ (¬ p2255))
    (h108931 : p3852 ∨ p3847)
    : p3852 ∨ (¬ p3707) ∨ p3564 ∨ p2761 ∨ p2573 ∨ p2727 ∨ (¬ p2662) ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3852) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2255 := h105367;
    let u9 : p4625 := h106455;
    let u10 : (¬ p3847) := (Or.elim h99124 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h108931 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step110381 (p2220 p2373 p2427 p2608 p3005 p3519 p3755 p3830 p3847 p3852 p4376 p4399 : Prop)
    (h106320 : p4376)
    (h78932 : (¬ p3755) ∨ p3830 ∨ (¬ p4399) ∨ (¬ p3847) ∨ (¬ p3519) ∨ (¬ p2427) ∨ (¬ p2220) ∨ p2373 ∨ p3005 ∨ (¬ p4376) ∨ (¬ p2608))
    (h108931 : p3852 ∨ p3847)
    : p3852 ∨ p2373 ∨ (¬ p2608) ∨ (¬ p2220) ∨ p3005 ∨ (¬ p3755) ∨ p3830 ∨ (¬ p3519) ∨ (¬ p4399) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3852) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4376 := h106320;
    let u11 : (¬ p3847) := (Or.elim h78932 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u2))))))))))))))))))))));
    (Or.elim h108931 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u11 r0)))))

theorem step110385 (p3619 p4233 p5351 p6092 : Prop)
    (h109022 : (¬ p5351) ∨ (¬ p6092) ∨ (¬ p4233) ∨ (¬ p3619))
    (h9196 : p4233 ∨ (¬ p5351))
    : (¬ p5351) ∨ (¬ p6092) ∨ (¬ p3619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5351 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6092 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4233) := (Or.elim h109022 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h9196 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110386 (p2753 p3599 p4233 p5351 : Prop)
    (h109024 : (¬ p5351) ∨ (¬ p4233) ∨ (¬ p2753) ∨ p3599)
    (h9196 : p4233 ∨ (¬ p5351))
    : (¬ p5351) ∨ (¬ p2753) ∨ p3599 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5351 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4233) := (Or.elim h109024 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h9196 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110388 (p3619 p4233 p5351 p6092 : Prop)
    (h109023 : p6092 ∨ p5351 ∨ (¬ p4233) ∨ (¬ p3619))
    (h13655 : p4233 ∨ p6092)
    : p6092 ∨ p5351 ∨ (¬ p3619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6092) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5351) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4233) := (Or.elim h109023 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h13655 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110391 (p2098 p2598 p3641 p4354 : Prop)
    (h96730 : p2098 ∨ (¬ p4354) ∨ (¬ p2598))
    (h96247 : (¬ p3641) ∨ p4354)
    : (¬ p3641) ∨ p2098 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4354) := (Or.elim h96730 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96247 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step110392 (p3367 p3537 p3641 p4354 : Prop)
    (h96732 : p3537 ∨ (¬ p4354) ∨ (¬ p3367))
    (h96247 : (¬ p3641) ∨ p4354)
    : (¬ p3641) ∨ p3537 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4354) := (Or.elim h96732 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96247 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step110393 (p2509 p2528 p2850 p3609 p3641 p4354 : Prop)
    (h74919 : (¬ p3609) ∨ (¬ p4354) ∨ p2850 ∨ (¬ p2509) ∨ p2528)
    (h96247 : (¬ p3641) ∨ p4354)
    : (¬ p3641) ∨ (¬ p3609) ∨ p2528 ∨ (¬ p2509) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4354) := (Or.elim h74919 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96247 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step110394 (p2850 p3073 p3449 p3609 p3641 p4354 : Prop)
    (h74966 : (¬ p4354) ∨ p3073 ∨ (¬ p3609) ∨ p3449 ∨ p2850)
    (h96247 : (¬ p3641) ∨ p4354)
    : (¬ p3641) ∨ (¬ p3609) ∨ p3073 ∨ p3449 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4354) := (Or.elim h74966 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96247 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step110395 (p3073 p3422 p3449 p3609 p3641 p4354 : Prop)
    (h74967 : (¬ p4354) ∨ p3073 ∨ (¬ p3609) ∨ p3449 ∨ p3422)
    (h96247 : (¬ p3641) ∨ p4354)
    : (¬ p3641) ∨ p3422 ∨ (¬ p3609) ∨ p3073 ∨ p3449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4354) := (Or.elim h74967 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96247 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step110399 (p2528 p2922 p3609 p3641 p4186 p4354 p5214 : Prop)
    (h105492 : p5214)
    (h74916 : (¬ p3609) ∨ p2528 ∨ (¬ p5214) ∨ (¬ p4186) ∨ (¬ p4354) ∨ p2922)
    (h96247 : (¬ p3641) ∨ p4354)
    : (¬ p3641) ∨ (¬ p3609) ∨ p2528 ∨ (¬ p4186) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5214 := h105492;
    let u6 : (¬ p4354) := (Or.elim h74916 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h96247 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step110401 (p2850 p3641 p4019 p4149 p4186 p4354 p4646 : Prop)
    (h105534 : p4646)
    (h102062 : p4149 ∨ (¬ p4019) ∨ (¬ p4186) ∨ (¬ p4354) ∨ p2850 ∨ (¬ p4646))
    (h96247 : (¬ p3641) ∨ p4354)
    : (¬ p3641) ∨ (¬ p4019) ∨ p4149 ∨ p2850 ∨ (¬ p4186) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4149) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4646 := h105534;
    let u6 : (¬ p4354) := (Or.elim h102062 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96247 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step110404 (p2088 p2386 p2850 p3609 p3641 p4197 p4354 p4717 : Prop)
    (h105424 : p4717)
    (h74881 : (¬ p4354) ∨ (¬ p3609) ∨ p2850 ∨ (¬ p4717) ∨ (¬ p4197) ∨ (¬ p2386) ∨ p2088)
    (h96247 : (¬ p3641) ∨ p4354)
    : (¬ p3641) ∨ (¬ p3609) ∨ (¬ p2386) ∨ p2088 ∨ (¬ p4197) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4717 := h105424;
    let u7 : (¬ p4354) := (Or.elim h74881 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (u3 r5))))))))))))));
    (Or.elim h96247 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u7 r0)))))

theorem step110406 (p2230 p2528 p3201 p3609 p3641 p3905 p4354 p4607 : Prop)
    (h88017 : (¬ p4354) ∨ (¬ p3609) ∨ p2230 ∨ (¬ p3905) ∨ (¬ p4607) ∨ p2528 ∨ p3201)
    (h96247 : (¬ p3641) ∨ p4354)
    : (¬ p3641) ∨ (¬ p3609) ∨ p2528 ∨ p3201 ∨ p2230 ∨ (¬ p3905) ∨ (¬ p4607) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4354) := (Or.elim h88017 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (False.elim (u3 r5))))))))))))));
    (Or.elim h96247 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u7 r0)))))

theorem step110409 (p2850 p3232 p3609 p3641 p3670 p3707 p4354 p4953 : Prop)
    (h109464 : (¬ p3609) ∨ (¬ p3232) ∨ (¬ p3670) ∨ p3707 ∨ p2850 ∨ (¬ p4354) ∨ (¬ p4953))
    (h96247 : (¬ p3641) ∨ p4354)
    : (¬ p3641) ∨ (¬ p3609) ∨ (¬ p3232) ∨ (¬ p3670) ∨ p3707 ∨ p2850 ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4354) := (Or.elim h109464 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h96247 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u7 r0)))))

theorem step110416 (p3193 p3232 p4264 p4374 : Prop)
    (h26653 : (¬ p3232) ∨ p4264 ∨ (¬ p4374))
    (h96852 : p3232 ∨ p3193)
    : p3193 ∨ p4264 ∨ (¬ p4374) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4374 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3232) := (Or.elim h26653 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96852 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110419 (p2241 p2437 p3193 p3232 p3343 p3830 : Prop)
    (h89499 : (¬ p3830) ∨ p3343 ∨ (¬ p3232) ∨ (¬ p2437) ∨ p2241)
    (h96852 : p3232 ∨ p3193)
    : p3193 ∨ p3343 ∨ (¬ p3830) ∨ (¬ p2437) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3232) := (Or.elim h89499 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96852 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110420 (p2241 p3016 p3193 p3232 p3343 p3830 : Prop)
    (h96857 : (¬ p3830) ∨ (¬ p3232) ∨ p2241 ∨ (¬ p3016) ∨ p3343)
    (h96852 : p3232 ∨ p3193)
    : p3193 ∨ p3343 ∨ (¬ p3830) ∨ (¬ p3016) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3232) := (Or.elim h96857 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96852 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110421 (p2440 p3193 p3232 p3343 p3399 p3830 : Prop)
    (h96858 : p3399 ∨ (¬ p3830) ∨ p3343 ∨ p2440 ∨ (¬ p3232))
    (h96852 : p3232 ∨ p3193)
    : p3193 ∨ p3343 ∨ (¬ p3830) ∨ p2440 ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3232) := (Or.elim h96858 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h96852 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110423 (p3193 p3232 p3379 p3830 p5160 p5217 : Prop)
    (h105493 : p5217)
    (h96866 : (¬ p3830) ∨ p3379 ∨ (¬ p5217) ∨ (¬ p3232) ∨ (¬ p5160))
    (h96852 : p3232 ∨ p3193)
    : p3193 ∨ (¬ p3830) ∨ (¬ p5160) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5217 := h105493;
    let u5 : (¬ p3232) := (Or.elim h96866 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96852 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110433 (p2440 p2619 p2972 p3105 p3193 p3232 p3343 : Prop)
    (h110204 : p2972 ∨ p3343 ∨ (¬ p3232) ∨ p2619 ∨ (¬ p3105) ∨ p2440)
    (h96852 : p3232 ∨ p3193)
    : p3193 ∨ p2972 ∨ p3343 ∨ p2619 ∨ (¬ p3105) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2972) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3232) := (Or.elim h110204 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h96852 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110438 (p2850 p3193 p3232 p3609 p3641 p3670 p3707 p4953 : Prop)
    (h110409 : (¬ p3641) ∨ (¬ p3609) ∨ (¬ p3232) ∨ (¬ p3670) ∨ p3707 ∨ p2850 ∨ (¬ p4953))
    (h96852 : p3232 ∨ p3193)
    : p3193 ∨ (¬ p3641) ∨ (¬ p3609) ∨ (¬ p3670) ∨ p3707 ∨ p2850 ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3232) := (Or.elim h110409 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h96852 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110442 (p2363 p2819 p3609 p4326 : Prop)
    (h95838 : p3609 ∨ (¬ p4326) ∨ (¬ p2363))
    (h96378 : p4326 ∨ (¬ p2819))
    : (¬ p2819) ∨ p3609 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4326) := (Or.elim h95838 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96378 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110444 (p2098 p2187 p2774 p2819 p4326 : Prop)
    (h107154 : (¬ p2098) ∨ (¬ p4326) ∨ p2187 ∨ p2774)
    (h96378 : p4326 ∨ (¬ p2819))
    : (¬ p2819) ∨ (¬ p2098) ∨ p2774 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4326) := (Or.elim h107154 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h96378 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110447 (p2098 p2352 p2774 p2819 p4326 p5225 : Prop)
    (h105495 : p5225)
    (h86428 : (¬ p2098) ∨ (¬ p4326) ∨ p2774 ∨ (¬ p5225) ∨ p2352)
    (h96378 : p4326 ∨ (¬ p2819))
    : (¬ p2819) ∨ (¬ p2098) ∨ p2774 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5225 := h105495;
    let u5 : (¬ p4326) := (Or.elim h86428 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96378 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110449 (p2122 p2819 p2829 p3537 p4326 p4405 : Prop)
    (h105512 : p4405)
    (h89755 : (¬ p4326) ∨ p2122 ∨ (¬ p3537) ∨ p2829 ∨ (¬ p4405))
    (h96378 : p4326 ∨ (¬ p2819))
    : (¬ p2819) ∨ (¬ p3537) ∨ p2829 ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4326) := (Or.elim h89755 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96378 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110453 (p2187 p2819 p2829 p3537 p4326 p4342 p4718 : Prop)
    (h105425 : p4718)
    (h89751 : (¬ p4326) ∨ (¬ p4342) ∨ p2829 ∨ p2187 ∨ (¬ p4718) ∨ (¬ p3537))
    (h96378 : p4326 ∨ (¬ p2819))
    : (¬ p2819) ∨ (¬ p4342) ∨ (¬ p3537) ∨ p2187 ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4718 := h105425;
    let u6 : (¬ p4326) := (Or.elim h89751 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96378 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110454 (p2098 p2122 p2753 p2819 p2829 p4326 p4405 : Prop)
    (h105512 : p4405)
    (h90545 : p2829 ∨ (¬ p4326) ∨ (¬ p2098) ∨ (¬ p4405) ∨ p2122 ∨ (¬ p2753))
    (h96378 : p4326 ∨ (¬ p2819))
    : (¬ p2819) ∨ (¬ p2098) ∨ p2122 ∨ p2829 ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4405 := h105512;
    let u6 : (¬ p4326) := (Or.elim h90545 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96378 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110466 (p2098 p2774 p2819 p2946 p3146 p3156 p3361 p3979 p4326 p4842 p5122 : Prop)
    (h105483 : p5122)
    (h86447 : (¬ p2098) ∨ p3146 ∨ (¬ p3979) ∨ (¬ p3361) ∨ (¬ p4326) ∨ p2774 ∨ p3156 ∨ (¬ p4842) ∨ (¬ p5122) ∨ p2946)
    (h96378 : p4326 ∨ (¬ p2819))
    : (¬ p2819) ∨ p3156 ∨ p3146 ∨ p2946 ∨ p2774 ∨ (¬ p2098) ∨ (¬ p3361) ∨ (¬ p3979) ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5122 := h105483;
    let u10 : (¬ p4326) := (Or.elim h86447 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (u3 r8))))))))))))))))))));
    (Or.elim h96378 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110468 (p3073 p3256 p4351 p5074 : Prop)
    (h109788 : (¬ p3073) ∨ (¬ p5074) ∨ p3256 ∨ (¬ p4351))
    (h96331 : p4351 ∨ (¬ p3073))
    : (¬ p3073) ∨ (¬ p5074) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5074 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4351) := (Or.elim h109788 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h96331 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110469 (p3073 p3609 p4351 p4353 : Prop)
    (h109789 : (¬ p3073) ∨ (¬ p4351) ∨ p3609 ∨ (¬ p4353))
    (h96331 : p4351 ∨ (¬ p3073))
    : (¬ p3073) ∨ p3609 ∨ (¬ p4353) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4353 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4351) := (Or.elim h109789 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96331 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110470 (p3073 p3449 p3830 p4351 : Prop)
    (h91343 : p3830 ∨ (¬ p4351) ∨ (¬ p3449))
    (h96331 : p4351 ∨ (¬ p3073))
    : (¬ p3073) ∨ (¬ p3449) ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4351) := (Or.elim h91343 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h96331 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110471 (p2210 p3073 p3830 p4351 p4496 : Prop)
    (h38355 : (¬ p2210) ∨ p3830 ∨ (¬ p4351) ∨ (¬ p4496))
    (h96331 : p4351 ∨ (¬ p3073))
    : (¬ p3073) ∨ (¬ p4496) ∨ p3830 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4496 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4351) := (Or.elim h38355 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h96331 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110474 (p2528 p3073 p3266 p3707 p4351 p4690 : Prop)
    (h95064 : p3266 ∨ (¬ p3707) ∨ p2528 ∨ (¬ p4690) ∨ (¬ p4351))
    (h96331 : p4351 ∨ (¬ p3073))
    : (¬ p3073) ∨ (¬ p4690) ∨ p2528 ∨ p3266 ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4351) := (Or.elim h95064 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => r3))))))));
    (Or.elim h96331 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110476 (p3073 p3367 p3670 p3707 p3755 p4351 p5316 : Prop)
    (h109476 : p3755 ∨ (¬ p3707) ∨ p3670 ∨ (¬ p4351) ∨ p3367 ∨ (¬ p5316))
    (h96331 : p4351 ∨ (¬ p3073))
    : (¬ p3073) ∨ p3755 ∨ (¬ p3707) ∨ p3670 ∨ p3367 ∨ (¬ p5316) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4351) := (Or.elim h109476 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96331 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110493 (p2246 p2264 p2459 p2608 p2663 p2744 p3073 p3389 p3740 p3830 p4351 p5118 p5693 : Prop)
    (h106503 : p2744)
    (h105482 : p5118)
    (h94210 : (¬ p5693) ∨ p3830 ∨ (¬ p2246) ∨ (¬ p5118) ∨ (¬ p2663) ∨ (¬ p3389) ∨ (¬ p4351) ∨ (¬ p2744) ∨ (¬ p2459) ∨ (¬ p2264) ∨ (¬ p2608) ∨ (¬ p3740))
    (h96331 : p4351 ∨ (¬ p3073))
    : (¬ p3073) ∨ (¬ p5693) ∨ (¬ p3389) ∨ (¬ p2264) ∨ p3830 ∨ (¬ p2663) ∨ (¬ p2246) ∨ (¬ p3740) ∨ (¬ p2608) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    let u11 : p5118 := h105482;
    let u12 : (¬ p4351) := (Or.elim h94210 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u8))) (fun r10 => (False.elim (r10 u7))))))))))))))))))))))));
    (Or.elim h96331 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110494 (p2972 p3680 p3707 p4387 : Prop)
    (h96716 : p3707 ∨ (¬ p3680) ∨ (¬ p4387))
    (h102677 : p4387 ∨ (¬ p2972))
    : (¬ p2972) ∨ p3707 ∨ (¬ p3680) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4387) := (Or.elim h96716 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h102677 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110497 (p2901 p2972 p3115 p3266 p3707 p4387 : Prop)
    (h84056 : p3707 ∨ (¬ p3266) ∨ p3115 ∨ (¬ p4387) ∨ (¬ p2901))
    (h102677 : p4387 ∨ (¬ p2972))
    : (¬ p2972) ∨ p3115 ∨ (¬ p2901) ∨ (¬ p3266) ∨ p3707 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4387) := (Or.elim h84056 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102677 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110498 (p2608 p2619 p2972 p3105 p3830 p4387 : Prop)
    (h84481 : p3105 ∨ (¬ p2619) ∨ (¬ p4387) ∨ (¬ p3830) ∨ p2608)
    (h102677 : p4387 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p3830) ∨ p3105 ∨ (¬ p2619) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4387) := (Or.elim h84481 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h102677 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110499 (p2210 p2972 p3105 p3830 p4387 p4878 : Prop)
    (h105452 : p4878)
    (h84599 : (¬ p4387) ∨ (¬ p3830) ∨ p3105 ∨ (¬ p4878) ∨ p2210)
    (h102677 : p4387 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p3830) ∨ p2210 ∨ p3105 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4878 := h105452;
    let u5 : (¬ p4387) := (Or.elim h84599 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h102677 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110500 (p2241 p2284 p2972 p3115 p3830 p4387 : Prop)
    (h93022 : p3115 ∨ (¬ p4387) ∨ p2241 ∨ (¬ p3830) ∨ (¬ p2284))
    (h102677 : p4387 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p3830) ∨ p2241 ∨ p3115 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4387) := (Or.elim h93022 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102677 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110501 (p2210 p2972 p2982 p3830 p4387 p4632 : Prop)
    (h106257 : p4632)
    (h96718 : (¬ p4387) ∨ (¬ p3830) ∨ (¬ p4632) ∨ p2210 ∨ p2982)
    (h102677 : p4387 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p3830) ∨ p2210 ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4632 := h106257;
    let u5 : (¬ p4387) := (Or.elim h96718 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102677 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110504 (p2210 p2972 p3115 p3830 p4387 p4960 : Prop)
    (h106209 : p4960)
    (h96721 : (¬ p4387) ∨ (¬ p3830) ∨ (¬ p4960) ∨ p3115 ∨ p2210)
    (h102677 : p4387 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p3830) ∨ p2210 ∨ p3115 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4960 := h106209;
    let u5 : (¬ p4387) := (Or.elim h96721 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h102677 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110505 (p2972 p2982 p3115 p3276 p3707 p4387 : Prop)
    (h110003 : (¬ p2982) ∨ p3707 ∨ (¬ p3276) ∨ p3115 ∨ (¬ p4387))
    (h102677 : p4387 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p2982) ∨ p3707 ∨ (¬ p3276) ∨ p3115 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4387) := (Or.elim h110003 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h102677 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110507 (p2363 p2972 p3266 p3707 p4335 p4387 p4433 : Prop)
    (h106150 : p4433)
    (h84052 : p3707 ∨ (¬ p3266) ∨ (¬ p4433) ∨ (¬ p4335) ∨ (¬ p4387) ∨ (¬ p2363))
    (h102677 : p4387 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p4335) ∨ (¬ p3266) ∨ (¬ p2363) ∨ p3707 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4433 := h106150;
    let u6 : (¬ p4387) := (Or.elim h84052 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h102677 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110510 (p2417 p2870 p2972 p3105 p4387 p4647 p5358 : Prop)
    (h105412 : p4647)
    (h96723 : p3105 ∨ (¬ p5358) ∨ (¬ p4387) ∨ (¬ p2417) ∨ (¬ p2870) ∨ (¬ p4647))
    (h102677 : p4387 ∨ (¬ p2972))
    : (¬ p2972) ∨ p3105 ∨ (¬ p5358) ∨ (¬ p2870) ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4647 := h105412;
    let u6 : (¬ p4387) := (Or.elim h96723 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102677 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110515 (p2088 p2972 p3005 p3136 p3171 p3266 p3680 p4374 p4387 : Prop)
    (h109813 : (¬ p2088) ∨ p3266 ∨ (¬ p3005) ∨ (¬ p3680) ∨ (¬ p3171) ∨ p3136 ∨ (¬ p4374) ∨ (¬ p4387))
    (h102677 : p4387 ∨ (¬ p2972))
    : (¬ p2972) ∨ (¬ p2088) ∨ p3266 ∨ (¬ p3005) ∨ (¬ p3680) ∨ (¬ p3171) ∨ p3136 ∨ (¬ p4374) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4374 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4387) := (Or.elim h109813 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => r6))))))))))))));
    (Or.elim h102677 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110518 (p2122 p2241 p2383 p2577 p2744 p2819 p2972 p3115 p3156 p3347 p3830 p4257 p4387 : Prop)
    (h106503 : p2744)
    (h88041 : (¬ p2819) ∨ p2122 ∨ p3115 ∨ (¬ p3156) ∨ (¬ p3347) ∨ (¬ p2744) ∨ (¬ p4257) ∨ p2383 ∨ (¬ p4387) ∨ (¬ p3830) ∨ (¬ p2577) ∨ p2241)
    (h102677 : p4387 ∨ (¬ p2972))
    : (¬ p2972) ∨ p3115 ∨ (¬ p2819) ∨ p2383 ∨ (¬ p3156) ∨ p2122 ∨ p2241 ∨ (¬ p3830) ∨ (¬ p3347) ∨ (¬ p2577) ∨ (¬ p4257) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2744 := h106503;
    let u12 : (¬ p4387) := (Or.elim h88041 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (u6 r10))))))))))))))))))))))));
    (Or.elim h102677 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110519 (p3246 p3571 p3631 p5358 : Prop)
    (h109861 : p3631 ∨ (¬ p3246) ∨ (¬ p3571) ∨ (¬ p5358))
    (h90058 : p5358 ∨ p3631)
    : p3631 ∨ (¬ p3246) ∨ (¬ p3571) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5358) := (Or.elim h109861 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h90058 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110520 (p3246 p3399 p3631 p3830 p5358 : Prop)
    (h107177 : (¬ p5358) ∨ p3830 ∨ (¬ p3246) ∨ (¬ p3399))
    (h90058 : p5358 ∨ p3631)
    : p3631 ∨ (¬ p3246) ∨ p3830 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5358) := (Or.elim h107177 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h90058 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110521 (p2396 p3399 p3631 p3830 p5358 : Prop)
    (h107204 : (¬ p5358) ∨ p3830 ∨ (¬ p3399) ∨ (¬ p2396))
    (h90058 : p5358 ∨ p3631)
    : p3631 ∨ (¬ p2396) ∨ p3830 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5358) := (Or.elim h107204 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h90058 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110523 (p3399 p3527 p3631 p3830 p4666 p5358 : Prop)
    (h105658 : p4666)
    (h85118 : (¬ p5358) ∨ p3830 ∨ (¬ p4666) ∨ (¬ p3527) ∨ (¬ p3399))
    (h90058 : p5358 ∨ p3631)
    : p3631 ∨ (¬ p3527) ∨ (¬ p3399) ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4666 := h105658;
    let u5 : (¬ p5358) := (Or.elim h85118 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h90058 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110524 (p2417 p2930 p3399 p3631 p3830 p5358 : Prop)
    (h105376 : p2930)
    (h91324 : p3830 ∨ (¬ p2417) ∨ (¬ p3399) ∨ (¬ p5358) ∨ (¬ p2930))
    (h90058 : p5358 ∨ p3631)
    : p3631 ∨ (¬ p2417) ∨ (¬ p3399) ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2930 := h105376;
    let u5 : (¬ p5358) := (Or.elim h91324 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h90058 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110530 (p2417 p2870 p2972 p3105 p3631 p5358 : Prop)
    (h110510 : (¬ p2972) ∨ p3105 ∨ (¬ p5358) ∨ (¬ p2870) ∨ (¬ p2417))
    (h90058 : p5358 ∨ p3631)
    : p3631 ∨ (¬ p2972) ∨ p3105 ∨ (¬ p2870) ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5358) := (Or.elim h110510 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h90058 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110532 (p2396 p3631 p3707 p4322 p4402 p4556 p5358 : Prop)
    (h105399 : p4556)
    (h49355 : (¬ p2396) ∨ (¬ p3707) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4556) ∨ (¬ p5358))
    (h90058 : p5358 ∨ p3631)
    : p3631 ∨ (¬ p3707) ∨ (¬ p2396) ∨ (¬ p4322) ∨ (¬ p4402) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4556 := h105399;
    let u6 : (¬ p5358) := (Or.elim h49355 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h90058 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110533 (p3063 p3093 p3631 p3830 p3945 p4133 p5358 : Prop)
    (h105712 : p4133)
    (h83459 : p3830 ∨ (¬ p3063) ∨ (¬ p3945) ∨ (¬ p5358) ∨ (¬ p4133) ∨ (¬ p3093))
    (h90058 : p5358 ∨ p3631)
    : p3631 ∨ (¬ p3063) ∨ p3830 ∨ (¬ p3945) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4133 := h105712;
    let u6 : (¬ p5358) := (Or.elim h83459 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h90058 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110534 (p2717 p3399 p3576 p3631 p3830 p4666 p5358 : Prop)
    (h105658 : p4666)
    (h88112 : (¬ p5358) ∨ p3830 ∨ (¬ p2717) ∨ (¬ p3399) ∨ (¬ p3576) ∨ (¬ p4666))
    (h90058 : p5358 ∨ p3631)
    : p3631 ∨ (¬ p3576) ∨ p3830 ∨ (¬ p3399) ∨ (¬ p2717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4666 := h105658;
    let u6 : (¬ p5358) := (Or.elim h88112 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h90058 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110546 (p2383 p3654 p3990 p5378 p5379 : Prop)
    (h40282 : (¬ p2383) ∨ (¬ p3990) ∨ (¬ p5378) ∨ (¬ p5379))
    (h102640 : p5378 ∨ p3654)
    : p3654 ∨ (¬ p3990) ∨ (¬ p5379) ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5378) := (Or.elim h40282 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h102640 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110551 (p2307 p2553 p3125 p3654 p3958 p5378 p5379 : Prop)
    (h105378 : p3958)
    (h95316 : (¬ p3125) ∨ (¬ p2307) ∨ (¬ p3958) ∨ (¬ p5379) ∨ (¬ p5378) ∨ p2553)
    (h102640 : p5378 ∨ p3654)
    : p3654 ∨ (¬ p2307) ∨ (¬ p3125) ∨ p2553 ∨ (¬ p5379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3958 := h105378;
    let u6 : (¬ p5378) := (Or.elim h95316 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h102640 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110568 (p2255 p2641 p2667 p2891 p2946 p3246 p3412 p3461 p3654 p3773 p4625 p5378 : Prop)
    (h105367 : p2255)
    (h106455 : p4625)
    (h96576 : (¬ p3773) ∨ (¬ p3461) ∨ (¬ p2946) ∨ (¬ p5378) ∨ (¬ p2891) ∨ (¬ p2255) ∨ p2641 ∨ (¬ p3412) ∨ (¬ p3246) ∨ (¬ p2667) ∨ (¬ p4625))
    (h102640 : p5378 ∨ p3654)
    : p3654 ∨ (¬ p3246) ∨ (¬ p3773) ∨ (¬ p2891) ∨ p2641 ∨ (¬ p3461) ∨ (¬ p2667) ∨ (¬ p2946) ∨ (¬ p3412) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2255 := h105367;
    let u10 : p4625 := h106455;
    let u11 : (¬ p5378) := (Or.elim h96576 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u10))))))))))))))))))))));
    (Or.elim h102640 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110571 (p3005 p3256 p3609 p4963 : Prop)
    (h35912 : p3256 ∨ (¬ p3609) ∨ (¬ p4963))
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ p3256 ∨ (¬ p3609) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4963) := (Or.elim h35912 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h102461 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110573 (p2098 p2132 p2860 p3005 p4312 p4963 : Prop)
    (h90785 : (¬ p4963) ∨ p2098 ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p4312))
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ (¬ p4312) ∨ p2098 ∨ (¬ p2860) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4963) := (Or.elim h90785 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102461 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110575 (p2651 p2737 p3005 p3166 p3537 p4963 : Prop)
    (h94086 : (¬ p3166) ∨ p3537 ∨ (¬ p4963) ∨ p2651 ∨ (¬ p2737))
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ p3537 ∨ (¬ p3166) ∨ (¬ p2737) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4963) := (Or.elim h94086 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102461 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110576 (p2098 p2696 p2737 p3005 p3256 p4963 : Prop)
    (h94087 : p2098 ∨ (¬ p4963) ∨ (¬ p2696) ∨ p2737 ∨ p3256)
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ p3256 ∨ p2098 ∨ (¬ p2696) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4963) := (Or.elim h94087 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h102461 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110577 (p2331 p3005 p3166 p3367 p3537 p4963 : Prop)
    (h94090 : (¬ p3166) ∨ p2331 ∨ (¬ p3367) ∨ p3537 ∨ (¬ p4963))
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ p3537 ∨ p2331 ∨ (¬ p3166) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4963) := (Or.elim h94090 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => r3))))))));
    (Or.elim h102461 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110578 (p2098 p2696 p2751 p3005 p3189 p4963 : Prop)
    (h106343 : p2751)
    (h100697 : p2098 ∨ (¬ p3189) ∨ (¬ p4963) ∨ (¬ p2751) ∨ (¬ p2696))
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ (¬ p3189) ∨ p2098 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    let u5 : (¬ p4963) := (Or.elim h100697 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102461 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110580 (p2098 p2630 p2737 p3005 p3366 p4963 p5008 : Prop)
    (h105469 : p5008)
    (h86934 : p2098 ∨ (¬ p3366) ∨ (¬ p2737) ∨ (¬ p5008) ∨ (¬ p2630) ∨ (¬ p4963))
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ (¬ p2630) ∨ p2098 ∨ (¬ p2737) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5008 := h105469;
    let u6 : (¬ p4963) := (Or.elim h86934 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => r4))))))))));
    (Or.elim h102461 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110581 (p2459 p2696 p3005 p3256 p3425 p3685 p4963 : Prop)
    (h88574 : (¬ p3425) ∨ (¬ p3685) ∨ (¬ p2459) ∨ (¬ p4963) ∨ p3256 ∨ (¬ p2696))
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ p3256 ∨ (¬ p2696) ∨ (¬ p3685) ∨ (¬ p3425) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4963) := (Or.elim h88574 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h102461 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110582 (p2881 p2996 p3005 p3189 p4362 p4804 p4963 : Prop)
    (h106173 : p4362)
    (h91968 : (¬ p3189) ∨ (¬ p2996) ∨ (¬ p4804) ∨ (¬ p4963) ∨ (¬ p4362) ∨ p2881)
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ (¬ p3189) ∨ (¬ p4804) ∨ (¬ p2996) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4804 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4362 := h106173;
    let u6 : (¬ p4963) := (Or.elim h91968 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h102461 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110589 (p2406 p2696 p2737 p3005 p3051 p3246 p3256 p3537 p3950 p4109 p4963 : Prop)
    (h82837 : (¬ p3246) ∨ (¬ p2737) ∨ (¬ p3950) ∨ (¬ p4109) ∨ p2696 ∨ (¬ p2406) ∨ (¬ p3051) ∨ (¬ p4963) ∨ p3537 ∨ p3256)
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ (¬ p3246) ∨ p3256 ∨ (¬ p3051) ∨ (¬ p2406) ∨ (¬ p3950) ∨ p3537 ∨ (¬ p4109) ∨ (¬ p2737) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4963) := (Or.elim h82837 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u9 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u6 q8))) (fun r8 => (False.elim (u2 r8))))))))))))))))))));
    (Or.elim h102461 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110590 (p2177 p2553 p2573 p2696 p2737 p3005 p3537 p3873 p4041 p4963 p5190 : Prop)
    (h105487 : p5190)
    (h100395 : p3537 ∨ p2696 ∨ (¬ p3873) ∨ (¬ p4041) ∨ (¬ p2177) ∨ (¬ p2573) ∨ (¬ p5190) ∨ (¬ p2553) ∨ (¬ p4963) ∨ (¬ p2737))
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ (¬ p2573) ∨ (¬ p2737) ∨ p3537 ∨ (¬ p4041) ∨ p2696 ∨ (¬ p2553) ∨ (¬ p3873) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5190 := h105487;
    let u10 : (¬ p4963) := (Or.elim h100395 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (r8 u2))))))))))))))))))));
    (Or.elim h102461 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110593 (p2230 p2427 p2753 p3005 p3073 p3609 p4129 p4419 p4436 p4963 p5560 p5600 : Prop)
    (h106188 : p5560)
    (h94089 : (¬ p5600) ∨ (¬ p4963) ∨ (¬ p2753) ∨ (¬ p2230) ∨ p3073 ∨ (¬ p3609) ∨ (¬ p4419) ∨ (¬ p4436) ∨ (¬ p2427) ∨ (¬ p5560) ∨ (¬ p4129))
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ p3073 ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2753) ∨ (¬ p3609) ∨ (¬ p4129) ∨ (¬ p5600) ∨ (¬ p4436) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4436 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p5560 := h106188;
    let u11 : (¬ p4963) := (Or.elim h94089 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u6))))))))))))))))))))));
    (Or.elim h102461 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110594 (p2383 p2427 p2563 p2778 p3005 p3051 p3256 p4019 p4399 p4419 p4963 p5580 : Prop)
    (h95453 : (¬ p4019) ∨ (¬ p5580) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p2778) ∨ p2383 ∨ p2427 ∨ (¬ p4399) ∨ (¬ p4963) ∨ (¬ p4419) ∨ p3256)
    (h102461 : p4963 ∨ p3005)
    : p3005 ∨ (¬ p4019) ∨ (¬ p5580) ∨ (¬ p3051) ∨ p2383 ∨ p3256 ∨ (¬ p4399) ∨ (¬ p2778) ∨ (¬ p2563) ∨ p2427 ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p4963) := (Or.elim h95453 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u9 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (u5 r9))))))))))))))))))))));
    (Or.elim h102461 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110598 (p2449 p3032 p3631 p5363 : Prop)
    (h110061 : (¬ p3631) ∨ (¬ p5363) ∨ p2449 ∨ (¬ p3032))
    (h96251 : p5363 ∨ (¬ p3631))
    : (¬ p3631) ∨ p2449 ∨ (¬ p3032) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5363) := (Or.elim h110061 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96251 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110600 (p3399 p3631 p3830 p5363 : Prop)
    (h91322 : p3830 ∨ (¬ p5363) ∨ (¬ p3399))
    (h96251 : p5363 ∨ (¬ p3631))
    : (¬ p3631) ∨ p3830 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5363) := (Or.elim h91322 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96251 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110601 (p2241 p3399 p3631 p3846 p5363 : Prop)
    (h95072 : (¬ p3846) ∨ (¬ p3399) ∨ p2241 ∨ (¬ p5363))
    (h96251 : p5363 ∨ (¬ p3631))
    : (¬ p3631) ∨ (¬ p3846) ∨ p2241 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5363) := (Or.elim h95072 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h96251 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110603 (p2241 p2761 p3399 p3631 p3707 p5363 : Prop)
    (h97556 : (¬ p3399) ∨ p2241 ∨ (¬ p3707) ∨ p2761 ∨ (¬ p5363))
    (h96251 : p5363 ∨ (¬ p3631))
    : (¬ p3631) ∨ p2761 ∨ (¬ p3707) ∨ p2241 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5363) := (Or.elim h97556 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => r3))))))));
    (Or.elim h96251 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110609 (p2249 p3038 p3286 p3631 p3707 p5284 p5363 : Prop)
    (h106513 : p2249)
    (h100417 : (¬ p5284) ∨ (¬ p3707) ∨ (¬ p5363) ∨ p3286 ∨ (¬ p2249) ∨ (¬ p3038))
    (h96251 : p5363 ∨ (¬ p3631))
    : (¬ p3631) ∨ p3286 ∨ (¬ p3707) ∨ (¬ p3038) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2249 := h106513;
    let u6 : (¬ p5363) := (Or.elim h100417 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h96251 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110619 (p2427 p2819 p3631 p3707 p4337 p4909 p5274 p5284 p5363 : Prop)
    (h60652 : (¬ p2427) ∨ (¬ p2819) ∨ (¬ p3707) ∨ (¬ p4337) ∨ (¬ p4909) ∨ (¬ p5274) ∨ (¬ p5284) ∨ (¬ p5363))
    (h96251 : p5363 ∨ (¬ p3631))
    : (¬ p3631) ∨ (¬ p5274) ∨ (¬ p5284) ∨ (¬ p3707) ∨ (¬ p4337) ∨ (¬ p2427) ∨ (¬ p4909) ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5363) := (Or.elim h60652 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => r6))))))))))))));
    (Or.elim h96251 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110622 (p2528 p2598 p2761 p3399 p3631 p3641 p3707 p3950 p4736 p5363 : Prop)
    (h105431 : p4736)
    (h97290 : p2528 ∨ p2761 ∨ (¬ p4736) ∨ (¬ p3707) ∨ p3641 ∨ (¬ p3950) ∨ (¬ p3399) ∨ p2598 ∨ (¬ p5363))
    (h96251 : p5363 ∨ (¬ p3631))
    : (¬ p3631) ∨ p2761 ∨ (¬ p3707) ∨ (¬ p3399) ∨ p2598 ∨ p2528 ∨ p3641 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4736 := h105431;
    let u9 : (¬ p5363) := (Or.elim h97290 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => r7))))))))))))))));
    (Or.elim h96251 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110625 (p3506 p3707 p3852 p3853 : Prop)
    (h96793 : p3707 ∨ (¬ p3853) ∨ (¬ p3506))
    (h96785 : p3853 ∨ (¬ p3852))
    : (¬ p3852) ∨ p3707 ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3852 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3853) := (Or.elim h96793 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96785 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110626 (p3189 p3833 p3852 p3853 p4349 : Prop)
    (h94434 : (¬ p3833) ∨ (¬ p4349) ∨ (¬ p3853) ∨ p3189)
    (h96785 : p3853 ∨ (¬ p3852))
    : (¬ p3852) ∨ (¬ p4349) ∨ p3189 ∨ (¬ p3833) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3852 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4349 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3833 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3853) := (Or.elim h94434 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h96785 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110627 (p2630 p3399 p3755 p3830 p3852 p3853 : Prop)
    (h87117 : p3399 ∨ (¬ p3853) ∨ p3755 ∨ (¬ p3830) ∨ (¬ p2630))
    (h96785 : p3853 ∨ (¬ p3852))
    : (¬ p3852) ∨ p3755 ∨ (¬ p3830) ∨ (¬ p2630) ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3852 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3853) := (Or.elim h87117 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96785 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110628 (p2608 p2797 p3755 p3830 p3852 p3853 : Prop)
    (h92302 : (¬ p3830) ∨ (¬ p3853) ∨ p3755 ∨ p2608 ∨ (¬ p2797))
    (h96785 : p3853 ∨ (¬ p3852))
    : (¬ p3852) ∨ (¬ p2797) ∨ p3755 ∨ (¬ p3830) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3852 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3853) := (Or.elim h92302 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96785 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110631 (p2241 p3266 p3506 p3830 p3852 p3853 : Prop)
    (h102253 : p3266 ∨ (¬ p3853) ∨ p2241 ∨ (¬ p3506) ∨ (¬ p3830))
    (h96785 : p3853 ∨ (¬ p3852))
    : (¬ p3852) ∨ (¬ p3830) ∨ p2241 ∨ p3266 ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3852 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3853) := (Or.elim h102253 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96785 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110632 (p2241 p2751 p3755 p3830 p3852 p3853 : Prop)
    (h106343 : p2751)
    (h102254 : p2241 ∨ (¬ p3853) ∨ (¬ p2751) ∨ (¬ p3830) ∨ p3755)
    (h96785 : p3853 ∨ (¬ p3852))
    : (¬ p3852) ∨ p3755 ∨ (¬ p3830) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3852 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    let u5 : (¬ p3853) := (Or.elim h102254 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96785 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110634 (p3073 p3146 p3166 p3286 p3852 p3853 : Prop)
    (h110133 : p3073 ∨ p3286 ∨ (¬ p3166) ∨ (¬ p3146) ∨ (¬ p3853))
    (h96785 : p3853 ∨ (¬ p3852))
    : (¬ p3852) ∨ p3073 ∨ p3286 ∨ (¬ p3166) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3852 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3853) := (Or.elim h110133 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96785 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110641 (p2156 p2187 p2241 p2992 p3506 p3645 p3830 p3852 p3853 p5580 : Prop)
    (h110021 : (¬ p2992) ∨ (¬ p5580) ∨ (¬ p3853) ∨ p2187 ∨ (¬ p3830) ∨ (¬ p3506) ∨ (¬ p3645) ∨ p2156 ∨ p2241)
    (h96785 : p3853 ∨ (¬ p3852))
    : (¬ p3852) ∨ (¬ p2992) ∨ (¬ p5580) ∨ p2187 ∨ (¬ p3830) ∨ (¬ p3506) ∨ (¬ p3645) ∨ p2156 ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3852 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3853) := (Or.elim h110021 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (False.elim (u8 r7))))))))))))))))));
    (Or.elim h96785 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110645 (p2249 p2573 p2656 p2727 p3266 p3286 p3564 p3707 p3852 p3853 p4330 : Prop)
    (h106513 : p2249)
    (h106329 : p4330)
    (h96798 : p3286 ∨ p3707 ∨ (¬ p3564) ∨ (¬ p3853) ∨ (¬ p2573) ∨ (¬ p2249) ∨ (¬ p3266) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p4330))
    (h96785 : p3853 ∨ (¬ p3852))
    : (¬ p3852) ∨ p3286 ∨ (¬ p3266) ∨ (¬ p3564) ∨ (¬ p2573) ∨ (¬ p2727) ∨ (¬ p2656) ∨ p3707 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3852 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2249 := h106513;
    let u9 : p4330 := h106329;
    let u10 : (¬ p3853) := (Or.elim h96798 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h96785 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110653 (p3189 p3833 p3852 p4349 : Prop)
    (h110626 : (¬ p3852) ∨ (¬ p4349) ∨ p3189 ∨ (¬ p3833))
    (h96788 : p3833 ∨ (¬ p3852))
    : (¬ p3852) ∨ (¬ p4349) ∨ p3189 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3852 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4349 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3833) := (Or.elim h110626 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h96788 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110656 (p2417 p2449 p2807 p3286 p4660 : Prop)
    (h107187 : (¬ p4660) ∨ (¬ p3286) ∨ p2417 ∨ p2807)
    (h96420 : p4660 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p3286) ∨ p2417 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4660) := (Or.elim h107187 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h96420 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110657 (p2449 p2761 p2807 p2996 p3286 p4660 : Prop)
    (h82041 : (¬ p3286) ∨ p2996 ∨ (¬ p4660) ∨ p2807 ∨ (¬ p2761))
    (h96420 : p4660 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p2761) ∨ p2807 ∨ (¬ p3286) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4660) := (Or.elim h82041 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96420 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110660 (p2449 p2685 p3246 p3755 p4362 p4660 : Prop)
    (h106173 : p4362)
    (h95832 : (¬ p4660) ∨ (¬ p3755) ∨ (¬ p4362) ∨ p2685 ∨ p3246)
    (h96420 : p4660 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p3755) ∨ p2685 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4362 := h106173;
    let u5 : (¬ p4660) := (Or.elim h95832 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96420 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110661 (p2396 p2449 p2685 p3755 p4361 p4660 : Prop)
    (h105382 : p4361)
    (h95834 : (¬ p3755) ∨ (¬ p4660) ∨ p2396 ∨ (¬ p4361) ∨ p2685)
    (h96420 : p4660 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p3755) ∨ p2685 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4361 := h105382;
    let u5 : (¬ p4660) := (Or.elim h95834 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96420 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110665 (p2396 p2449 p2807 p3286 p3740 p4660 p4712 : Prop)
    (h105422 : p4712)
    (h93221 : (¬ p4660) ∨ (¬ p3286) ∨ p2396 ∨ (¬ p3740) ∨ (¬ p4712) ∨ p2807)
    (h96420 : p4660 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p3740) ∨ p2396 ∨ p2807 ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4712 := h105422;
    let u6 : (¬ p4660) := (Or.elim h93221 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h96420 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110666 (p2298 p2449 p2807 p3246 p3286 p4556 p4660 : Prop)
    (h105399 : p4556)
    (h93226 : (¬ p4660) ∨ (¬ p2298) ∨ (¬ p3286) ∨ p3246 ∨ (¬ p4556) ∨ p2807)
    (h96420 : p4660 ∨ (¬ p2449))
    : (¬ p2449) ∨ p3246 ∨ (¬ p3286) ∨ (¬ p2298) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4556 := h105399;
    let u6 : (¬ p4660) := (Or.elim h93226 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h96420 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110667 (p2417 p2449 p2911 p3146 p4660 p4905 p5107 : Prop)
    (h105995 : p4905)
    (h94567 : p2417 ∨ (¬ p5107) ∨ (¬ p4905) ∨ (¬ p3146) ∨ (¬ p4660) ∨ (¬ p2911))
    (h96420 : p4660 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p5107) ∨ p2417 ∨ (¬ p3146) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4905 := h105995;
    let u6 : (¬ p4660) := (Or.elim h94567 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96420 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110669 (p2396 p2427 p2449 p2982 p4040 p4559 p4660 : Prop)
    (h105701 : p4559)
    (h95218 : (¬ p4660) ∨ (¬ p4040) ∨ (¬ p4559) ∨ p2427 ∨ p2396 ∨ (¬ p2982))
    (h96420 : p4660 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p4040) ∨ (¬ p2982) ∨ p2427 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4559 := h105701;
    let u6 : (¬ p4660) := (Or.elim h95218 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96420 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110672 (p2187 p2230 p2449 p2563 p4658 p4660 p5193 : Prop)
    (h105488 : p5193)
    (h101707 : p4658 ∨ (¬ p4660) ∨ p2230 ∨ p2187 ∨ (¬ p5193) ∨ p2563)
    (h96420 : p4660 ∨ (¬ p2449))
    : (¬ p2449) ∨ p4658 ∨ p2187 ∨ p2230 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4658) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5193 := h105488;
    let u6 : (¬ p4660) := (Or.elim h101707 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h96420 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110680 (p2145 p2449 p2685 p2807 p3266 p3755 p3950 p4032 p4117 p4322 p4660 : Prop)
    (h76734 : (¬ p4322) ∨ (¬ p3266) ∨ (¬ p2145) ∨ (¬ p2807) ∨ (¬ p3755) ∨ (¬ p4660) ∨ (¬ p4117) ∨ (¬ p4032) ∨ (¬ p3950) ∨ p2685)
    (h96420 : p4660 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p4322) ∨ p2685 ∨ (¬ p3266) ∨ (¬ p3755) ∨ (¬ p4032) ∨ (¬ p4117) ∨ (¬ p3950) ∨ (¬ p2807) ∨ (¬ p2145) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4660) := (Or.elim h76734 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (u2 r8))))))))))))))))))));
    (Or.elim h96420 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110683 (p2098 p2717 p3425 p4805 : Prop)
    (h101761 : p2098 ∨ (¬ p4805) ∨ p3425)
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ p2098 ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4805) := (Or.elim h101761 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h77953 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110684 (p2707 p2717 p3537 p4805 : Prop)
    (h36686 : (¬ p2707) ∨ p3537 ∨ (¬ p4805))
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ (¬ p2707) ∨ p3537 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4805) := (Or.elim h36686 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h77953 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110685 (p2459 p2717 p3609 p4423 p4805 p5559 : Prop)
    (h106189 : p5559)
    (h75078 : (¬ p4423) ∨ (¬ p5559) ∨ (¬ p3609) ∨ p2459 ∨ (¬ p4805))
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ (¬ p4423) ∨ (¬ p3609) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4423 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5559 := h106189;
    let u5 : (¬ p4805) := (Or.elim h75078 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h77953 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110686 (p2459 p2608 p2707 p2717 p3609 p4805 : Prop)
    (h75096 : (¬ p3609) ∨ (¬ p2707) ∨ p2459 ∨ (¬ p4805) ∨ (¬ p2608))
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ (¬ p3609) ∨ (¬ p2707) ∨ (¬ p2608) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4805) := (Or.elim h75096 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h77953 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110688 (p2717 p2911 p3434 p4019 p4805 p5558 : Prop)
    (h89415 : (¬ p4019) ∨ (¬ p5558) ∨ (¬ p4805) ∨ p3434 ∨ p2911)
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ (¬ p4019) ∨ (¬ p5558) ∨ p3434 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4805) := (Or.elim h89415 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h77953 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110691 (p2363 p2717 p3550 p3609 p4423 p4805 p5559 : Prop)
    (h106189 : p5559)
    (h75089 : (¬ p4423) ∨ (¬ p5559) ∨ (¬ p3609) ∨ (¬ p4805) ∨ (¬ p3550) ∨ p2363)
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ (¬ p4423) ∨ (¬ p3550) ∨ p2363 ∨ (¬ p3609) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4423 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5559 := h106189;
    let u6 : (¬ p4805) := (Or.elim h75089 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h77953 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110696 (p2373 p2717 p2995 p4019 p4705 p4777 p4805 p5568 : Prop)
    (h106238 : p4705)
    (h95756 : (¬ p4019) ∨ (¬ p5568) ∨ (¬ p2995) ∨ (¬ p4777) ∨ (¬ p4805) ∨ p2373 ∨ (¬ p4705))
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ (¬ p4019) ∨ p2373 ∨ (¬ p2995) ∨ (¬ p5568) ∨ (¬ p4777) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4705 := h106238;
    let u7 : (¬ p4805) := (Or.elim h95756 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h77953 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110697 (p2641 p2667 p2717 p2745 p4019 p4197 p4781 p4805 p5590 : Prop)
    (h105523 : p2745)
    (h102059 : (¬ p4019) ∨ (¬ p5590) ∨ (¬ p4781) ∨ (¬ p2745) ∨ (¬ p2667) ∨ (¬ p4197) ∨ p2641 ∨ (¬ p4805))
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ (¬ p5590) ∨ (¬ p4019) ∨ (¬ p2667) ∨ p2641 ∨ (¬ p4197) ∨ (¬ p4781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2745 := h105523;
    let u8 : (¬ p4805) := (Or.elim h102059 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => r6))))))))))))));
    (Or.elim h77953 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110699 (p2373 p2406 p2459 p2598 p2707 p2717 p3609 p4030 p4805 p4905 : Prop)
    (h105995 : p4905)
    (h75095 : (¬ p3609) ∨ (¬ p4805) ∨ p2459 ∨ p2406 ∨ p2373 ∨ (¬ p4905) ∨ p2598 ∨ (¬ p4030) ∨ (¬ p2707))
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ (¬ p3609) ∨ p2373 ∨ p2459 ∨ (¬ p2707) ∨ p2406 ∨ (¬ p4030) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4905 := h105995;
    let u9 : (¬ p4805) := (Or.elim h75095 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u4))))))))))))))))));
    (Or.elim h77953 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110700 (p2459 p2641 p2668 p2696 p2707 p2717 p2748 p3609 p4503 p4805 : Prop)
    (h106530 : p4503)
    (h82914 : (¬ p2707) ∨ (¬ p3609) ∨ p2641 ∨ p2696 ∨ p2668 ∨ p2459 ∨ (¬ p4503) ∨ (¬ p2748) ∨ (¬ p4805))
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ (¬ p3609) ∨ (¬ p2707) ∨ p2668 ∨ p2641 ∨ (¬ p2748) ∨ p2696 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4503 := h106530;
    let u9 : (¬ p4805) := (Or.elim h82914 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => r7))))))))))))))));
    (Or.elim h77953 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110701 (p2177 p2553 p2573 p2608 p2717 p3434 p3537 p4666 p4805 p5190 : Prop)
    (h105658 : p4666)
    (h105487 : p5190)
    (h102042 : p3434 ∨ (¬ p2553) ∨ (¬ p2177) ∨ p3537 ∨ (¬ p4666) ∨ (¬ p5190) ∨ p2608 ∨ (¬ p2573) ∨ (¬ p4805))
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ p3434 ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ p3537 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4666 := h105658;
    let u8 : p5190 := h105487;
    let u9 : (¬ p4805) := (Or.elim h102042 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => r7))))))))))))))));
    (Or.elim h77953 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110703 (p2248 p2341 p2427 p2440 p2459 p2651 p2717 p3609 p4805 p4898 p5206 : Prop)
    (h105365 : p2248)
    (h105455 : p4898)
    (h74939 : (¬ p4805) ∨ (¬ p2651) ∨ (¬ p2248) ∨ p2440 ∨ (¬ p2427) ∨ p2459 ∨ (¬ p5206) ∨ p2341 ∨ (¬ p4898) ∨ (¬ p3609))
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ (¬ p3609) ∨ p2341 ∨ p2440 ∨ (¬ p2651) ∨ (¬ p2427) ∨ p2459 ∨ (¬ p5206) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2248 := h105365;
    let u9 : p4898 := h105455;
    let u10 : (¬ p4805) := (Or.elim h74939 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u1))))))))))))))))))));
    (Or.elim h77953 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110707 (p2241 p2459 p2668 p2717 p2750 p2753 p3093 p3425 p3609 p4319 p4503 p4805 : Prop)
    (h106530 : p4503)
    (h106345 : p2750)
    (h74942 : (¬ p2753) ∨ p3093 ∨ (¬ p4319) ∨ (¬ p4503) ∨ p2459 ∨ (¬ p3609) ∨ (¬ p2750) ∨ p2668 ∨ (¬ p4805) ∨ p3425 ∨ (¬ p2241))
    (h77953 : p4805 ∨ (¬ p2717))
    : (¬ p2717) ∨ (¬ p3609) ∨ p2668 ∨ p3093 ∨ (¬ p2241) ∨ p3425 ∨ (¬ p2753) ∨ (¬ p4319) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4503 := h106530;
    let u10 : p2750 := h106345;
    let u11 : (¬ p4805) := (Or.elim h74942 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u5 q9))) (fun r9 => (False.elim (r9 u4))))))))))))))))))))));
    (Or.elim h77953 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110714 (p2470 p3367 p3537 p3641 p4730 p5369 : Prop)
    (h106074 : p4730)
    (h77780 : (¬ p5369) ∨ p3537 ∨ (¬ p3367) ∨ (¬ p2470) ∨ (¬ p4730))
    (h102528 : p5369 ∨ p3641)
    : p3641 ∨ p3537 ∨ (¬ p3367) ∨ (¬ p2470) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4730 := h106074;
    let u5 : (¬ p5369) := (Or.elim h77780 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102528 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110715 (p2850 p3367 p3537 p3641 p4608 p5369 : Prop)
    (h105540 : p4608)
    (h87883 : p3537 ∨ (¬ p2850) ∨ (¬ p5369) ∨ (¬ p3367) ∨ (¬ p4608))
    (h102528 : p5369 ∨ p3641)
    : p3641 ∨ p3537 ∨ (¬ p3367) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4608 := h105540;
    let u5 : (¬ p5369) := (Or.elim h87883 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102528 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110716 (p2098 p2598 p3422 p3641 p4595 p5369 : Prop)
    (h95212 : p2098 ∨ (¬ p5369) ∨ (¬ p4595) ∨ (¬ p2598) ∨ (¬ p3422))
    (h102528 : p5369 ∨ p3641)
    : p3641 ∨ p2098 ∨ (¬ p3422) ∨ (¬ p4595) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4595 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5369) := (Or.elim h95212 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102528 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110718 (p2098 p2528 p2598 p3367 p3641 p5369 : Prop)
    (h99635 : p2098 ∨ p2528 ∨ p3367 ∨ (¬ p2598) ∨ (¬ p5369))
    (h102528 : p5369 ∨ p3641)
    : p3641 ∨ p2098 ∨ p2528 ∨ (¬ p2598) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5369) := (Or.elim h99635 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h102528 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110721 (p3083 p3367 p3537 p3641 p4750 p5369 : Prop)
    (h105433 : p4750)
    (h101312 : p3537 ∨ (¬ p3367) ∨ (¬ p4750) ∨ (¬ p5369) ∨ (¬ p3083))
    (h102528 : p5369 ∨ p3641)
    : p3641 ∨ p3537 ∨ (¬ p3083) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4750 := h105433;
    let u5 : (¬ p5369) := (Or.elim h101312 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102528 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110725 (p2098 p2598 p3641 p4149 p5369 p5615 : Prop)
    (h108550 : (¬ p5615) ∨ p4149 ∨ (¬ p2598) ∨ p2098 ∨ (¬ p5369))
    (h102528 : p5369 ∨ p3641)
    : p3641 ∨ (¬ p5615) ∨ p4149 ∨ (¬ p2598) ∨ p2098 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p5615 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4149) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5369) := (Or.elim h108550 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h102528 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110738 (p2528 p2598 p2951 p2992 p3051 p3246 p3367 p3537 p3641 p3950 p5369 : Prop)
    (h102044 : (¬ p2992) ∨ p2528 ∨ (¬ p3246) ∨ (¬ p3950) ∨ p2598 ∨ p3537 ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3367) ∨ (¬ p5369))
    (h102528 : p5369 ∨ p3641)
    : p3641 ∨ (¬ p3246) ∨ (¬ p3051) ∨ (¬ p3367) ∨ (¬ p2992) ∨ p2598 ∨ p2528 ∨ p3537 ∨ (¬ p2951) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p5369) := (Or.elim h102044 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => r8))))))))))))))))));
    (Or.elim h102528 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110740 (p3073 p3440 p4492 p4938 : Prop)
    (h26120 : (¬ p3440) ∨ (¬ p4492) ∨ p4938)
    (h102561 : p3440 ∨ p3073)
    : p3073 ∨ (¬ p4492) ∨ p4938 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4938) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3440) := (Or.elim h26120 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h102561 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110741 (p3073 p3440 p3449 p4374 p4439 : Prop)
    (h95313 : p3449 ∨ (¬ p3440) ∨ (¬ p4374) ∨ (¬ p4439))
    (h102561 : p3440 ∨ p3073)
    : p3073 ∨ (¬ p4439) ∨ p3449 ∨ (¬ p4374) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4439 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4374 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3440) := (Or.elim h95313 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h102561 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110743 (p2459 p3073 p3266 p3440 p3707 p4832 : Prop)
    (h84036 : p3707 ∨ (¬ p3440) ∨ (¬ p3266) ∨ (¬ p2459) ∨ (¬ p4832))
    (h102561 : p3440 ∨ p3073)
    : p3073 ∨ (¬ p3266) ∨ p3707 ∨ (¬ p4832) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4832 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3440) := (Or.elim h84036 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102561 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110744 (p3073 p3266 p3379 p3440 p3449 p3707 : Prop)
    (h84048 : p3707 ∨ p3449 ∨ (¬ p3379) ∨ (¬ p3266) ∨ (¬ p3440))
    (h102561 : p3440 ∨ p3073)
    : p3073 ∨ p3707 ∨ (¬ p3379) ∨ (¬ p3266) ∨ p3449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3440) := (Or.elim h84048 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h102561 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110745 (p2608 p3073 p3266 p3440 p3449 p3707 : Prop)
    (h84049 : p3707 ∨ p3449 ∨ (¬ p3266) ∨ (¬ p2608) ∨ (¬ p3440))
    (h102561 : p3440 ∨ p3073)
    : p3073 ∨ p3707 ∨ (¬ p2608) ∨ (¬ p3266) ∨ p3449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3440) := (Or.elim h84049 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h102561 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110747 (p2982 p3073 p3440 p3680 p3707 p4492 p4629 : Prop)
    (h94611 : p3707 ∨ (¬ p3440) ∨ (¬ p3680) ∨ (¬ p4492) ∨ (¬ p2982) ∨ (¬ p4629))
    (h102561 : p3440 ∨ p3073)
    : p3073 ∨ (¬ p3680) ∨ (¬ p4492) ∨ p3707 ∨ (¬ p2982) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3440) := (Or.elim h94611 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h102561 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110761 (p2248 p2651 p3016 p3073 p3266 p3440 p3449 p3564 p3707 p4330 : Prop)
    (h105365 : p2248)
    (h106329 : p4330)
    (h84050 : (¬ p3266) ∨ p3449 ∨ p3707 ∨ (¬ p4330) ∨ (¬ p2651) ∨ (¬ p3564) ∨ (¬ p3016) ∨ (¬ p3440) ∨ (¬ p2248))
    (h102561 : p3440 ∨ p3073)
    : p3073 ∨ (¬ p3564) ∨ (¬ p2651) ∨ (¬ p3016) ∨ p3449 ∨ (¬ p3266) ∨ p3707 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    let u8 : p4330 := h106329;
    let u9 : (¬ p3440) := (Or.elim h84050 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h102561 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110763 (p2252 p2608 p2750 p2946 p3073 p3146 p3156 p3440 p3830 p4181 p5122 : Prop)
    (h106345 : p2750)
    (h105483 : p5122)
    (h95895 : (¬ p4181) ∨ p3146 ∨ (¬ p3440) ∨ p2608 ∨ p3156 ∨ (¬ p2750) ∨ (¬ p5122) ∨ p2946 ∨ (¬ p2252) ∨ (¬ p3830))
    (h102561 : p3440 ∨ p3073)
    : p3073 ∨ (¬ p3830) ∨ (¬ p4181) ∨ p3146 ∨ p3156 ∨ p2608 ∨ (¬ p2252) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2750 := h106345;
    let u9 : p5122 := h105483;
    let u10 : (¬ p3440) := (Or.elim h95895 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u1))))))))))))))))))));
    (Or.elim h102561 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110766 (p2751 p2951 p2992 p3005 p3051 p3073 p3246 p3266 p3440 p3707 p3950 p4288 : Prop)
    (h106343 : p2751)
    (h94104 : p3707 ∨ (¬ p2951) ∨ (¬ p3266) ∨ (¬ p3246) ∨ p3005 ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p2751) ∨ (¬ p4288) ∨ (¬ p3440) ∨ (¬ p3950))
    (h102561 : p3440 ∨ p3073)
    : p3073 ∨ (¬ p4288) ∨ p3707 ∨ (¬ p3246) ∨ (¬ p3266) ∨ p3005 ∨ (¬ p3051) ∨ (¬ p2992) ∨ (¬ p2951) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2751 := h106343;
    let u11 : (¬ p3440) := (Or.elim h94104 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => q9) (fun r9 => (False.elim (r9 u9))))))))))))))))))))));
    (Or.elim h102561 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110768 (p3727 p5436 p6116 : Prop)
    (h108462 : (¬ p5436) ∨ (¬ p3727) ∨ (¬ p6116))
    (h9380 : p3727 ∨ (¬ p5436))
    : (¬ p5436) ∨ (¬ p6116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5436 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6116 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3727) := (Or.elim h108462 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h9380 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110769 (p3727 p5436 p6116 : Prop)
    (h108463 : p6116 ∨ p5436 ∨ (¬ p3727))
    (h13872 : p3727 ∨ p6116)
    : p6116 ∨ p5436 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5436) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3727) := (Or.elim h108463 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h13872 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110770 (p5433 p5436 p6116 : Prop)
    (h110768 : (¬ p5436) ∨ (¬ p6116))
    (h108454 : p5436 ∨ p5433)
    : p5433 ∨ (¬ p6116) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5433) := (fun h => hn (Or.inl h));
    let u1 : p6116 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5436) := (Or.elim h110768 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h108454 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110771 (p3727 p5436 p6116 : Prop)
    (h9380 : p3727 ∨ (¬ p5436))
    (h110769 : p6116 ∨ p5436)
    : p6116 ∨ p3727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3727) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5436) := (Or.elim h9380 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h110769 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step110777 (p2230 p3054 p3717 p3727 p6116 : Prop)
    (h109352 : p3717 ∨ (¬ p3727) ∨ (¬ p2230) ∨ (¬ p3054))
    (h110771 : p6116 ∨ p3727)
    : p6116 ∨ p3717 ∨ (¬ p2230) ∨ (¬ p3054) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3727) := (Or.elim h109352 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h110771 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step110778 (p3016 p3727 p4700 p4717 p5740 p6116 : Prop)
    (h105424 : p4717)
    (h61311 : (¬ p3016) ∨ (¬ p3727) ∨ (¬ p4700) ∨ (¬ p4717) ∨ (¬ p5740))
    (h110771 : p6116 ∨ p3727)
    : p6116 ∨ (¬ p5740) ∨ (¬ p4700) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4717 := h105424;
    let u5 : (¬ p3727) := (Or.elim h61311 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h110771 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step110780 (p2850 p3096 p3422 p3727 p6116 p6119 : Prop)
    (h109213 : p6119 ∨ (¬ p3727) ∨ (¬ p2850) ∨ p3422 ∨ (¬ p3096))
    (h110771 : p6116 ∨ p3727)
    : p6116 ∨ p6119 ∨ (¬ p2850) ∨ p3422 ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p6119) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3727) := (Or.elim h109213 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h110771 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step110782 (p2563 p2651 p3727 p4236 p4700 p5740 p6116 : Prop)
    (h93880 : (¬ p3727) ∨ (¬ p5740) ∨ p2563 ∨ (¬ p4700) ∨ p2651 ∨ (¬ p4236))
    (h110771 : p6116 ∨ p3727)
    : p6116 ∨ (¬ p5740) ∨ (¬ p4236) ∨ (¬ p4700) ∨ p2651 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3727) := (Or.elim h93880 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h110771 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step110785 (p2331 p2598 p2850 p3323 p3461 p3727 p4789 p5400 p6116 : Prop)
    (h105646 : p4789)
    (h87810 : (¬ p3727) ∨ (¬ p5400) ∨ p2331 ∨ (¬ p2850) ∨ p3461 ∨ (¬ p2598) ∨ (¬ p4789) ∨ p3323)
    (h110771 : p6116 ∨ p3727)
    : p6116 ∨ p3323 ∨ p3461 ∨ p2331 ∨ (¬ p2850) ∨ (¬ p2598) ∨ (¬ p5400) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4789 := h105646;
    let u8 : (¬ p3727) := (Or.elim h87810 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u1 r6))))))))))))))));
    (Or.elim h110771 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u8 r0)))))

theorem step110789 (p2307 p2396 p2598 p2753 p2761 p2850 p3204 p3727 p4870 p5400 p6116 : Prop)
    (h96136 : p2761 ∨ (¬ p5400) ∨ (¬ p2598) ∨ (¬ p3204) ∨ p2396 ∨ (¬ p2850) ∨ (¬ p3727) ∨ p2307 ∨ (¬ p4870) ∨ (¬ p2753))
    (h110771 : p6116 ∨ p3727)
    : p6116 ∨ p2396 ∨ (¬ p5400) ∨ (¬ p2850) ∨ p2761 ∨ (¬ p2753) ∨ (¬ p2598) ∨ (¬ p4870) ∨ p2307 ∨ (¬ p3204) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p3727) := (Or.elim h96136 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u5))))))))))))))))))));
    (Or.elim h110771 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u10 r0)))))

theorem step110792 (p2311 p2341 p2363 p2598 p2753 p2850 p3204 p3266 p3550 p3727 p4870 p5400 p6116 : Prop)
    (h87870 : p3266 ∨ p2363 ∨ (¬ p3204) ∨ (¬ p5400) ∨ (¬ p3727) ∨ (¬ p2311) ∨ (¬ p3550) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p2598) ∨ (¬ p4870) ∨ p2341)
    (h110771 : p6116 ∨ p3727)
    : p6116 ∨ p3266 ∨ (¬ p3550) ∨ (¬ p2850) ∨ p2363 ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2311) ∨ p2341 ∨ (¬ p3204) ∨ (¬ p4870) ∨ (¬ p5400) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p3727) := (Or.elim h87870 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (False.elim (u8 r10))))))))))))))))))))))));
    (Or.elim h110771 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u12 r0)))))

theorem step110793 (p3892 p3901 p6137 : Prop)
    (h14138 : p3901 ∨ p6137)
    (h108034 : p3892 ∨ (¬ p6137))
    : p3892 ∨ p3901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3892) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3901) := (fun h => hn (Or.inr h));
    let u2 : p6137 := (Or.elim h14138 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h108034 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step110799 (p2373 p3979 p5433 p5567 p6116 : Prop)
    (h109884 : (¬ p5567) ∨ (¬ p5433) ∨ (¬ p3979) ∨ (¬ p2373))
    (h110770 : p5433 ∨ (¬ p6116))
    : (¬ p6116) ∨ (¬ p5567) ∨ (¬ p3979) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5433) := (Or.elim h109884 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h110770 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110801 (p3016 p3413 p5433 p5740 p6116 : Prop)
    (h110169 : p5740 ∨ (¬ p5433) ∨ (¬ p3413) ∨ p3016)
    (h110770 : p5433 ∨ (¬ p6116))
    : (¬ p6116) ∨ p5740 ∨ (¬ p3413) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5740) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5433) := (Or.elim h110169 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h110770 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110806 (p2440 p3016 p4203 p5433 p6116 p6118 : Prop)
    (h109036 : p6118 ∨ (¬ p5433) ∨ (¬ p4203) ∨ (¬ p2440) ∨ (¬ p3016))
    (h110770 : p5433 ∨ (¬ p6116))
    : (¬ p6116) ∨ p6118 ∨ (¬ p4203) ∨ (¬ p2440) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p6118) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5433) := (Or.elim h109036 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h110770 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110808 (p2440 p2531 p3083 p5433 p5567 p6116 : Prop)
    (h109079 : (¬ p5567) ∨ (¬ p3083) ∨ (¬ p2531) ∨ (¬ p5433) ∨ (¬ p2440))
    (h110770 : p5433 ∨ (¬ p6116))
    : (¬ p6116) ∨ (¬ p5567) ∨ (¬ p3083) ∨ (¬ p2531) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5433) := (Or.elim h109079 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h110770 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110811 (p2563 p2946 p4117 p5433 p5740 p6116 : Prop)
    (h110168 : p5740 ∨ (¬ p5433) ∨ (¬ p2946) ∨ (¬ p2563) ∨ (¬ p4117))
    (h110770 : p5433 ∨ (¬ p6116))
    : (¬ p6116) ∨ p5740 ∨ (¬ p2946) ∨ (¬ p2563) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5740) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5433) := (Or.elim h110168 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h110770 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110812 (p2946 p2982 p4117 p5433 p5740 p6116 : Prop)
    (h110170 : p5740 ∨ (¬ p5433) ∨ (¬ p4117) ∨ (¬ p2946) ∨ (¬ p2982))
    (h110770 : p5433 ∨ (¬ p6116))
    : (¬ p6116) ∨ p5740 ∨ (¬ p4117) ∨ (¬ p2946) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5740) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5433) := (Or.elim h110170 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h110770 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110814 (p2363 p2383 p2598 p2781 p2850 p3266 p5405 p5433 p6116 : Prop)
    (h96090 : (¬ p5433) ∨ (¬ p5405) ∨ (¬ p2383) ∨ p2850 ∨ p2598 ∨ (¬ p3266) ∨ (¬ p2781) ∨ (¬ p2363))
    (h110770 : p5433 ∨ (¬ p6116))
    : (¬ p6116) ∨ (¬ p5405) ∨ (¬ p2363) ∨ p2850 ∨ (¬ p2383) ∨ (¬ p3266) ∨ (¬ p2781) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5433) := (Or.elim h96090 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u2))))))))))))))));
    (Or.elim h110770 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110815 (p2307 p2396 p2598 p2761 p2781 p2850 p5405 p5433 p6116 : Prop)
    (h96093 : (¬ p5433) ∨ (¬ p2307) ∨ (¬ p2781) ∨ p2598 ∨ (¬ p5405) ∨ (¬ p2396) ∨ (¬ p2761) ∨ p2850)
    (h110770 : p5433 ∨ (¬ p6116))
    : (¬ p6116) ∨ (¬ p5405) ∨ (¬ p2396) ∨ p2850 ∨ (¬ p2761) ∨ p2598 ∨ (¬ p2781) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5433) := (Or.elim h96093 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (u3 r6))))))))))))))));
    (Or.elim h110770 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110820 (p3016 p3379 p3801 p3892 p3901 : Prop)
    (h109239 : p3801 ∨ (¬ p3901) ∨ p3016 ∨ p3379)
    (h110793 : p3892 ∨ p3901)
    : p3892 ∨ p3801 ∨ p3016 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3892) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3801) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3901) := (Or.elim h109239 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h110793 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step110849 (p2563 p2630 p2982 p3115 p3755 p4039 : Prop)
    (h92072 : (¬ p4039) ∨ (¬ p3755) ∨ p2630 ∨ (¬ p2563) ∨ p2982)
    (h102665 : p4039 ∨ (¬ p3115))
    : (¬ p3115) ∨ (¬ p3755) ∨ p2982 ∨ p2630 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4039) := (Or.elim h92072 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h102665 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110850 (p2946 p2992 p3115 p3286 p3680 p4039 : Prop)
    (h93235 : (¬ p3286) ∨ (¬ p4039) ∨ (¬ p2992) ∨ (¬ p3680) ∨ p2946)
    (h102665 : p4039 ∨ (¬ p3115))
    : (¬ p3115) ∨ (¬ p2992) ∨ (¬ p3680) ∨ p2946 ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4039) := (Or.elim h93235 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102665 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110851 (p2946 p3105 p3115 p3286 p4039 p4906 : Prop)
    (h105632 : p4906)
    (h93236 : (¬ p3286) ∨ (¬ p4039) ∨ p2946 ∨ p3105 ∨ (¬ p4906))
    (h102665 : p4039 ∨ (¬ p3115))
    : (¬ p3115) ∨ p3105 ∨ (¬ p3286) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4906 := h105632;
    let u5 : (¬ p4039) := (Or.elim h93236 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102665 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110852 (p2284 p2946 p3115 p3286 p4039 p5046 : Prop)
    (h105472 : p5046)
    (h93239 : (¬ p3286) ∨ (¬ p4039) ∨ p2946 ∨ p2284 ∨ (¬ p5046))
    (h102665 : p4039 ∨ (¬ p3115))
    : (¬ p3115) ∨ p2284 ∨ (¬ p3286) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5046 := h105472;
    let u5 : (¬ p4039) := (Or.elim h93239 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102665 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110855 (p2946 p3115 p3136 p3286 p3680 p4039 : Prop)
    (h101751 : (¬ p4039) ∨ (¬ p3286) ∨ p2946 ∨ (¬ p3136) ∨ (¬ p3680))
    (h102665 : p4039 ∨ (¬ p3115))
    : (¬ p3115) ∨ (¬ p3286) ∨ p2946 ∨ (¬ p3136) ∨ (¬ p3680) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4039) := (Or.elim h101751 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102665 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110859 (p2156 p2957 p3115 p3136 p3755 p4039 p5046 : Prop)
    (h105472 : p5046)
    (h96772 : (¬ p4039) ∨ (¬ p3755) ∨ p3136 ∨ (¬ p2957) ∨ (¬ p5046) ∨ p2156)
    (h102665 : p4039 ∨ (¬ p3115))
    : (¬ p3115) ∨ (¬ p3755) ∨ p2156 ∨ (¬ p2957) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5046 := h105472;
    let u6 : (¬ p4039) := (Or.elim h96772 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u2 r4))))))))))));
    (Or.elim h102665 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110861 (p2563 p2972 p3115 p3125 p3707 p4039 p5284 : Prop)
    (h109781 : p3125 ∨ (¬ p2972) ∨ (¬ p5284) ∨ p2563 ∨ (¬ p3707) ∨ (¬ p4039))
    (h102665 : p4039 ∨ (¬ p3115))
    : (¬ p3115) ∨ p3125 ∨ (¬ p2972) ∨ (¬ p5284) ∨ p2563 ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4039) := (Or.elim h109781 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h102665 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110866 (p2246 p2352 p2363 p2573 p2749 p2946 p3115 p3136 p3347 p3755 p4039 p4450 : Prop)
    (h94949 : (¬ p4039) ∨ p2363 ∨ (¬ p2749) ∨ (¬ p3755) ∨ (¬ p2246) ∨ (¬ p4450) ∨ (¬ p2946) ∨ p2352 ∨ p2573 ∨ (¬ p3347) ∨ p3136)
    (h102665 : p4039 ∨ (¬ p3115))
    : (¬ p3115) ∨ (¬ p3755) ∨ p2363 ∨ (¬ p2946) ∨ p2352 ∨ p2573 ∨ p3136 ∨ (¬ p2246) ∨ (¬ p3347) ∨ (¬ p2749) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p4039) := (Or.elim h94949 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (u6 r9))))))))))))))))))))));
    (Or.elim h102665 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110869 (p2098 p2528 p2598 p2748 p2761 p2972 p3115 p3368 p4039 p4669 p4749 p5284 p5373 : Prop)
    (h105432 : p4749)
    (h105415 : p4669)
    (h76479 : (¬ p5284) ∨ (¬ p4039) ∨ (¬ p4669) ∨ (¬ p2761) ∨ (¬ p3368) ∨ (¬ p2098) ∨ (¬ p2748) ∨ (¬ p4749) ∨ (¬ p2528) ∨ (¬ p5373) ∨ p2598 ∨ p2972)
    (h102665 : p4039 ∨ (¬ p3115))
    : (¬ p3115) ∨ (¬ p5284) ∨ (¬ p2528) ∨ (¬ p2761) ∨ (¬ p2098) ∨ p2972 ∨ p2598 ∨ (¬ p2748) ∨ (¬ p3368) ∨ (¬ p5373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4749 := h105432;
    let u11 : p4669 := h105415;
    let u12 : (¬ p4039) := (Or.elim h76479 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u6 q10))) (fun r10 => (False.elim (u5 r10))))))))))))))))))))))));
    (Or.elim h102665 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110870 (p3323 p3461 p4367 p5284 : Prop)
    (h21126 : (¬ p3461) ∨ (¬ p4367) ∨ (¬ p5284))
    (h95301 : p4367 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3461) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4367) := (Or.elim h21126 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h95301 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110874 (p2797 p3323 p3755 p4228 p4367 : Prop)
    (h110220 : p4228 ∨ (¬ p3755) ∨ (¬ p4367) ∨ p2797)
    (h95301 : p4367 ∨ (¬ p3323))
    : (¬ p3323) ∨ p4228 ∨ (¬ p3755) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4367) := (Or.elim h110220 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h95301 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110876 (p2331 p2797 p3286 p3323 p3461 p4367 : Prop)
    (h92278 : (¬ p3286) ∨ (¬ p4367) ∨ p2331 ∨ (¬ p2797) ∨ (¬ p3461))
    (h95301 : p4367 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3286) ∨ p2331 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4367) := (Or.elim h92278 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h95301 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110878 (p2331 p2797 p3323 p3461 p3755 p4367 : Prop)
    (h94956 : (¬ p3755) ∨ p2797 ∨ (¬ p3461) ∨ (¬ p4367) ∨ (¬ p2331))
    (h95301 : p4367 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3755) ∨ (¬ p3461) ∨ p2797 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4367) := (Or.elim h94956 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h95301 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110879 (p2295 p2797 p3323 p3755 p4367 p4624 : Prop)
    (h105408 : p4624)
    (h94970 : (¬ p3755) ∨ p2797 ∨ p2295 ∨ (¬ p4367) ∨ (¬ p4624))
    (h95301 : p4367 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3755) ∨ p2295 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4624 := h105408;
    let u5 : (¬ p4367) := (Or.elim h94970 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h95301 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110880 (p2797 p3323 p3654 p3755 p4367 p4581 : Prop)
    (h105405 : p4581)
    (h95026 : (¬ p3755) ∨ p2797 ∨ (¬ p4367) ∨ (¬ p4581) ∨ p3654)
    (h95301 : p4367 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3755) ∨ p3654 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4581 := h105405;
    let u5 : (¬ p4367) := (Or.elim h95026 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h95301 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110883 (p2331 p2641 p3286 p3323 p3461 p4367 : Prop)
    (h100300 : (¬ p3286) ∨ (¬ p4367) ∨ (¬ p2641) ∨ (¬ p3461) ∨ p2331)
    (h95301 : p4367 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3461) ∨ (¬ p2641) ∨ p2331 ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4367) := (Or.elim h100300 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h95301 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110884 (p2331 p3286 p3323 p3917 p4367 p4843 : Prop)
    (h105449 : p4843)
    (h101150 : (¬ p3286) ∨ p2331 ∨ (¬ p4367) ∨ (¬ p4843) ∨ (¬ p3917))
    (h95301 : p4367 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3917) ∨ (¬ p3286) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4843 := h105449;
    let u5 : (¬ p4367) := (Or.elim h101150 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h95301 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110885 (p2331 p3286 p3319 p3323 p4367 p4757 : Prop)
    (h101151 : (¬ p3286) ∨ (¬ p4367) ∨ p2331 ∨ (¬ p4757) ∨ p3319)
    (h95301 : p4367 ∨ (¬ p3323))
    : (¬ p3323) ∨ p3319 ∨ (¬ p3286) ∨ p2331 ∨ (¬ p4757) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4757 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4367) := (Or.elim h101151 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h95301 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110898 (p2331 p2459 p2753 p2797 p2911 p3323 p3347 p3389 p3755 p4117 p4330 p4367 : Prop)
    (h106329 : p4330)
    (h94958 : p2911 ∨ (¬ p2753) ∨ (¬ p2331) ∨ (¬ p3347) ∨ (¬ p3755) ∨ (¬ p4330) ∨ (¬ p4117) ∨ (¬ p4367) ∨ p3389 ∨ p2459 ∨ p2797)
    (h95301 : p4367 ∨ (¬ p3323))
    : (¬ p3323) ∨ (¬ p3755) ∨ (¬ p2331) ∨ p3389 ∨ p2797 ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p4117) ∨ p2911 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4330 := h106329;
    let u11 : (¬ p4367) := (Or.elim h94958 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u3 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u9 q9))) (fun r9 => (False.elim (u4 r9))))))))))))))))))))));
    (Or.elim h95301 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step110899 (p2449 p2807 p3286 p4429 : Prop)
    (h93210 : (¬ p4429) ∨ (¬ p3286) ∨ p2807)
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p3286) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4429) := (Or.elim h93210 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h102487 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110900 (p2449 p2996 p3842 p4429 : Prop)
    (h20003 : (¬ p2996) ∨ (¬ p3842) ∨ (¬ p4429))
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p2996) ∨ (¬ p3842) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4429) := (Or.elim h20003 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h102487 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110901 (p2449 p2685 p3755 p4429 : Prop)
    (h94409 : (¬ p4429) ∨ (¬ p3755) ∨ p2685)
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p3755) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4429) := (Or.elim h94409 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h102487 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110904 (p2449 p2761 p3040 p3631 p4429 p5284 : Prop)
    (h41148 : (¬ p2761) ∨ (¬ p3040) ∨ (¬ p3631) ∨ (¬ p4429) ∨ (¬ p5284))
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p3631) ∨ (¬ p5284) ∨ (¬ p3040) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4429) := (Or.elim h41148 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102487 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110905 (p2177 p2449 p2761 p3945 p4429 p5284 : Prop)
    (h71988 : (¬ p2761) ∨ (¬ p5284) ∨ (¬ p4429) ∨ (¬ p3945) ∨ (¬ p2177))
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p3945) ∨ (¬ p5284) ∨ (¬ p2177) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4429) := (Or.elim h71988 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102487 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step110907 (p2264 p2449 p3707 p3830 p4429 p5284 : Prop)
    (h47591 : (¬ p2264) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4429) ∨ (¬ p5284))
    (h102487 : p4429 ∨ p2449)
    : p2449 ∨ (¬ p3830) ∨ (¬ p5284) ∨ (¬ p2264) ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4429) := (Or.elim h47591 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102487 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

end ElevenRUP
