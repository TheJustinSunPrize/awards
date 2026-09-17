import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step107334 (p2774 p2819 p3955 p4232 p4620 p5265 : Prop)
    (h62312 : (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3955) ∨ (¬ p4232) ∨ (¬ p4620) ∨ (¬ p5265))
    (h106261 : p4620 ∨ (¬ p3955))
    : (¬ p4232) ∨ (¬ p5265) ∨ (¬ p3955) ∨ (¬ p2819) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4232 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5265 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4620) := (Or.elim h62312 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h106261 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107337 (p2440 p2659 p2870 p3051 p3698 p3904 : Prop)
    (h94552 : (¬ p2870) ∨ p3051 ∨ (¬ p3904) ∨ (¬ p3698) ∨ p2440 ∨ (¬ p2659))
    (h105739 : p2659 ∨ (¬ p2870))
    : p2440 ∨ p3051 ∨ (¬ p2870) ∨ (¬ p3698) ∨ (¬ p3904) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2659) := (Or.elim h94552 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => r4))))))))));
    (Or.elim h105739 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107338 (p2449 p2870 p3516 p3691 p4386 p5053 : Prop)
    (h94586 : (¬ p3516) ∨ p2449 ∨ (¬ p5053) ∨ (¬ p4386) ∨ (¬ p3691) ∨ (¬ p2870))
    (h105600 : p5053 ∨ (¬ p2870))
    : (¬ p3516) ∨ (¬ p3691) ∨ (¬ p2870) ∨ p2449 ∨ (¬ p4386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5053) := (Or.elim h94586 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h105600 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107339 (p2807 p3323 p3654 p3987 p4194 p4650 : Prop)
    (h95140 : (¬ p3654) ∨ p3323 ∨ (¬ p4650) ∨ p2807 ∨ (¬ p4194) ∨ (¬ p3987))
    (h106245 : p4650 ∨ p2807)
    : (¬ p3654) ∨ p3323 ∨ p2807 ∨ (¬ p4194) ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4650) := (Or.elim h95140 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h106245 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step107343 (p2230 p2427 p3193 p3347 p4952 p5104 : Prop)
    (h96154 : p3193 ∨ (¬ p4952) ∨ p2230 ∨ (¬ p3347) ∨ p2427 ∨ (¬ p5104))
    (h106365 : p5104 ∨ p2427)
    : p3193 ∨ (¬ p4952) ∨ p2230 ∨ p2427 ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5104) := (Or.elim h96154 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => r4))))))))));
    (Or.elim h106365 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step107354 (p2470 p2501 p2656 p3016 p3923 p4157 : Prop)
    (h98920 : (¬ p2470) ∨ (¬ p4157) ∨ (¬ p2656) ∨ p3016 ∨ (¬ p2501) ∨ (¬ p3923))
    (h106509 : p2501 ∨ p3016)
    : (¬ p2470) ∨ (¬ p3923) ∨ (¬ p2656) ∨ p3016 ∨ (¬ p4157) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2501) := (Or.elim h98920 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h106509 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step107356 (p2807 p2911 p3166 p4653 p5074 p5307 : Prop)
    (h99213 : (¬ p3166) ∨ (¬ p5307) ∨ p2807 ∨ p2911 ∨ (¬ p4653) ∨ (¬ p5074))
    (h106436 : p4653 ∨ p2807)
    : (¬ p5307) ∨ (¬ p3166) ∨ p2911 ∨ p2807 ∨ (¬ p5074) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5074 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4653) := (Or.elim h99213 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h106436 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step107358 (p2284 p2608 p2696 p2839 p3136 p4316 : Prop)
    (h100651 : p2608 ∨ p2284 ∨ p2839 ∨ p2696 ∨ p3136 ∨ (¬ p4316))
    (h84419 : p4316 ∨ p3136)
    : p3136 ∨ p2839 ∨ p2608 ∨ p2696 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4316) := (Or.elim h100651 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => r4))))))))));
    (Or.elim h84419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107359 (p2619 p2797 p3156 p4313 p4700 p4972 : Prop)
    (h100812 : (¬ p2619) ∨ p2797 ∨ (¬ p4313) ∨ (¬ p4700) ∨ p3156 ∨ (¬ p4972))
    (h105906 : p4972 ∨ p3156)
    : (¬ p4313) ∨ p2797 ∨ (¬ p2619) ∨ (¬ p4700) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4972) := (Or.elim h100812 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => r4))))))))));
    (Or.elim h105906 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step107363 (p2177 p2319 p2341 p3323 p3567 p4620 : Prop)
    (h102424 : (¬ p2341) ∨ (¬ p2319) ∨ (¬ p4620) ∨ p2177 ∨ p3323 ∨ (¬ p3567))
    (h106260 : p4620 ∨ p3323)
    : p3323 ∨ (¬ p3567) ∨ p2177 ∨ (¬ p2319) ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4620) := (Or.elim h102424 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h106260 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107366 (p2363 p2630 p2668 p2696 p2819 p4972 : Prop)
    (h103358 : (¬ p2668) ∨ (¬ p4972) ∨ (¬ p2630) ∨ p2819 ∨ (¬ p2363) ∨ (¬ p2696))
    (h105837 : p4972 ∨ (¬ p2630))
    : p2819 ∨ (¬ p2696) ∨ (¬ p2630) ∨ (¬ p2363) ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4972) := (Or.elim h103358 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h105837 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107370 (p2177 p2608 p2881 p3449 p3527 p5142 : Prop)
    (h104209 : p3527 ∨ p3449 ∨ (¬ p2177) ∨ (¬ p2881) ∨ (¬ p2608) ∨ (¬ p5142))
    (h105799 : p5142 ∨ (¬ p2177))
    : p3527 ∨ p3449 ∨ (¬ p2881) ∨ (¬ p2177) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5142) := (Or.elim h104209 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h105799 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107372 (p2352 p2363 p2518 p2528 p2573 p3379 : Prop)
    (h104567 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2573) ∨ (¬ p3379) ∨ (¬ p2352) ∨ (¬ p2363))
    (h81453 : (¬ p2518) ∨ (¬ p2528) ∨ p2363 ∨ (¬ p3379))
    : (¬ p2518) ∨ (¬ p3379) ∨ (¬ p2528) ∨ (¬ p2573) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2363) := (Or.elim h104567 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h81453 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step107373 (p2707 p2737 p2829 p3319 p3323 p4842 : Prop)
    (h104863 : (¬ p2707) ∨ p2829 ∨ p3319 ∨ (¬ p2737) ∨ (¬ p3323) ∨ (¬ p4842))
    (h106067 : p4842 ∨ p2829)
    : p2829 ∨ p3319 ∨ (¬ p2737) ∨ (¬ p3323) ∨ (¬ p2707) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4842) := (Or.elim h104863 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => r4))))))))));
    (Or.elim h106067 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107374 (p2187 p2383 p2608 p3093 p4870 p5020 : Prop)
    (h104963 : (¬ p2383) ∨ p2608 ∨ (¬ p3093) ∨ (¬ p5020) ∨ (¬ p4870) ∨ p2187)
    (h102428 : p5020 ∨ (¬ p3093))
    : (¬ p4870) ∨ (¬ p3093) ∨ p2608 ∨ (¬ p2383) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5020) := (Or.elim h104963 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h102428 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step107376 (p2187 p2230 p2406 p2440 p2553 p2563 : Prop)
    (h105334 : (¬ p2406) ∨ p2553 ∨ p2230 ∨ (¬ p2440) ∨ p2563 ∨ p2187)
    (h106911 : (¬ p2230) ∨ (¬ p2440))
    : p2553 ∨ p2187 ∨ (¬ p2406) ∨ (¬ p2440) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2187) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2230 := (Or.elim h105334 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (u1 r4))))))))))));
    (Or.elim h106911 (fun q0 => (False.elim (q0 u5))) (fun r0 => (False.elim (r0 u3)))))

theorem step107377 (p2274 p2608 p2707 p2829 p3309 p4401 : Prop)
    (h106604 : p2829 ∨ (¬ p2707) ∨ p2608 ∨ p2274 ∨ (¬ p3309) ∨ (¬ p4401))
    (h106315 : p4401 ∨ p2829)
    : (¬ p2707) ∨ p2829 ∨ (¬ p3309) ∨ p2274 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4401) := (Or.elim h106604 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => r4))))))))));
    (Or.elim h106315 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step107378 (p2373 p2440 p2510 p2531 p3016 p3156 p3422 : Prop)
    (h77712 : (¬ p2510) ∨ p3156 ∨ (¬ p2531) ∨ (¬ p2440) ∨ p3016 ∨ (¬ p2373) ∨ (¬ p3422))
    (h101940 : p2531 ∨ (¬ p2373))
    : (¬ p3422) ∨ p3156 ∨ (¬ p2440) ∨ p3016 ∨ (¬ p2373) ∨ (¬ p2510) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2531) := (Or.elim h77712 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u0))))))))))))));
    (Or.elim h101940 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107381 (p3093 p3379 p3590 p3641 p3922 p3984 p4595 : Prop)
    (h79857 : (¬ p3922) ∨ p3379 ∨ (¬ p3590) ∨ (¬ p4595) ∨ p3641 ∨ (¬ p3984) ∨ (¬ p3093))
    (h106295 : p4595 ∨ p3641)
    : (¬ p3984) ∨ p3641 ∨ (¬ p3590) ∨ (¬ p3922) ∨ p3379 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3984 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4595) := (Or.elim h79857 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h106295 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step107382 (p2230 p2406 p2655 p2829 p3361 p3541 p4842 : Prop)
    (h81745 : p2829 ∨ (¬ p3541) ∨ p2230 ∨ (¬ p4842) ∨ (¬ p2406) ∨ (¬ p3361) ∨ (¬ p2655))
    (h106067 : p4842 ∨ p2829)
    : (¬ p2655) ∨ (¬ p2406) ∨ (¬ p3361) ∨ p2230 ∨ (¬ p3541) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2655 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4842) := (Or.elim h81745 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u0))))))))))))));
    (Or.elim h106067 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step107390 (p2156 p2187 p2241 p3506 p3842 p5123 p5580 : Prop)
    (h84949 : (¬ p5580) ∨ (¬ p3842) ∨ (¬ p5123) ∨ (¬ p2241) ∨ p2187 ∨ p2156 ∨ (¬ p3506))
    (h106200 : p5123 ∨ (¬ p2241))
    : (¬ p5580) ∨ (¬ p3506) ∨ (¬ p2241) ∨ p2187 ∨ p2156 ∨ (¬ p3842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5123) := (Or.elim h84949 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h106200 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107395 (p2241 p2630 p2748 p3399 p4319 p4452 p4972 : Prop)
    (h87110 : (¬ p4319) ∨ p3399 ∨ (¬ p2241) ∨ (¬ p2630) ∨ (¬ p4452) ∨ (¬ p4972) ∨ (¬ p2748))
    (h105837 : p4972 ∨ (¬ p2630))
    : (¬ p4319) ∨ (¬ p2748) ∨ (¬ p2241) ∨ (¬ p2630) ∨ (¬ p4452) ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4972) := (Or.elim h87110 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h105837 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107398 (p2797 p2870 p2957 p3051 p4313 p4700 p4972 : Prop)
    (h87193 : p2797 ∨ (¬ p2957) ∨ (¬ p4313) ∨ (¬ p4972) ∨ (¬ p2870) ∨ (¬ p4700) ∨ p3051)
    (h105902 : p4972 ∨ p3051)
    : (¬ p4313) ∨ p2797 ∨ (¬ p2957) ∨ (¬ p2870) ∨ (¬ p4700) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4972) := (Or.elim h87193 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (u5 r5))))))))))))));
    (Or.elim h105902 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step107400 (p2331 p2341 p2926 p3487 p3527 p4104 p4972 : Prop)
    (h87694 : p2331 ∨ (¬ p2341) ∨ (¬ p4104) ∨ p3527 ∨ (¬ p3487) ∨ (¬ p4972) ∨ (¬ p2926))
    (h105971 : p4972 ∨ (¬ p2341))
    : (¬ p4104) ∨ p3527 ∨ (¬ p2926) ∨ (¬ p2341) ∨ p2331 ∨ (¬ p3487) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2926 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4972) := (Or.elim h87694 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u2))))))))))))));
    (Or.elim h105971 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107406 (p2241 p2881 p3051 p3506 p3842 p5123 p5558 : Prop)
    (h89436 : (¬ p5558) ∨ (¬ p3842) ∨ (¬ p3506) ∨ (¬ p5123) ∨ (¬ p2241) ∨ p3051 ∨ p2881)
    (h106200 : p5123 ∨ (¬ p2241))
    : (¬ p3506) ∨ (¬ p5558) ∨ p2881 ∨ (¬ p2241) ∨ (¬ p3842) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5123) := (Or.elim h89436 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (False.elim (u2 r5))))))))))))));
    (Or.elim h106200 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107414 (p2220 p2241 p2641 p3146 p3266 p4228 p5250 : Prop)
    (h92521 : (¬ p4228) ∨ p3266 ∨ (¬ p5250) ∨ p2220 ∨ (¬ p2241) ∨ (¬ p2641) ∨ p3146)
    (h106520 : p5250 ∨ p3266)
    : (¬ p4228) ∨ p2220 ∨ p3146 ∨ p3266 ∨ (¬ p2241) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5250) := (Or.elim h92521 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (u2 r5))))))))))))));
    (Or.elim h106520 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step107416 (p2319 p2727 p3031 p3516 p3567 p3631 p4972 : Prop)
    (h93448 : p3631 ∨ (¬ p3567) ∨ (¬ p3516) ∨ (¬ p2727) ∨ (¬ p3031) ∨ (¬ p4972) ∨ (¬ p2319))
    (h105964 : p4972 ∨ (¬ p3516))
    : p3631 ∨ (¬ p3031) ∨ (¬ p3516) ∨ (¬ p3567) ∨ (¬ p2727) ∨ (¬ p2319) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4972) := (Or.elim h93448 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h105964 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107419 (p2088 p2630 p3567 p3609 p4114 p4364 p4972 : Prop)
    (h93811 : p3609 ∨ (¬ p4114) ∨ (¬ p4972) ∨ (¬ p3567) ∨ (¬ p4364) ∨ (¬ p2630) ∨ (¬ p2088))
    (h105837 : p4972 ∨ (¬ p2630))
    : (¬ p4364) ∨ (¬ p3567) ∨ (¬ p2088) ∨ (¬ p4114) ∨ p3609 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4364 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4972) := (Or.elim h93811 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u2))))))))))))));
    (Or.elim h105837 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step107420 (p2641 p2662 p2891 p3051 p3904 p4365 p4972 : Prop)
    (h94555 : (¬ p4365) ∨ p2641 ∨ (¬ p3904) ∨ (¬ p2891) ∨ (¬ p4972) ∨ (¬ p2662) ∨ p3051)
    (h105902 : p4972 ∨ p3051)
    : (¬ p2891) ∨ p3051 ∨ p2641 ∨ (¬ p3904) ∨ (¬ p4365) ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4972) := (Or.elim h94555 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (u1 r5))))))))))))));
    (Or.elim h105902 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step107421 (p2156 p2192 p2662 p2996 p3904 p4365 p4650 : Prop)
    (h94557 : (¬ p2996) ∨ (¬ p4650) ∨ p2156 ∨ (¬ p3904) ∨ (¬ p2192) ∨ (¬ p2662) ∨ (¬ p4365))
    (h106244 : p4650 ∨ (¬ p2996))
    : (¬ p2996) ∨ p2156 ∨ (¬ p2192) ∨ (¬ p4365) ∨ (¬ p3904) ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4650) := (Or.elim h94557 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u3))))))))))))));
    (Or.elim h106244 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107422 (p2088 p2427 p3073 p3691 p4492 p4590 p4629 : Prop)
    (h94597 : p3073 ∨ (¬ p4590) ∨ (¬ p3691) ∨ (¬ p4629) ∨ (¬ p2427) ∨ (¬ p4492) ∨ (¬ p2088))
    (h106081 : p4629 ∨ (¬ p2427))
    : p3073 ∨ (¬ p3691) ∨ (¬ p4492) ∨ (¬ p4590) ∨ (¬ p2427) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4629) := (Or.elim h94597 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h106081 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107426 (p2427 p3571 p3670 p3707 p4885 p5031 p5357 : Prop)
    (h96648 : p3707 ∨ (¬ p3670) ∨ (¬ p5031) ∨ (¬ p5357) ∨ (¬ p4885) ∨ p2427 ∨ (¬ p3571))
    (h105997 : p4885 ∨ p2427)
    : (¬ p5357) ∨ (¬ p3571) ∨ (¬ p5031) ∨ (¬ p3670) ∨ p2427 ∨ p3707 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5357 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4885) := (Or.elim h96648 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h105997 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step107428 (p2166 p2220 p2641 p2662 p3904 p4365 p4972 : Prop)
    (h97653 : p2641 ∨ (¬ p4365) ∨ (¬ p4972) ∨ p2220 ∨ (¬ p3904) ∨ (¬ p2166) ∨ (¬ p2662))
    (h105927 : p4972 ∨ p2220)
    : (¬ p4365) ∨ (¬ p2166) ∨ p2641 ∨ p2220 ∨ (¬ p3904) ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4972) := (Or.elim h97653 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h105927 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step107431 (p2177 p2246 p2295 p2331 p2608 p2641 p2737 : Prop)
    (h102905 : p2246 ∨ p2641 ∨ (¬ p2177) ∨ (¬ p2608) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2295))
    (h103207 : p2641 ∨ (¬ p2246) ∨ (¬ p2331))
    : p2641 ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2246 := (Or.elim h102905 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u2))))))))))))));
    (Or.elim h103207 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (False.elim (r1 u3)))))))

theorem step107434 (p2630 p2651 p2727 p2829 p3589 p4117 p4842 : Prop)
    (h103071 : p2829 ∨ (¬ p3589) ∨ (¬ p4117) ∨ p2630 ∨ (¬ p4842) ∨ (¬ p2651) ∨ (¬ p2727))
    (h106067 : p4842 ∨ p2829)
    : p2829 ∨ p2630 ∨ (¬ p3589) ∨ (¬ p4117) ∨ (¬ p2651) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4842) := (Or.elim h103071 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h106067 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107436 (p2437 p2608 p2662 p2727 p2911 p3201 p3389 : Prop)
    (h103082 : (¬ p3201) ∨ p3389 ∨ p2727 ∨ (¬ p2662) ∨ p2437 ∨ (¬ p2608) ∨ (¬ p2911))
    (h98048 : (¬ p2437) ∨ p3389 ∨ (¬ p2662))
    : p2727 ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p3201) ∨ p3389 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2437 := (Or.elim h103082 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u2))))))))))))));
    (Or.elim h98048 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u5)))))))

theorem step107438 (p2166 p2177 p2192 p2210 p2274 p2608 p3073 : Prop)
    (h103243 : (¬ p2192) ∨ p2166 ∨ p2274 ∨ (¬ p2210) ∨ p2608 ∨ (¬ p3073) ∨ (¬ p2177))
    (h103078 : (¬ p3073) ∨ p2608 ∨ (¬ p2166) ∨ (¬ p2210))
    : (¬ p3073) ∨ (¬ p2210) ∨ p2608 ∨ (¬ p2192) ∨ p2274 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2166 := (Or.elim h103243 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h103078 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step107442 (p2264 p2341 p2630 p2717 p4117 p4357 p4650 : Prop)
    (h103369 : (¬ p2341) ∨ p2717 ∨ (¬ p2264) ∨ (¬ p2630) ∨ (¬ p4117) ∨ (¬ p4357) ∨ (¬ p4650))
    (h104070 : (¬ p2264) ∨ p2341)
    : (¬ p4117) ∨ p2717 ∨ (¬ p2630) ∨ (¬ p2264) ∨ (¬ p4357) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4117 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2341) := (Or.elim h103369 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h104070 (fun q0 => (False.elim (q0 u3))) (fun r0 => (False.elim (u6 r0)))))

theorem step107446 (p2264 p2437 p2630 p2685 p2737 p3425 p4777 : Prop)
    (h103731 : p2737 ∨ p2630 ∨ p2264 ∨ p2685 ∨ (¬ p3425) ∨ p2437 ∨ (¬ p4777))
    (h102557 : p4777 ∨ p2685)
    : p2737 ∨ p2630 ∨ p2264 ∨ p2685 ∨ (¬ p3425) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4777) := (Or.elim h103731 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => r5))))))))))));
    (Or.elim h102557 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step107447 (p2241 p2437 p2440 p2630 p2727 p2829 p3475 : Prop)
    (h103905 : (¬ p2829) ∨ (¬ p2437) ∨ (¬ p2727) ∨ (¬ p2440) ∨ (¬ p2241) ∨ (¬ p2630) ∨ (¬ p3475))
    (h96403 : p3475 ∨ (¬ p2630))
    : (¬ p2241) ∨ (¬ p2437) ∨ (¬ p2829) ∨ (¬ p2630) ∨ (¬ p2440) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3475) := (Or.elim h103905 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => r5))))))))))));
    (Or.elim h96403 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107448 (p2241 p2449 p2608 p2727 p2761 p2992 p2996 : Prop)
    (h103927 : (¬ p2996) ∨ p2608 ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p2992) ∨ (¬ p2761) ∨ (¬ p2449))
    (h75635 : p2996 ∨ (¬ p2449) ∨ (¬ p2241) ∨ p2608)
    : (¬ p2761) ∨ (¬ p2241) ∨ p2608 ∨ (¬ p2727) ∨ (¬ p2992) ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2996) := (Or.elim h103927 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h75635 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step107449 (p2210 p2331 p2651 p3379 p3412 p4448 p4972 : Prop)
    (h104376 : p2210 ∨ p2331 ∨ (¬ p3379) ∨ (¬ p3412) ∨ (¬ p4448) ∨ (¬ p4972) ∨ (¬ p2651))
    (h105905 : p4972 ∨ p2210)
    : (¬ p3379) ∨ (¬ p2651) ∨ p2210 ∨ (¬ p3412) ∨ (¬ p4448) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3379 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4448 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4972) := (Or.elim h104376 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h105905 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step107456 (p2573 p2578 p2641 p2662 p2667 p3461 p3564 : Prop)
    (h105108 : p3461 ∨ p2641 ∨ (¬ p2578) ∨ (¬ p2667) ∨ p3564 ∨ (¬ p2662) ∨ p2573)
    (h78528 : p2578 ∨ p2573)
    : p3461 ∨ p2641 ∨ p2573 ∨ (¬ p2667) ∨ (¬ p2662) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2578) := (Or.elim h105108 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (u2 r5))))))))))))));
    (Or.elim h78528 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step107464 (p2220 p2459 p2608 p2737 p3005 p3146 p4041 p4521 : Prop)
    (h75734 : p2608 ∨ (¬ p3146) ∨ p3005 ∨ (¬ p2220) ∨ p2737 ∨ (¬ p4521) ∨ (¬ p4041) ∨ p2459)
    (h106488 : p4041 ∨ p2459)
    : p3005 ∨ p2737 ∨ p2459 ∨ (¬ p3146) ∨ (¬ p4521) ∨ (¬ p2220) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4041) := (Or.elim h75734 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (u2 r6))))))))))))))));
    (Or.elim h106488 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step107465 (p2230 p2373 p2608 p3347 p3707 p3830 p5123 p5568 : Prop)
    (h75736 : (¬ p5568) ∨ (¬ p3830) ∨ p2230 ∨ (¬ p5123) ∨ (¬ p3707) ∨ p2373 ∨ p2608 ∨ (¬ p3347))
    (h106199 : p5123 ∨ (¬ p3830))
    : (¬ p5568) ∨ (¬ p3707) ∨ p2230 ∨ p2608 ∨ p2373 ∨ (¬ p3830) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5123) := (Or.elim h75736 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h106199 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step107466 (p2352 p2573 p2608 p3347 p3707 p3830 p5123 p5580 : Prop)
    (h75754 : (¬ p5580) ∨ (¬ p3707) ∨ p2608 ∨ (¬ p3347) ∨ (¬ p5123) ∨ p2352 ∨ p2573 ∨ (¬ p3830))
    (h106199 : p5123 ∨ (¬ p3830))
    : (¬ p3707) ∨ (¬ p3830) ∨ (¬ p5580) ∨ (¬ p3347) ∨ p2352 ∨ p2608 ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5123) := (Or.elim h75754 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (False.elim (r6 u1))))))))))))))));
    (Or.elim h106199 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step107469 (p2230 p2373 p2608 p3146 p3347 p3399 p3631 p3950 : Prop)
    (h78972 : p2608 ∨ p3146 ∨ p2373 ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p3347) ∨ p2230)
    (h106489 : p3950 ∨ (¬ p3399))
    : p3146 ∨ p2373 ∨ p2608 ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3347) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3950) := (Or.elim h78972 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h106489 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107473 (p2187 p2241 p2352 p2383 p3379 p3449 p4514 p4756 : Prop)
    (h80648 : p3449 ∨ (¬ p2352) ∨ (¬ p4514) ∨ p2383 ∨ (¬ p2241) ∨ (¬ p2187) ∨ (¬ p4756) ∨ (¬ p3379))
    (h105543 : p4514 ∨ (¬ p2187))
    : p3449 ∨ (¬ p2187) ∨ (¬ p3379) ∨ (¬ p2352) ∨ p2383 ∨ (¬ p4756) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4756 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4514) := (Or.elim h80648 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u2))))))))))))))));
    (Or.elim h105543 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step107476 (p2139 p2528 p2598 p2901 p3051 p3115 p3641 p4450 : Prop)
    (h81030 : (¬ p3115) ∨ p2901 ∨ p2528 ∨ (¬ p3051) ∨ p2598 ∨ (¬ p2139) ∨ (¬ p4450) ∨ p3641)
    (h106564 : p4450 ∨ (¬ p3115))
    : (¬ p3115) ∨ p3641 ∨ p2901 ∨ (¬ p3051) ∨ p2598 ∨ (¬ p2139) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4450) := (Or.elim h81030 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (u1 r6))))))))))))))));
    (Or.elim h106564 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107479 (p2139 p2220 p2459 p2630 p2696 p3083 p3146 p4438 : Prop)
    (h82613 : (¬ p2220) ∨ p3083 ∨ p2696 ∨ (¬ p4438) ∨ (¬ p2139) ∨ (¬ p3146) ∨ p2459 ∨ p2630)
    (h106132 : p4438 ∨ (¬ p3146))
    : p2696 ∨ (¬ p3146) ∨ p3083 ∨ (¬ p2220) ∨ (¬ p2139) ∨ p2630 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4438) := (Or.elim h82613 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (False.elim (u5 r6))))))))))))))));
    (Or.elim h106132 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step107481 (p2139 p2156 p2177 p2274 p2630 p2696 p3083 p4438 : Prop)
    (h82703 : (¬ p2274) ∨ (¬ p2177) ∨ (¬ p2156) ∨ p3083 ∨ (¬ p4438) ∨ p2630 ∨ p2696 ∨ (¬ p2139))
    (h106125 : p4438 ∨ (¬ p2274))
    : p2630 ∨ p2696 ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2177) ∨ p3083 ∨ (¬ p2139) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4438) := (Or.elim h82703 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h106125 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107483 (p2132 p2352 p2573 p3105 p3979 p4322 p4419 p5119 : Prop)
    (h84565 : (¬ p3979) ∨ (¬ p4322) ∨ (¬ p2352) ∨ p3105 ∨ p2132 ∨ (¬ p4419) ∨ (¬ p5119) ∨ (¬ p2573))
    (h106362 : p5119 ∨ (¬ p2573))
    : (¬ p4322) ∨ (¬ p3979) ∨ (¬ p2352) ∨ p3105 ∨ p2132 ∨ (¬ p4419) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5119) := (Or.elim h84565 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h106362 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u6)))))

theorem step107484 (p2241 p2363 p2383 p2992 p3156 p3609 p4746 p5021 : Prop)
    (h85895 : (¬ p2992) ∨ (¬ p3609) ∨ p2383 ∨ (¬ p2241) ∨ (¬ p3156) ∨ (¬ p4746) ∨ p2363 ∨ (¬ p5021))
    (h105809 : p5021 ∨ (¬ p2992))
    : (¬ p3609) ∨ p2363 ∨ p2383 ∨ (¬ p3156) ∨ (¬ p2992) ∨ (¬ p4746) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5021) := (Or.elim h85895 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => r6))))))))))))));
    (Or.elim h105809 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107487 (p2230 p2363 p2774 p2819 p2982 p3367 p3759 p4450 : Prop)
    (h86326 : p2363 ∨ (¬ p4450) ∨ p2774 ∨ p2819 ∨ (¬ p2982) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p2230))
    (h106472 : p4450 ∨ (¬ p2982))
    : p2819 ∨ (¬ p3367) ∨ p2774 ∨ p2363 ∨ (¬ p3759) ∨ (¬ p2982) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4450) := (Or.elim h86326 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h106472 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step107491 (p2139 p2156 p2459 p2563 p2717 p2982 p3425 p4450 : Prop)
    (h88654 : (¬ p2982) ∨ (¬ p2156) ∨ p2459 ∨ p2717 ∨ p2563 ∨ (¬ p4450) ∨ (¬ p3425) ∨ (¬ p2139))
    (h106467 : p4450 ∨ (¬ p2156))
    : (¬ p2982) ∨ (¬ p2156) ∨ (¬ p3425) ∨ p2717 ∨ p2459 ∨ p2563 ∨ (¬ p2139) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4450) := (Or.elim h88654 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h106467 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step107492 (p2210 p2352 p2363 p2573 p2608 p2972 p3347 p4450 : Prop)
    (h88912 : p2363 ∨ p2608 ∨ (¬ p2210) ∨ (¬ p4450) ∨ p2573 ∨ (¬ p3347) ∨ (¬ p2972) ∨ p2352)
    (h106470 : p4450 ∨ (¬ p2972))
    : (¬ p2972) ∨ p2363 ∨ (¬ p2210) ∨ p2573 ∨ p2608 ∨ (¬ p3347) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4450) := (Or.elim h88912 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h106470 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107493 (p2608 p3266 p3276 p3346 p3347 p3399 p3631 p3950 : Prop)
    (h88914 : p3276 ∨ (¬ p3266) ∨ (¬ p3347) ∨ (¬ p3950) ∨ (¬ p3631) ∨ (¬ p3399) ∨ (¬ p3346) ∨ p2608)
    (h106489 : p3950 ∨ (¬ p3399))
    : (¬ p3266) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3346) ∨ p3276 ∨ (¬ p3347) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3950) := (Or.elim h88914 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h106489 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step107494 (p2352 p2363 p2573 p2608 p3347 p3399 p3631 p3950 : Prop)
    (h89371 : (¬ p3631) ∨ p2363 ∨ p2573 ∨ (¬ p3347) ∨ p2608 ∨ (¬ p3399) ∨ (¬ p3950) ∨ p2352)
    (h106489 : p3950 ∨ (¬ p3399))
    : (¬ p3631) ∨ p2352 ∨ p2363 ∨ p2573 ∨ p2608 ∨ (¬ p3399) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2352) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3950) := (Or.elim h89371 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (u1 r6))))))))))))))));
    (Or.elim h106489 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step107495 (p2145 p2696 p2881 p3051 p3506 p3755 p5123 p5558 : Prop)
    (h89406 : (¬ p5558) ∨ (¬ p5123) ∨ (¬ p3755) ∨ (¬ p3506) ∨ (¬ p2145) ∨ p3051 ∨ (¬ p2696) ∨ p2881)
    (h106197 : p5123 ∨ (¬ p2696))
    : (¬ p5558) ∨ (¬ p3506) ∨ (¬ p2145) ∨ (¬ p2696) ∨ (¬ p3755) ∨ p3051 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5123) := (Or.elim h89406 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h106197 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107498 (p2177 p2307 p2406 p2459 p2982 p3379 p4450 p5021 : Prop)
    (h91081 : p2459 ∨ p2177 ∨ (¬ p3379) ∨ (¬ p2982) ∨ (¬ p2406) ∨ p2307 ∨ (¬ p5021) ∨ (¬ p4450))
    (h106472 : p4450 ∨ (¬ p2982))
    : (¬ p3379) ∨ (¬ p2406) ∨ (¬ p2982) ∨ p2307 ∨ p2177 ∨ p2459 ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3379 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4450) := (Or.elim h91081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => r6))))))))))))));
    (Or.elim h106472 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107499 (p2145 p2220 p2696 p2797 p3146 p3266 p4228 p5250 : Prop)
    (h92181 : (¬ p4228) ∨ p3266 ∨ p2220 ∨ (¬ p2145) ∨ (¬ p2797) ∨ (¬ p5250) ∨ p3146 ∨ (¬ p2696))
    (h106520 : p5250 ∨ p3266)
    : (¬ p4228) ∨ (¬ p2145) ∨ (¬ p2696) ∨ p3146 ∨ p3266 ∨ p2220 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5250) := (Or.elim h92181 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (False.elim (r6 u2))))))))))))))));
    (Or.elim h106520 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step107500 (p2210 p2608 p2972 p3266 p3276 p3346 p3347 p4450 : Prop)
    (h92429 : p3276 ∨ p2608 ∨ (¬ p4450) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p2972) ∨ (¬ p2210) ∨ (¬ p3347))
    (h106470 : p4450 ∨ (¬ p2972))
    : p3276 ∨ (¬ p3266) ∨ p2608 ∨ (¬ p3346) ∨ (¬ p2972) ∨ (¬ p2210) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4450) := (Or.elim h92429 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h106470 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107501 (p2156 p2274 p2396 p2509 p2528 p3379 p3950 p4521 : Prop)
    (h93936 : (¬ p2396) ∨ (¬ p2274) ∨ p2528 ∨ (¬ p2509) ∨ (¬ p2156) ∨ (¬ p4521) ∨ p3379 ∨ (¬ p3950))
    (h106098 : p4521 ∨ (¬ p2509))
    : (¬ p2396) ∨ (¬ p2509) ∨ (¬ p3950) ∨ p2528 ∨ (¬ p2274) ∨ (¬ p2156) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4521) := (Or.elim h93936 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (False.elim (r6 u2))))))))))))))));
    (Or.elim h106098 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step107503 (p2156 p2177 p2241 p2274 p2727 p3083 p4438 p4521 : Prop)
    (h93938 : (¬ p2274) ∨ p2241 ∨ p3083 ∨ (¬ p4521) ∨ (¬ p4438) ∨ (¬ p2177) ∨ p2727 ∨ (¬ p2156))
    (h106125 : p4438 ∨ (¬ p2274))
    : p3083 ∨ p2727 ∨ p2241 ∨ (¬ p4521) ∨ (¬ p2274) ∨ (¬ p2177) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4438) := (Or.elim h93938 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h106125 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107504 (p2493 p2761 p3051 p3246 p3379 p4521 p5254 p5514 : Prop)
    (h94707 : (¬ p5514) ∨ (¬ p3051) ∨ (¬ p4521) ∨ (¬ p5254) ∨ (¬ p2761) ∨ p2493 ∨ (¬ p3246) ∨ p3379)
    (h106096 : p4521 ∨ p2493)
    : (¬ p5514) ∨ (¬ p5254) ∨ (¬ p3246) ∨ (¬ p2761) ∨ p2493 ∨ (¬ p3051) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5514 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4521) := (Or.elim h94707 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h106096 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step107507 (p2156 p2563 p2608 p2982 p3537 p3609 p4450 p4521 : Prop)
    (h97163 : (¬ p2982) ∨ p3609 ∨ (¬ p4521) ∨ p2563 ∨ p2608 ∨ (¬ p4450) ∨ p3537 ∨ (¬ p2156))
    (h106467 : p4450 ∨ (¬ p2156))
    : (¬ p2982) ∨ p3609 ∨ (¬ p4521) ∨ p2563 ∨ p2608 ∨ p3537 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4450) := (Or.elim h97163 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h106467 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u6)))))

theorem step107509 (p2210 p2459 p2608 p2911 p2972 p3347 p3389 p4450 : Prop)
    (h97717 : p2911 ∨ p2608 ∨ (¬ p2972) ∨ (¬ p4450) ∨ p3389 ∨ (¬ p2210) ∨ (¬ p3347) ∨ p2459)
    (h106470 : p4450 ∨ (¬ p2972))
    : (¬ p2972) ∨ p3389 ∨ p2911 ∨ p2608 ∨ p2459 ∨ (¬ p2210) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4450) := (Or.elim h97717 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u4 r6))))))))))))))));
    (Or.elim h106470 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107514 (p2241 p2363 p2383 p2992 p3266 p4272 p5021 p5400 : Prop)
    (h98385 : (¬ p4272) ∨ (¬ p5400) ∨ p2363 ∨ p3266 ∨ (¬ p2241) ∨ p2383 ∨ (¬ p2992) ∨ (¬ p5021))
    (h105809 : p5021 ∨ (¬ p2992))
    : (¬ p4272) ∨ (¬ p5400) ∨ p3266 ∨ (¬ p2241) ∨ p2363 ∨ p2383 ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4272 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5021) := (Or.elim h98385 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => r6))))))))))))));
    (Or.elim h105809 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u6)))))

theorem step107516 (p2241 p2992 p3115 p3266 p3461 p3654 p4450 p5021 : Prop)
    (h99576 : p3461 ∨ (¬ p3266) ∨ (¬ p3115) ∨ (¬ p2992) ∨ p3654 ∨ (¬ p2241) ∨ (¬ p4450) ∨ (¬ p5021))
    (h105809 : p5021 ∨ (¬ p2992))
    : p3461 ∨ (¬ p3266) ∨ (¬ p4450) ∨ (¬ p2992) ∨ p3654 ∨ (¬ p2241) ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5021) := (Or.elim h99576 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => r6))))))))))))));
    (Or.elim h105809 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107519 (p2241 p2307 p2396 p2761 p2992 p4272 p5021 p5400 : Prop)
    (h100956 : (¬ p4272) ∨ p2761 ∨ (¬ p5021) ∨ p2396 ∨ (¬ p2992) ∨ (¬ p5400) ∨ (¬ p2241) ∨ p2307)
    (h105809 : p5021 ∨ (¬ p2992))
    : (¬ p4272) ∨ (¬ p5400) ∨ (¬ p2241) ∨ (¬ p2992) ∨ p2396 ∨ p2761 ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4272 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5021) := (Or.elim h100956 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u6 r6))))))))))))))));
    (Or.elim h105809 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107523 (p2264 p2437 p2440 p2459 p2659 p3389 p3575 p5197 : Prop)
    (h103128 : (¬ p2440) ∨ (¬ p5197) ∨ p3389 ∨ (¬ p3575) ∨ (¬ p2459) ∨ (¬ p2437) ∨ (¬ p2264) ∨ (¬ p2659))
    (h102519 : p5197 ∨ p3389)
    : (¬ p2264) ∨ (¬ p2459) ∨ (¬ p3575) ∨ p3389 ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2659) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5197) := (Or.elim h103128 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u6))))))))))))))));
    (Or.elim h102519 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step107533 (p2132 p2352 p2528 p2598 p2630 p2727 p3422 p3573 : Prop)
    (h104599 : p2132 ∨ (¬ p2727) ∨ p2352 ∨ p2528 ∨ (¬ p3573) ∨ (¬ p2598) ∨ p2630 ∨ p3422)
    (h77694 : p2132 ∨ (¬ p3422) ∨ (¬ p2598))
    : p2132 ∨ (¬ p2598) ∨ p2630 ∨ p2352 ∨ (¬ p3573) ∨ (¬ p2727) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3422 := (Or.elim h104599 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => r6))))))))))))));
    (Or.elim h77694 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (False.elim (r1 u1)))))))

theorem step107539 (p2253 p2363 p2383 p2651 p2727 p3189 p3609 p4969 p5021 : Prop)
    (h75030 : p2727 ∨ p2363 ∨ (¬ p2253) ∨ (¬ p3609) ∨ (¬ p3189) ∨ p2383 ∨ (¬ p2651) ∨ (¬ p4969) ∨ (¬ p5021))
    (h105806 : p5021 ∨ (¬ p2651))
    : (¬ p3189) ∨ p2727 ∨ (¬ p2253) ∨ p2363 ∨ (¬ p3609) ∨ p2383 ∨ (¬ p2651) ∨ (¬ p4969) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5021) := (Or.elim h75030 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => r7))))))))))))))));
    (Or.elim h105806 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u6)))))

theorem step107543 (p2139 p2156 p2274 p2396 p2528 p2651 p3083 p3950 p4236 : Prop)
    (h78276 : p2528 ∨ (¬ p2396) ∨ (¬ p4236) ∨ p3083 ∨ (¬ p2274) ∨ p2651 ∨ (¬ p2139) ∨ (¬ p3950) ∨ (¬ p2156))
    (h106539 : p2139 ∨ (¬ p4236))
    : (¬ p2156) ∨ (¬ p4236) ∨ (¬ p3950) ∨ p2528 ∨ (¬ p2274) ∨ p3083 ∨ p2651 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2139) := (Or.elim h78276 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u0))))))))))))))))));
    (Or.elim h106539 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step107544 (p2307 p2363 p2459 p2608 p3325 p3367 p3641 p4438 p5017 : Prop)
    (h78342 : (¬ p2307) ∨ (¬ p5017) ∨ p3367 ∨ p2459 ∨ (¬ p3325) ∨ (¬ p2363) ∨ p3641 ∨ (¬ p4438) ∨ p2608)
    (h106121 : p4438 ∨ (¬ p2363))
    : p3367 ∨ p2608 ∨ p3641 ∨ p2459 ∨ (¬ p5017) ∨ (¬ p2363) ∨ (¬ p2307) ∨ (¬ p3325) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3367) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4438) := (Or.elim h78342 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (u1 r7))))))))))))))))));
    (Or.elim h106121 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step107546 (p2156 p2177 p2274 p2528 p3073 p3379 p3453 p4438 p4521 : Prop)
    (h79827 : p3073 ∨ (¬ p2274) ∨ (¬ p4438) ∨ p3379 ∨ (¬ p3453) ∨ (¬ p2528) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p4521))
    (h106114 : p4438 ∨ (¬ p2528))
    : p3073 ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2528) ∨ (¬ p3453) ∨ p3379 ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4438) := (Or.elim h79827 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h106114 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107547 (p2192 p2230 p2493 p2573 p2860 p2891 p3051 p3369 p4885 : Prop)
    (h79973 : (¬ p2891) ∨ (¬ p2860) ∨ (¬ p4885) ∨ (¬ p3369) ∨ p2192 ∨ (¬ p2493) ∨ p3051 ∨ p2573 ∨ (¬ p2230))
    (h106011 : p4885 ∨ (¬ p2493))
    : (¬ p2493) ∨ (¬ p2860) ∨ (¬ p3369) ∨ p2192 ∨ (¬ p2891) ∨ p3051 ∨ p2573 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4885) := (Or.elim h79973 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h106011 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107549 (p2246 p2440 p2651 p2982 p3073 p3093 p3449 p4450 p4760 : Prop)
    (h80607 : (¬ p2246) ∨ (¬ p2982) ∨ (¬ p3093) ∨ (¬ p4450) ∨ p2440 ∨ p3073 ∨ p3449 ∨ (¬ p4760) ∨ (¬ p2651))
    (h106472 : p4450 ∨ (¬ p2982))
    : (¬ p2246) ∨ p2440 ∨ (¬ p3093) ∨ (¬ p2982) ∨ p3073 ∨ p3449 ∨ (¬ p4760) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4760 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4450) := (Or.elim h80607 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h106472 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107550 (p2331 p2493 p2553 p2598 p2737 p3323 p3361 p3590 p4620 : Prop)
    (h81273 : (¬ p2553) ∨ p2331 ∨ (¬ p4620) ∨ (¬ p3590) ∨ p2737 ∨ (¬ p2598) ∨ p3323 ∨ (¬ p3361) ∨ (¬ p2493))
    (h106260 : p4620 ∨ p3323)
    : (¬ p3590) ∨ (¬ p2493) ∨ (¬ p2553) ∨ p2331 ∨ p2737 ∨ (¬ p2598) ∨ p3323 ∨ (¬ p3361) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3590 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4620) := (Or.elim h81273 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u1))))))))))))))))));
    (Or.elim h106260 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step107552 (p2241 p2383 p2449 p2996 p3266 p3322 p3461 p3950 p5021 : Prop)
    (h82127 : p3461 ∨ (¬ p3266) ∨ p2383 ∨ (¬ p2241) ∨ (¬ p3322) ∨ (¬ p3950) ∨ p2996 ∨ (¬ p2449) ∨ (¬ p5021))
    (h105811 : p5021 ∨ p2996)
    : p3461 ∨ (¬ p3266) ∨ (¬ p2449) ∨ (¬ p2241) ∨ p2383 ∨ (¬ p3950) ∨ (¬ p3322) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5021) := (Or.elim h82127 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => r7))))))))))))))));
    (Or.elim h105811 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u7 r0)))))

theorem step107555 (p2608 p3204 p3266 p3399 p3461 p3631 p3654 p3950 p4870 : Prop)
    (h82503 : p3461 ∨ (¬ p3266) ∨ (¬ p3631) ∨ (¬ p3399) ∨ p2608 ∨ (¬ p3950) ∨ (¬ p4870) ∨ p3654 ∨ (¬ p3204))
    (h106489 : p3950 ∨ (¬ p3399))
    : p3461 ∨ (¬ p3266) ∨ (¬ p3204) ∨ (¬ p3399) ∨ p2608 ∨ (¬ p4870) ∨ p3654 ∨ (¬ p3631) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p3950) := (Or.elim h82503 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (False.elim (r7 u2))))))))))))))))));
    (Or.elim h106489 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107556 (p2427 p2696 p2982 p3005 p3051 p3256 p4399 p4419 p4450 : Prop)
    (h82687 : (¬ p3051) ∨ p3256 ∨ (¬ p2982) ∨ p2696 ∨ (¬ p4419) ∨ (¬ p4399) ∨ p2427 ∨ (¬ p4450) ∨ p3005)
    (h106472 : p4450 ∨ (¬ p2982))
    : (¬ p4399) ∨ p2696 ∨ (¬ p3051) ∨ (¬ p4419) ∨ (¬ p2982) ∨ p3005 ∨ p3256 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4450) := (Or.elim h82687 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (u5 r7))))))))))))))))));
    (Or.elim h106472 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107559 (p2177 p2241 p2311 p2341 p2396 p2992 p3115 p4395 p5021 : Prop)
    (h87573 : p2341 ∨ p2396 ∨ (¬ p3115) ∨ (¬ p2177) ∨ (¬ p4395) ∨ (¬ p5021) ∨ (¬ p2992) ∨ (¬ p2241) ∨ (¬ p2311))
    (h105809 : p5021 ∨ (¬ p2992))
    : p2341 ∨ (¬ p2177) ∨ (¬ p4395) ∨ (¬ p2241) ∨ p2396 ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p2311) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5021) := (Or.elim h87573 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h105809 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step107561 (p2696 p2753 p2911 p3347 p3389 p3506 p3755 p5123 p5558 : Prop)
    (h88905 : (¬ p5558) ∨ (¬ p5123) ∨ (¬ p3755) ∨ p3389 ∨ (¬ p2753) ∨ (¬ p2696) ∨ (¬ p3347) ∨ p2911 ∨ (¬ p3506))
    (h106197 : p5123 ∨ (¬ p2696))
    : (¬ p3506) ∨ (¬ p5558) ∨ (¬ p3755) ∨ p3389 ∨ (¬ p2753) ∨ (¬ p2696) ∨ (¬ p3347) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5123) := (Or.elim h88905 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (False.elim (r7 u0))))))))))))))))));
    (Or.elim h106197 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step107563 (p2230 p2563 p2685 p2807 p3125 p3755 p4236 p4419 p5279 : Prop)
    (h89135 : p3755 ∨ p2807 ∨ (¬ p5279) ∨ (¬ p2563) ∨ (¬ p4419) ∨ (¬ p2230) ∨ (¬ p3125) ∨ (¬ p2685) ∨ (¬ p4236))
    (h106481 : p4419 ∨ (¬ p4236))
    : p3755 ∨ (¬ p3125) ∨ (¬ p5279) ∨ (¬ p2563) ∨ p2807 ∨ (¬ p2230) ∨ (¬ p2685) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4419) := (Or.elim h89135 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h106481 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u7)))))

theorem step107564 (p2139 p2651 p2761 p3051 p3083 p3246 p4149 p4236 p5123 : Prop)
    (h89961 : p4149 ∨ (¬ p2139) ∨ (¬ p3246) ∨ (¬ p3051) ∨ (¬ p4236) ∨ (¬ p2761) ∨ (¬ p5123) ∨ p3083 ∨ p2651)
    (h106539 : p2139 ∨ (¬ p4236))
    : (¬ p2761) ∨ p4149 ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4236) ∨ (¬ p5123) ∨ p3083 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4149) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2139) := (Or.elim h89961 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (False.elim (u7 r7))))))))))))))))));
    (Or.elim h106539 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107569 (p2132 p2440 p2839 p2850 p3016 p3201 p3362 p3363 p3698 : Prop)
    (h90633 : p2440 ∨ p3016 ∨ p2850 ∨ (¬ p3698) ∨ (¬ p2132) ∨ (¬ p3363) ∨ p2839 ∨ p3201 ∨ (¬ p3362))
    (h102190 : p3698 ∨ p2850)
    : p2850 ∨ p3016 ∨ p2440 ∨ (¬ p2132) ∨ (¬ p3363) ∨ p2839 ∨ p3201 ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p3698) := (Or.elim h90633 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h102190 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107570 (p2132 p2192 p2274 p2331 p2737 p3323 p3361 p4418 p4620 : Prop)
    (h90638 : (¬ p2274) ∨ (¬ p4620) ∨ (¬ p2132) ∨ p2737 ∨ (¬ p4418) ∨ p2331 ∨ p3323 ∨ (¬ p3361) ∨ (¬ p2192))
    (h106260 : p4620 ∨ p3323)
    : p3323 ∨ (¬ p2132) ∨ (¬ p3361) ∨ p2737 ∨ (¬ p2274) ∨ p2331 ∨ (¬ p4418) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4620) := (Or.elim h90638 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u0 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h106260 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107571 (p2088 p2102 p3073 p3425 p3918 p3985 p4313 p4317 p4782 : Prop)
    (h90812 : (¬ p4317) ∨ (¬ p3073) ∨ p3425 ∨ (¬ p3918) ∨ (¬ p3985) ∨ (¬ p2102) ∨ (¬ p4782) ∨ p2088 ∨ (¬ p4313))
    (h105524 : p4782 ∨ p3425)
    : (¬ p2102) ∨ (¬ p3985) ∨ (¬ p4313) ∨ (¬ p3918) ∨ (¬ p4317) ∨ (¬ p3073) ∨ p3425 ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2102 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4782) := (Or.elim h90812 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (False.elim (r7 u2))))))))))))))))));
    (Or.elim h105524 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step107572 (p2363 p2383 p2406 p2598 p2785 p2829 p2982 p3590 p4450 : Prop)
    (h90958 : p2363 ∨ (¬ p3590) ∨ (¬ p2785) ∨ (¬ p2982) ∨ (¬ p2406) ∨ p2829 ∨ p2383 ∨ (¬ p4450) ∨ (¬ p2598))
    (h106472 : p4450 ∨ (¬ p2982))
    : (¬ p2785) ∨ (¬ p2598) ∨ p2363 ∨ p2829 ∨ (¬ p2982) ∨ (¬ p3590) ∨ p2383 ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2785 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4450) := (Or.elim h90958 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u1))))))))))))))))));
    (Or.elim h106472 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107573 (p2383 p2406 p2982 p3266 p3322 p3379 p3461 p4450 p5021 : Prop)
    (h91097 : p3461 ∨ (¬ p3266) ∨ (¬ p2982) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p4450) ∨ (¬ p5021) ∨ (¬ p3322) ∨ p2383)
    (h106472 : p4450 ∨ (¬ p2982))
    : p3461 ∨ (¬ p3266) ∨ (¬ p2982) ∨ (¬ p2406) ∨ (¬ p3379) ∨ p2383 ∨ (¬ p5021) ∨ (¬ p3322) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4450) := (Or.elim h91097 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u5 r7))))))))))))))))));
    (Or.elim h106472 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107576 (p2396 p2553 p2573 p3266 p3286 p3950 p4236 p4419 p5284 : Prop)
    (h93255 : (¬ p5284) ∨ (¬ p3266) ∨ (¬ p3950) ∨ (¬ p2553) ∨ (¬ p2396) ∨ p3286 ∨ (¬ p4419) ∨ (¬ p4236) ∨ (¬ p2573))
    (h106481 : p4419 ∨ (¬ p4236))
    : (¬ p5284) ∨ (¬ p3266) ∨ (¬ p3950) ∨ (¬ p2553) ∨ p3286 ∨ (¬ p2396) ∨ (¬ p4236) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4419) := (Or.elim h93255 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h106481 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u6)))))

theorem step107577 (p2459 p2493 p2553 p2901 p3051 p3156 p3379 p4042 p4521 : Prop)
    (h93348 : p3379 ∨ (¬ p4521) ∨ (¬ p4042) ∨ (¬ p3156) ∨ p2901 ∨ p2493 ∨ (¬ p2459) ∨ (¬ p3051) ∨ p2553)
    (h106096 : p4521 ∨ p2493)
    : p2901 ∨ (¬ p3051) ∨ p3379 ∨ (¬ p3156) ∨ (¬ p4042) ∨ p2493 ∨ (¬ p2459) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4521) := (Or.elim h93348 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u0 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (u7 r7))))))))))))))))));
    (Or.elim h106096 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step107579 (p2139 p2331 p2373 p2427 p2797 p3005 p3051 p4043 p4236 : Prop)
    (h93850 : p3005 ∨ p2331 ∨ (¬ p4043) ∨ (¬ p2797) ∨ (¬ p2139) ∨ p2427 ∨ (¬ p2373) ∨ (¬ p4236) ∨ (¬ p3051))
    (h106539 : p2139 ∨ (¬ p4236))
    : p3005 ∨ (¬ p2373) ∨ (¬ p4043) ∨ (¬ p2797) ∨ p2331 ∨ p2427 ∨ (¬ p4236) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2139) := (Or.elim h93850 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h106539 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u6)))))

theorem step107581 (p2284 p2459 p2911 p3136 p3286 p3389 p3755 p4236 p4419 : Prop)
    (h95019 : (¬ p3389) ∨ p3136 ∨ (¬ p2911) ∨ (¬ p2459) ∨ (¬ p4236) ∨ (¬ p4419) ∨ p2284 ∨ (¬ p3755) ∨ p3286)
    (h106481 : p4419 ∨ (¬ p4236))
    : p3136 ∨ (¬ p3755) ∨ (¬ p3389) ∨ (¬ p2459) ∨ (¬ p4236) ∨ (¬ p2911) ∨ p2284 ∨ p3286 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4419) := (Or.elim h95019 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (u7 r7))))))))))))))))));
    (Or.elim h106481 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107582 (p2284 p2352 p2363 p2573 p3136 p3286 p3755 p4236 p4419 : Prop)
    (h95048 : (¬ p3755) ∨ p3136 ∨ p3286 ∨ (¬ p2363) ∨ (¬ p2352) ∨ p2284 ∨ (¬ p4236) ∨ (¬ p2573) ∨ (¬ p4419))
    (h106481 : p4419 ∨ (¬ p4236))
    : p3136 ∨ (¬ p3755) ∨ p3286 ∨ (¬ p2363) ∨ (¬ p2352) ∨ p2284 ∨ (¬ p4236) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4419) := (Or.elim h95048 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => r7))))))))))))))));
    (Or.elim h106481 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u6)))))

theorem step107583 (p2177 p2307 p2696 p2727 p2748 p2779 p2829 p3083 p4438 : Prop)
    (h95732 : (¬ p2748) ∨ p2696 ∨ (¬ p4438) ∨ p3083 ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2829) ∨ p2727 ∨ (¬ p2779))
    (h106126 : p4438 ∨ (¬ p2307))
    : (¬ p2779) ∨ (¬ p2829) ∨ p3083 ∨ (¬ p2748) ∨ (¬ p2307) ∨ p2696 ∨ (¬ p2177) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2779 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4438) := (Or.elim h95732 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (False.elim (r7 u0))))))))))))))))));
    (Or.elim h106126 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107584 (p2459 p2470 p2528 p2946 p3005 p3136 p4041 p4236 p4419 : Prop)
    (h96071 : p2946 ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p2470) ∨ (¬ p2528) ∨ p2459 ∨ p3005 ∨ (¬ p4041) ∨ (¬ p3136))
    (h106481 : p4419 ∨ (¬ p4236))
    : (¬ p2470) ∨ p2946 ∨ (¬ p4236) ∨ (¬ p2528) ∨ p2459 ∨ p3005 ∨ (¬ p4041) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4419) := (Or.elim h96071 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h106481 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107587 (p2177 p2210 p2307 p2459 p2608 p2972 p3204 p4450 p4870 : Prop)
    (h97443 : p2459 ∨ p2177 ∨ (¬ p3204) ∨ (¬ p2972) ∨ (¬ p2210) ∨ p2307 ∨ (¬ p4870) ∨ (¬ p4450) ∨ p2608)
    (h106470 : p4450 ∨ (¬ p2972))
    : (¬ p2210) ∨ (¬ p4870) ∨ p2177 ∨ (¬ p2972) ∨ p2608 ∨ p2307 ∨ (¬ p3204) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4450) := (Or.elim h97443 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (u4 r7))))))))))))))))));
    (Or.elim h106470 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107588 (p2139 p2156 p2177 p2274 p2630 p2651 p3005 p4041 p4236 : Prop)
    (h98135 : (¬ p2274) ∨ (¬ p2177) ∨ (¬ p4041) ∨ (¬ p2139) ∨ (¬ p4236) ∨ (¬ p2156) ∨ (¬ p2630) ∨ p2651 ∨ p3005)
    (h106539 : p2139 ∨ (¬ p4236))
    : (¬ p2630) ∨ (¬ p4041) ∨ (¬ p2177) ∨ p3005 ∨ (¬ p2156) ∨ (¬ p4236) ∨ (¬ p2274) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2139) := (Or.elim h98135 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (False.elim (u3 r7))))))))))))))))));
    (Or.elim h106539 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step107589 (p2156 p2177 p2245 p2274 p2528 p3166 p3256 p4438 p4521 : Prop)
    (h98204 : p3166 ∨ (¬ p2274) ∨ (¬ p2528) ∨ (¬ p2156) ∨ (¬ p4438) ∨ p3256 ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p4521))
    (h106125 : p4438 ∨ (¬ p2274))
    : p3166 ∨ (¬ p2177) ∨ (¬ p2528) ∨ (¬ p2274) ∨ (¬ p2156) ∨ p3256 ∨ (¬ p2245) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4438) := (Or.elim h98204 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h106125 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107591 (p2352 p2573 p2696 p2753 p3347 p3506 p3755 p5123 p5580 : Prop)
    (h99527 : (¬ p5580) ∨ (¬ p5123) ∨ (¬ p2696) ∨ (¬ p3755) ∨ (¬ p2753) ∨ p2573 ∨ (¬ p3506) ∨ (¬ p3347) ∨ p2352)
    (h106197 : p5123 ∨ (¬ p2696))
    : (¬ p3506) ∨ (¬ p5580) ∨ p2352 ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3755) ∨ (¬ p3347) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5123) := (Or.elim h99527 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u2 r7))))))))))))))))));
    (Or.elim h106197 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107594 (p2470 p2528 p2696 p2753 p2797 p3266 p3347 p4228 p5250 : Prop)
    (h100689 : (¬ p4228) ∨ (¬ p2753) ∨ p2470 ∨ p2528 ∨ (¬ p2797) ∨ (¬ p5250) ∨ p3266 ∨ (¬ p3347) ∨ (¬ p2696))
    (h106520 : p5250 ∨ p3266)
    : (¬ p4228) ∨ p2470 ∨ (¬ p3347) ∨ p2528 ∨ (¬ p2797) ∨ p3266 ∨ (¬ p2753) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5250) := (Or.elim h100689 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h106520 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step107595 (p2331 p2911 p3323 p3389 p3461 p3941 p4236 p4419 p5119 : Prop)
    (h101036 : (¬ p3941) ∨ p3461 ∨ (¬ p4236) ∨ (¬ p2911) ∨ p3323 ∨ (¬ p5119) ∨ (¬ p4419) ∨ p2331 ∨ (¬ p3389))
    (h106481 : p4419 ∨ (¬ p4236))
    : (¬ p3941) ∨ (¬ p3389) ∨ (¬ p4236) ∨ p3461 ∨ p3323 ∨ (¬ p5119) ∨ p2331 ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4419) := (Or.elim h101036 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (False.elim (r7 u1))))))))))))))))));
    (Or.elim h106481 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107596 (p2331 p2459 p2470 p2528 p2797 p3005 p4041 p4236 p4419 : Prop)
    (h101123 : p3005 ∨ (¬ p2470) ∨ p2331 ∨ p2459 ∨ (¬ p2797) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p4041) ∨ (¬ p2528))
    (h106481 : p4419 ∨ (¬ p4236))
    : (¬ p2470) ∨ (¬ p2797) ∨ p2331 ∨ p3005 ∨ p2459 ∨ (¬ p4236) ∨ (¬ p4041) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4419) := (Or.elim h101123 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h106481 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step107597 (p2177 p2459 p2598 p2753 p2850 p2982 p3309 p4450 p4870 : Prop)
    (h101351 : (¬ p2753) ∨ p3309 ∨ p2177 ∨ (¬ p4870) ∨ (¬ p2850) ∨ p2459 ∨ (¬ p4450) ∨ (¬ p2598) ∨ (¬ p2982))
    (h106472 : p4450 ∨ (¬ p2982))
    : (¬ p2850) ∨ (¬ p2598) ∨ p3309 ∨ p2177 ∨ (¬ p4870) ∨ p2459 ∨ (¬ p2753) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4450) := (Or.elim h101351 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h106472 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u7)))))

theorem step107598 (p2230 p2427 p3005 p3166 p3246 p3755 p4236 p4419 p4663 : Prop)
    (h101960 : (¬ p3246) ∨ p3755 ∨ (¬ p3005) ∨ (¬ p4236) ∨ (¬ p4663) ∨ (¬ p2230) ∨ (¬ p4419) ∨ (¬ p2427) ∨ p3166)
    (h106481 : p4419 ∨ (¬ p4236))
    : (¬ p4663) ∨ p3755 ∨ (¬ p3005) ∨ (¬ p4236) ∨ (¬ p3246) ∨ (¬ p2230) ∨ (¬ p2427) ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4663 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4419) := (Or.elim h101960 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u7 r7))))))))))))))))));
    (Or.elim h106481 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107601 (p2230 p2427 p3246 p3286 p3670 p4236 p4419 p5236 p5284 : Prop)
    (h102372 : (¬ p3670) ∨ (¬ p5284) ∨ p3286 ∨ (¬ p4236) ∨ (¬ p2427) ∨ (¬ p2230) ∨ (¬ p3246) ∨ (¬ p5236) ∨ (¬ p4419))
    (h106481 : p4419 ∨ (¬ p4236))
    : (¬ p5284) ∨ (¬ p3670) ∨ p3286 ∨ (¬ p4236) ∨ (¬ p2427) ∨ (¬ p2230) ∨ (¬ p3246) ∨ (¬ p5236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4419) := (Or.elim h102372 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => r7))))))))))))))));
    (Or.elim h106481 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107610 (p2440 p2459 p2532 p2533 p2563 p2651 p3146 p3256 p3266 : Prop)
    (h104692 : p3266 ∨ (¬ p3256) ∨ (¬ p2440) ∨ p2459 ∨ (¬ p3146) ∨ p2651 ∨ (¬ p2532) ∨ p2563 ∨ (¬ p2533))
    (h96311 : p2533 ∨ (¬ p3146))
    : (¬ p3256) ∨ p2563 ∨ (¬ p2440) ∨ (¬ p2532) ∨ p2651 ∨ (¬ p3146) ∨ p2459 ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2533) := (Or.elim h104692 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => r7))))))))))))))));
    (Or.elim h96311 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step107624 (p2156 p2187 p2241 p3506 p3645 p3830 p3853 p4959 p5123 p5580 : Prop)
    (h84923 : (¬ p5580) ∨ (¬ p3853) ∨ (¬ p3830) ∨ (¬ p3506) ∨ p2241 ∨ (¬ p5123) ∨ (¬ p3645) ∨ p2187 ∨ p2156 ∨ (¬ p4959))
    (h106199 : p5123 ∨ (¬ p3830))
    : (¬ p3506) ∨ (¬ p5580) ∨ (¬ p3645) ∨ (¬ p3853) ∨ p2241 ∨ (¬ p3830) ∨ p2187 ∨ p2156 ∨ (¬ p4959) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5123) := (Or.elim h84923 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h106199 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step107627 (p2598 p2753 p2850 p2982 p3204 p3266 p3461 p3654 p4450 p4870 : Prop)
    (h87725 : p3461 ∨ (¬ p3266) ∨ (¬ p2982) ∨ (¬ p4450) ∨ (¬ p3204) ∨ (¬ p2850) ∨ (¬ p4870) ∨ (¬ p2753) ∨ (¬ p2598) ∨ p3654)
    (h106472 : p4450 ∨ (¬ p2982))
    : p3461 ∨ (¬ p3266) ∨ (¬ p2982) ∨ p3654 ∨ (¬ p3204) ∨ (¬ p2850) ∨ (¬ p4870) ∨ (¬ p2753) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4450) := (Or.elim h87725 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (u3 r8))))))))))))))))))));
    (Or.elim h106472 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107633 (p2122 p2553 p2696 p2753 p2839 p3115 p3564 p4316 p4368 p4842 : Prop)
    (h90408 : (¬ p3564) ∨ p3115 ∨ (¬ p4316) ∨ (¬ p4368) ∨ (¬ p4842) ∨ p2839 ∨ (¬ p2122) ∨ (¬ p2753) ∨ p2553 ∨ (¬ p2696))
    (h106069 : p4842 ∨ p2839)
    : (¬ p4316) ∨ p3115 ∨ (¬ p2696) ∨ (¬ p4368) ∨ p2839 ∨ (¬ p2122) ∨ (¬ p3564) ∨ p2553 ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4316 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4842) := (Or.elim h90408 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (False.elim (r8 u2))))))))))))))))))));
    (Or.elim h106069 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step107637 (p2139 p2156 p2274 p2396 p2651 p3276 p4236 p4641 p5170 p5284 : Prop)
    (h93862 : (¬ p5284) ∨ (¬ p2396) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2139) ∨ (¬ p5170) ∨ (¬ p4236) ∨ (¬ p3276) ∨ p2651 ∨ (¬ p4641))
    (h106539 : p2139 ∨ (¬ p4236))
    : (¬ p5284) ∨ (¬ p3276) ∨ p2651 ∨ (¬ p2274) ∨ (¬ p5170) ∨ (¬ p2156) ∨ (¬ p4236) ∨ (¬ p2396) ∨ (¬ p4641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2139) := (Or.elim h93862 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u2 q8))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h106539 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u6)))))

theorem step107641 (p2573 p2630 p2807 p3461 p3564 p4236 p4253 p4391 p4419 p4781 : Prop)
    (h94445 : (¬ p4253) ∨ (¬ p4391) ∨ (¬ p4236) ∨ (¬ p4781) ∨ (¬ p3461) ∨ p2630 ∨ (¬ p3564) ∨ (¬ p2573) ∨ (¬ p4419) ∨ p2807)
    (h106481 : p4419 ∨ (¬ p4236))
    : (¬ p4391) ∨ (¬ p4253) ∨ (¬ p4236) ∨ (¬ p4781) ∨ (¬ p3461) ∨ p2630 ∨ (¬ p3564) ∨ (¬ p2573) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4391 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4419) := (Or.elim h94445 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (u8 r8))))))))))))))))))));
    (Or.elim h106481 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107647 (p2139 p2220 p2459 p2573 p3256 p3422 p3641 p3905 p4312 p4438 : Prop)
    (h95653 : (¬ p4312) ∨ p3641 ∨ p2573 ∨ (¬ p3905) ∨ (¬ p2139) ∨ p2459 ∨ (¬ p4438) ∨ (¬ p3256) ∨ (¬ p3422) ∨ (¬ p2220))
    (h106118 : p4438 ∨ (¬ p3256))
    : (¬ p3422) ∨ p3641 ∨ p2573 ∨ (¬ p4312) ∨ (¬ p2139) ∨ p2459 ∨ (¬ p3256) ∨ (¬ p3905) ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4438) := (Or.elim h95653 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h106118 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u6)))))

theorem step107648 (p2210 p2241 p2307 p2396 p2761 p3412 p4756 p5016 p5405 p5740 : Prop)
    (h96081 : (¬ p5740) ∨ (¬ p2761) ∨ p2210 ∨ (¬ p2396) ∨ (¬ p2241) ∨ (¬ p5016) ∨ (¬ p5405) ∨ (¬ p4756) ∨ (¬ p3412) ∨ (¬ p2307))
    (h106434 : p4756 ∨ (¬ p2241))
    : (¬ p5740) ∨ (¬ p3412) ∨ p2210 ∨ (¬ p2396) ∨ (¬ p2241) ∨ (¬ p5016) ∨ (¬ p2761) ∨ (¬ p5405) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5740 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4756) := (Or.elim h96081 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h106434 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107654 (p2139 p2630 p2651 p2761 p2962 p3461 p3654 p3755 p4236 p4663 : Prop)
    (h98139 : (¬ p4236) ∨ p2761 ∨ p3755 ∨ (¬ p3461) ∨ (¬ p2139) ∨ p2651 ∨ (¬ p4663) ∨ (¬ p2962) ∨ (¬ p2630) ∨ (¬ p3654))
    (h106539 : p2139 ∨ (¬ p4236))
    : (¬ p3461) ∨ p3755 ∨ p2761 ∨ (¬ p4236) ∨ p2651 ∨ (¬ p4663) ∨ (¬ p2962) ∨ (¬ p2630) ∨ (¬ p3654) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2139) := (Or.elim h98139 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h106539 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107658 (p2341 p2528 p2608 p2753 p2774 p3266 p3914 p4404 p5210 p5250 : Prop)
    (h101508 : (¬ p3914) ∨ p3266 ∨ (¬ p2774) ∨ (¬ p5210) ∨ p2341 ∨ (¬ p2608) ∨ (¬ p4404) ∨ p2528 ∨ (¬ p5250) ∨ (¬ p2753))
    (h106520 : p5250 ∨ p3266)
    : (¬ p3914) ∨ (¬ p5210) ∨ (¬ p2774) ∨ p2528 ∨ p2341 ∨ (¬ p2608) ∨ p3266 ∨ (¬ p4404) ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p5250) := (Or.elim h101508 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h106520 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step107663 (p2122 p2274 p2363 p2630 p2668 p2785 p2786 p4389 p4841 p4972 : Prop)
    (h103227 : (¬ p2668) ∨ (¬ p4841) ∨ (¬ p4389) ∨ p2122 ∨ (¬ p2786) ∨ (¬ p2274) ∨ (¬ p2785) ∨ (¬ p2630) ∨ (¬ p2363) ∨ (¬ p4972))
    (h105896 : p4972 ∨ (¬ p2274))
    : p2122 ∨ (¬ p2786) ∨ (¬ p2363) ∨ (¬ p2274) ∨ (¬ p2668) ∨ (¬ p2785) ∨ (¬ p4841) ∨ (¬ p4389) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4972) := (Or.elim h103227 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u0 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => r8))))))))))))))))));
    (Or.elim h105896 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107666 (p2352 p2406 p2440 p2553 p2922 p3389 p3564 p4079 p4620 p4710 : Prop)
    (h104200 : (¬ p2553) ∨ p3564 ∨ p2440 ∨ (¬ p2922) ∨ (¬ p4620) ∨ p2406 ∨ (¬ p3389) ∨ (¬ p4079) ∨ (¬ p2352) ∨ (¬ p4710))
    (h88716 : (¬ p2922) ∨ p3389 ∨ p2406 ∨ p2440)
    : (¬ p2352) ∨ p3564 ∨ p2406 ∨ p2440 ∨ (¬ p4620) ∨ (¬ p2922) ∨ (¬ p4079) ∨ (¬ p2553) ∨ (¬ p4710) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3389) := (Or.elim h104200 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h88716 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step107667 (p2210 p2341 p2427 p2608 p3369 p3370 p3379 p3389 p4108 p5206 : Prop)
    (h104289 : p2210 ∨ (¬ p4108) ∨ (¬ p2608) ∨ p3389 ∨ (¬ p5206) ∨ (¬ p3369) ∨ (¬ p3370) ∨ p3379 ∨ (¬ p2427) ∨ p2341)
    (h96465 : p3370 ∨ p2210)
    : (¬ p2608) ∨ p3379 ∨ p3389 ∨ p2210 ∨ (¬ p3369) ∨ (¬ p4108) ∨ p2341 ∨ (¬ p2427) ∨ (¬ p5206) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3370) := (Or.elim h104289 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (u6 r8))))))))))))))))))));
    (Or.elim h96465 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step107683 (p2139 p2156 p2685 p2807 p3096 p3276 p3461 p3755 p4236 p4422 p5279 : Prop)
    (h82449 : p3461 ∨ (¬ p3276) ∨ (¬ p3096) ∨ (¬ p2139) ∨ (¬ p4236) ∨ (¬ p5279) ∨ (¬ p2156) ∨ (¬ p2685) ∨ p2807 ∨ p3755 ∨ (¬ p4422))
    (h106539 : p2139 ∨ (¬ p4236))
    : (¬ p3276) ∨ p3755 ∨ (¬ p3096) ∨ (¬ p4236) ∨ (¬ p5279) ∨ (¬ p2156) ∨ (¬ p2685) ∨ p2807 ∨ p3461 ∨ (¬ p4422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2139) := (Or.elim h82449 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u1 q9))) (fun r9 => (False.elim (r9 u9))))))))))))))))))))));
    (Or.elim h106539 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107702 (p2187 p2192 p2210 p2363 p2651 p2727 p2911 p2946 p2992 p3370 p3579 : Prop)
    (h105220 : (¬ p2911) ∨ p2727 ∨ (¬ p3579) ∨ (¬ p2992) ∨ (¬ p2946) ∨ (¬ p3370) ∨ p2651 ∨ (¬ p2363) ∨ p2210 ∨ p2192 ∨ (¬ p2187))
    (h96465 : p3370 ∨ p2210)
    : (¬ p3579) ∨ (¬ p2992) ∨ (¬ p2911) ∨ p2727 ∨ (¬ p2946) ∨ p2651 ∨ (¬ p2363) ∨ p2210 ∨ p2192 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p3370) := (Or.elim h105220 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u8 q9))) (fun r9 => (False.elim (r9 u9))))))))))))))))))))));
    (Or.elim h96465 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u7 r0)))))

theorem step107703 (p2177 p2241 p2284 p2459 p2829 p3115 p3136 p3309 p3873 p4450 p4845 : Prop)
    (h106590 : p2177 ∨ p3309 ∨ (¬ p2829) ∨ (¬ p3115) ∨ p2459 ∨ (¬ p3136) ∨ (¬ p3873) ∨ p2241 ∨ (¬ p4450) ∨ (¬ p2284) ∨ (¬ p4845))
    (h106564 : p4450 ∨ (¬ p3115))
    : (¬ p2829) ∨ p3309 ∨ (¬ p4845) ∨ p2177 ∨ (¬ p3136) ∨ (¬ p3115) ∨ p2241 ∨ (¬ p3873) ∨ (¬ p2284) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4450) := (Or.elim h106590 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u9 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u2))))))))))))))))))))));
    (Or.elim h106564 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u5)))))

theorem step107723 (p2122 p2177 p2210 p2241 p2307 p2459 p2881 p2891 p2972 p3093 p3146 p4450 p4870 : Prop)
    (h106577 : p2177 ∨ (¬ p4870) ∨ p2459 ∨ p2122 ∨ (¬ p2972) ∨ p3146 ∨ p2307 ∨ p2881 ∨ p2241 ∨ (¬ p3093) ∨ (¬ p2210) ∨ (¬ p4450) ∨ (¬ p2891))
    (h106470 : p4450 ∨ (¬ p2972))
    : p3146 ∨ (¬ p2210) ∨ (¬ p4870) ∨ (¬ p2891) ∨ p2177 ∨ p2881 ∨ (¬ p3093) ∨ p2307 ∨ p2459 ∨ p2122 ∨ (¬ p2972) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p4450) := (Or.elim h106577 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u9 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u11 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u1))) (fun r10 => (Or.elim r10 (fun q11 => q11) (fun r11 => (False.elim (r11 u3))))))))))))))))))))))))));
    (Or.elim h106470 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u10)))))

theorem step107738 (p2437 p2440 p2504 p2505 p2584 p2651 p2727 p2797 p2996 p3019 p3379 p3579 p3819 p4117 p4782 : Prop)
    (h106579 : (¬ p2797) ∨ (¬ p3379) ∨ p2996 ∨ (¬ p2727) ∨ (¬ p3819) ∨ (¬ p4117) ∨ (¬ p2505) ∨ (¬ p2504) ∨ (¬ p2437) ∨ (¬ p2584) ∨ (¬ p3019) ∨ (¬ p2651) ∨ (¬ p3579) ∨ (¬ p2440) ∨ (¬ p4782))
    (h102554 : p3579 ∨ (¬ p2437))
    : (¬ p2504) ∨ (¬ p2584) ∨ (¬ p2505) ∨ (¬ p2727) ∨ (¬ p3379) ∨ (¬ p2797) ∨ (¬ p4117) ∨ p2996 ∨ (¬ p3819) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3019) ∨ (¬ p2440) ∨ (¬ p4782) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2504 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : (¬ p3579) := (Or.elim h106579 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (Or.elim r11 (fun q12 => q12) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u12))) (fun r13 => (False.elim (r13 u13))))))))))))))))))))))))))))));
    (Or.elim h102554 (fun q0 => (False.elim (u14 q0))) (fun r0 => (False.elim (r0 u9)))))

theorem step107742 (p2295 p2363 p2383 p2427 p2563 p2598 p2668 p2781 p2850 p2870 p3201 p3987 p4138 p5045 p5059 : Prop)
    (h107019 : p2668 ∨ (¬ p2870) ∨ (¬ p2427) ∨ p3201 ∨ p2850 ∨ (¬ p2383) ∨ (¬ p5045) ∨ (¬ p4138) ∨ (¬ p2295) ∨ (¬ p5059) ∨ p2563 ∨ (¬ p3987) ∨ (¬ p2781) ∨ p2598 ∨ (¬ p2363))
    (h81049 : (¬ p2870) ∨ p2427 ∨ p2850 ∨ p2598)
    : (¬ p4138) ∨ p2598 ∨ (¬ p2870) ∨ p2850 ∨ p2668 ∨ p3201 ∨ (¬ p2383) ∨ (¬ p5045) ∨ (¬ p2295) ∨ p2563 ∨ (¬ p3987) ∨ (¬ p2781) ∨ (¬ p5059) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : (¬ p2427) := (Or.elim h107019 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u9 q10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u11))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (u1 q13))) (fun r13 => (False.elim (r13 u13))))))))))))))))))))))))))))));
    (Or.elim h81049 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u14 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step107785 (p2598 p2630 p2696 p2727 p3362 p3363 p3364 : Prop)
    (h99643 : p3363 ∨ (¬ p2598))
    (h101922 : p3362 ∨ (¬ p2598))
    (h103023 : p2727 ∨ (¬ p2630) ∨ (¬ p2598))
    (h88126 : p3364 ∨ p2630)
    (h82871 : p2696 ∨ (¬ p3364) ∨ (¬ p3363) ∨ (¬ p3362))
    : (¬ p2598) ∨ p2727 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3363 := (Or.elim h99643 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u4 : p3362 := (Or.elim h101922 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u5 : (¬ p2630) := (Or.elim h103023 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u0))))));
    let u6 : p3364 := (Or.elim h88126 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h82871 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step107786 (p2264 p2284 p2881 p2901 p2995 p3699 p4558 : Prop)
    (h105400 : p4558)
    (h30100 : (¬ p2264) ∨ p2881 ∨ (¬ p3699))
    (h96350 : p3699 ∨ p2901)
    (h85984 : p2995 ∨ (¬ p2901))
    (h76197 : (¬ p2995) ∨ (¬ p2264) ∨ p2284 ∨ (¬ p4558) ∨ p2881)
    : p2284 ∨ (¬ p2264) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4558 := h105400;
    let u4 : (¬ p3699) := (Or.elim h30100 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    let u5 : p2901 := (Or.elim h96350 (fun q0 => (False.elim (u4 q0))) (fun r0 => r0));
    let u6 : p2995 := (Or.elim h85984 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h76197 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step107787 (p2210 p2241 p2727 p2992 p3412 p4365 : Prop)
    (h75453 : p2210 ∨ (¬ p3412) ∨ (¬ p2727) ∨ (¬ p2241))
    (h79864 : p3412 ∨ p2992)
    (h75456 : p2210 ∨ (¬ p2241) ∨ (¬ p4365))
    (h96340 : p4365 ∨ (¬ p2992))
    : p2210 ∨ (¬ p2727) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3412) := (Or.elim h75453 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    let u4 : p2992 := (Or.elim h79864 (fun q0 => (False.elim (u3 q0))) (fun r0 => r0));
    let u5 : (¬ p4365) := (Or.elim h75456 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96340 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u4)))))

theorem step107788 (p2192 p2210 p2241 p2284 p2641 p2992 p3093 p3957 p4336 p4759 p4957 : Prop)
    (h79172 : p4336 ∨ (¬ p2284))
    (h80422 : (¬ p2241) ∨ p3093 ∨ (¬ p4759))
    (h96022 : p4759 ∨ (¬ p2641))
    (h81807 : p2641 ∨ (¬ p2992) ∨ (¬ p4336))
    (h102402 : p4957 ∨ p2992)
    (h96469 : p3957 ∨ p2192)
    (h75477 : p2192 ∨ (¬ p2284) ∨ (¬ p2241) ∨ p2210)
    (h80383 : p3093 ∨ (¬ p2210) ∨ (¬ p2284) ∨ (¬ p4957) ∨ (¬ p3957))
    : p2192 ∨ p3093 ∨ (¬ p2284) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2192) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4336 := (Or.elim h79172 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u5 : (¬ p4759) := (Or.elim h80422 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    let u6 : (¬ p2641) := (Or.elim h96022 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    let u7 : (¬ p2992) := (Or.elim h81807 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u4))))));
    let u8 : p4957 := (Or.elim h102402 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u9 : p3957 := (Or.elim h96469 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2210 := (Or.elim h75477 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h80383 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u9)))))))))))

theorem step107789 (p2230 p2406 p2427 p2440 p2608 p2630 p2870 p2891 p2901 p3051 p3136 p3379 p3879 p3904 p3948 p4109 p4210 p4376 p4700 p4814 p5051 p5191 : Prop)
    (h106911 : (¬ p2230) ∨ (¬ p2440))
    (h96429 : p3948 ∨ (¬ p2406))
    (h106320 : p4376)
    (h96428 : p4210 ∨ (¬ p2406))
    (h91024 : (¬ p2608) ∨ (¬ p2406) ∨ (¬ p3948) ∨ (¬ p4376) ∨ (¬ p4210) ∨ p2230)
    (h91068 : p2608 ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p2440))
    (h91519 : p5191 ∨ p3379)
    (h102493 : p3904 ∨ p2230)
    (h105440 : p4814)
    (h100363 : p4700 ∨ (¬ p2440))
    (h91693 : p4109 ∨ p2230)
    (h100365 : p3879 ∨ (¬ p2440))
    (h104437 : (¬ p2406) ∨ p2630 ∨ (¬ p2440))
    (h83093 : (¬ p2406) ∨ p3136 ∨ (¬ p3879) ∨ (¬ p2630) ∨ (¬ p4814))
    (h96314 : p5051 ∨ (¬ p3136))
    (h26296 : p2870 ∨ (¬ p2901) ∨ (¬ p5051))
    (h83062 : (¬ p3051) ∨ p2901 ∨ (¬ p4109) ∨ (¬ p4700) ∨ (¬ p2406) ∨ (¬ p4814))
    (h91023 : (¬ p2427) ∨ (¬ p2406) ∨ (¬ p5191) ∨ (¬ p3904) ∨ p3051)
    (h91666 : (¬ p2891) ∨ (¬ p3948) ∨ p2427 ∨ (¬ p5191) ∨ p2230)
    : (¬ p2891) ∨ p2870 ∨ (¬ p2406) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2230) := (Or.elim h106911 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u5 : p3948 := (Or.elim h96429 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u6 : p4376 := h106320;
    let u7 : p4210 := (Or.elim h96428 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u8 : (¬ p2608) := (Or.elim h91024 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (u4 r4))))))))))));
    let u9 : (¬ p3379) := (Or.elim h91068 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    let u10 : p5191 := (Or.elim h91519 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u11 : p3904 := (Or.elim h102493 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4814 := h105440;
    let u13 : p4700 := (Or.elim h100363 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u14 : p4109 := (Or.elim h91693 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u15 : p3879 := (Or.elim h100365 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u16 : p2630 := (Or.elim h104437 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u3))))));
    let u17 : p3136 := (Or.elim h83093 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u16))) (fun r3 => (False.elim (r3 u12))))))))));
    let u18 : p5051 := (Or.elim h96314 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    let u19 : (¬ p2901) := (Or.elim h26296 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u18))))));
    let u20 : (¬ p3051) := (Or.elim h83062 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u19 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u12))))))))))));
    let u21 : (¬ p2427) := (Or.elim h91023 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (False.elim (u20 r3))))))))));
    (Or.elim h91666 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u21 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (False.elim (u4 r3)))))))))))

theorem step107790 (p2440 p2982 p3237 p3266 p3276 p3343 p3506 p4953 p5176 : Prop)
    (h91402 : (¬ p3343) ∨ (¬ p3237) ∨ (¬ p2440))
    (h96343 : p3237 ∨ p2982)
    (h102547 : p4953 ∨ (¬ p2982))
    (h102376 : p5176 ∨ (¬ p3343))
    (h100256 : p3266 ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p2440))
    (h93311 : p3276 ∨ (¬ p5176) ∨ (¬ p2440) ∨ (¬ p4953) ∨ (¬ p3506))
    : (¬ p3343) ∨ (¬ p3506) ∨ p3266 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3237) := (Or.elim h91402 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u3))))));
    let u5 : p2982 := (Or.elim h96343 (fun q0 => (False.elim (u4 q0))) (fun r0 => r0));
    let u6 : p4953 := (Or.elim h102547 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u7 : p5176 := (Or.elim h102376 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : (¬ p3276) := (Or.elim h100256 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h93311 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step107791 (p2230 p2427 p2440 p2630 p2651 p2655 p2662 p2850 p2870 p2901 p3051 p3136 p3413 p3698 p3904 p4241 p4316 : Prop)
    (h102493 : p3904 ∨ p2230)
    (h107337 : p2440 ∨ p3051 ∨ (¬ p2870) ∨ (¬ p3698) ∨ (¬ p3904))
    (h102190 : p3698 ∨ p2850)
    (h96414 : p3413 ∨ p2440)
    (h96413 : p4241 ∨ p2440)
    (h74520 : p2440 ∨ (¬ p2662) ∨ p2230)
    (h96928 : p2662 ∨ (¬ p2651))
    (h88056 : p2655 ∨ p2651)
    (h74528 : p2440 ∨ (¬ p2655) ∨ p2230 ∨ (¬ p2630))
    (h107142 : (¬ p4241) ∨ p2630 ∨ p2230 ∨ (¬ p3136))
    (h84419 : p4316 ∨ p3136)
    (h100652 : p2901 ∨ (¬ p4316) ∨ (¬ p2870))
    (h107205 : (¬ p3413) ∨ p2427 ∨ p2230 ∨ (¬ p2901))
    (h87771 : p3051 ∨ (¬ p2850) ∨ (¬ p3904) ∨ (¬ p2427))
    : (¬ p2870) ∨ p3051 ∨ p2440 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3904 := (Or.elim h102493 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u5 : (¬ p3698) := (Or.elim h107337 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    let u6 : p2850 := (Or.elim h102190 (fun q0 => (False.elim (u5 q0))) (fun r0 => r0));
    let u7 : p3413 := (Or.elim h96414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4241 := (Or.elim h96413 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : (¬ p2662) := (Or.elim h74520 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u3 r1))))));
    let u10 : (¬ p2651) := (Or.elim h96928 (fun q0 => (False.elim (u9 q0))) (fun r0 => r0));
    let u11 : p2655 := (Or.elim h88056 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u12 : (¬ p2630) := (Or.elim h74528 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => r2))))));
    let u13 : (¬ p3136) := (Or.elim h107142 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u12 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => r2))))));
    let u14 : p4316 := (Or.elim h84419 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u15 : p2901 := (Or.elim h100652 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (False.elim (r1 u0))))));
    let u16 : p2427 := (Or.elim h107205 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (r2 u15))))))));
    (Or.elim h87771 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u16)))))))))

theorem step107792 (p2230 p2274 p2563 p2598 p2850 p3367 p3759 : Prop)
    (h42743 : (¬ p2274) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (¬ p2850))
    (h95983 : p3759 ∨ p2598)
    (h104124 : (¬ p2850) ∨ (¬ p3367) ∨ p2230)
    (h45753 : (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3367) ∨ (¬ p3759))
    : (¬ p3367) ∨ (¬ p2850) ∨ (¬ p2274) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2598) := (Or.elim h42743 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    let u5 : p3759 := (Or.elim h95983 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u6 : p2230 := (Or.elim h104124 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => r1))));
    (Or.elim h45753 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step107793 (p1574 p1580 p3794 : Prop)
    (h5584 : (¬ p1580) ∨ p3794)
    (h5583 : (¬ p1574) ∨ p3794)
    (h1717 : p1574 ∨ p1580)
    : p3794 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3794) := (fun h => hn h);
    let u1 : (¬ p1580) := (Or.elim h5584 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u2 : (¬ p1574) := (Or.elim h5583 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h1717 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step107794 (p3794 p5482 p5483 : Prop)
    (h107793 : p3794)
    (h105505 : p5482)
    (h96544 : (¬ p5482) ∨ p5483 ∨ (¬ p3794))
    : p5483 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5483) := (fun h => hn h);
    let u1 : p3794 := h107793;
    let u2 : p5482 := h105505;
    (Or.elim h96544 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step107801 (p3670 p3707 p4027 p4028 p4029 : Prop)
    (h5996 : (¬ p3707) ∨ (¬ p4027) ∨ (¬ p4028) ∨ (¬ p4029))
    (h96219 : p4027 ∨ p3670)
    : p3670 ∨ (¬ p3707) ∨ (¬ p4028) ∨ (¬ p4029) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4028 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4029 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4027) := (Or.elim h5996 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h96219 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107804 (p2264 p2295 p2331 p2341 p4104 p4572 : Prop)
    (h96685 : (¬ p2341) ∨ p2331 ∨ (¬ p4104) ∨ p2264 ∨ (¬ p4572))
    (h96454 : p4572 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2341) ∨ (¬ p4104) ∨ p2331 ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4572) := (Or.elim h96685 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h96454 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107805 (p2122 p2230 p2307 p2331 p2655 p2819 p3146 p3256 p4134 p4346 p4580 p4607 : Prop)
    (h105379 : p4134)
    (h96683 : (¬ p2819) ∨ p3256 ∨ (¬ p4607) ∨ (¬ p3146) ∨ (¬ p4580) ∨ (¬ p2655) ∨ p2230 ∨ p2122 ∨ (¬ p4134) ∨ (¬ p4346) ∨ (¬ p2307))
    (h102694 : p4580 ∨ p2331)
    : p2331 ∨ (¬ p4607) ∨ (¬ p2819) ∨ (¬ p2307) ∨ (¬ p3146) ∨ p3256 ∨ p2122 ∨ (¬ p2655) ∨ p2230 ∨ (¬ p4346) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4134 := h105379;
    let u11 : (¬ p4580) := (Or.elim h96683 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u8 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u3))))))))))))))))))))));
    (Or.elim h102694 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107808 (p2608 p2619 p3093 p3537 p4243 p4512 p4741 : Prop)
    (h93009 : p3537 ∨ p2608 ∨ (¬ p3093) ∨ (¬ p4243) ∨ (¬ p4741) ∨ (¬ p4512))
    (h96151 : p4741 ∨ p2619)
    : p2619 ∨ (¬ p4512) ∨ (¬ p3093) ∨ p3537 ∨ (¬ p4243) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4741) := (Or.elim h93009 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h96151 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107809 (p2307 p2668 p3189 p3309 p3567 p4245 p4773 : Prop)
    (h83613 : (¬ p4773) ∨ (¬ p4245) ∨ (¬ p2307) ∨ (¬ p3189) ∨ p3309 ∨ (¬ p3567))
    (h96400 : p4773 ∨ (¬ p2668))
    : (¬ p2668) ∨ (¬ p3189) ∨ p3309 ∨ (¬ p2307) ∨ (¬ p4245) ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4773) := (Or.elim h83613 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96400 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107815 (p2098 p2132 p3105 p3146 p4188 p5056 : Prop)
    (h84482 : (¬ p2098) ∨ (¬ p4188) ∨ p2132 ∨ p3105 ∨ (¬ p5056))
    (h102664 : p5056 ∨ p3146)
    : p3146 ∨ (¬ p2098) ∨ p3105 ∨ (¬ p4188) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4188 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5056) := (Or.elim h84482 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => r3))))))));
    (Or.elim h102664 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107829 (p2088 p2098 p2112 p3537 p3599 p5339 : Prop)
    (h95184 : (¬ p5339) ∨ (¬ p2112) ∨ (¬ p3537) ∨ (¬ p2088) ∨ p3599)
    (h96990 : p2112 ∨ (¬ p2098))
    : (¬ p2098) ∨ (¬ p2088) ∨ (¬ p3537) ∨ p3599 ∨ (¬ p5339) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5339 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2112) := (Or.elim h95184 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96990 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107831 (p2307 p2493 p2500 p3309 p3379 : Prop)
    (h104194 : (¬ p3309) ∨ p2307 ∨ (¬ p3379) ∨ (¬ p2500))
    (h102393 : p2500 ∨ p2493)
    : p2493 ∨ (¬ p3309) ∨ p2307 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2500) := (Or.elim h104194 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h102393 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107832 (p2383 p2493 p2500 p3063 p3379 p5015 : Prop)
    (h83521 : (¬ p3063) ∨ p2383 ∨ (¬ p3379) ∨ (¬ p5015) ∨ (¬ p2500))
    (h102393 : p2500 ∨ p2493)
    : p2493 ∨ (¬ p3063) ∨ p2383 ∨ (¬ p3379) ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2500) := (Or.elim h83521 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h102393 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107833 (p2156 p2192 p2417 p2449 p2807 p2891 p2946 p2959 p4277 : Prop)
    (h105380 : p4277)
    (h86494 : p2417 ∨ (¬ p2449) ∨ p2891 ∨ (¬ p2192) ∨ p2156 ∨ (¬ p2959) ∨ (¬ p2807) ∨ (¬ p4277))
    (h96892 : p2959 ∨ (¬ p2946))
    : (¬ p2946) ∨ (¬ p2449) ∨ p2891 ∨ p2156 ∨ (¬ p2807) ∨ p2417 ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4277 := h105380;
    let u8 : (¬ p2959) := (Or.elim h86494 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h96892 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107835 (p2187 p2246 p2284 p2946 p2996 p3039 p3955 p4427 : Prop)
    (h41606 : (¬ p2187) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3039) ∨ (¬ p3955) ∨ (¬ p4427))
    (h96884 : p3039 ∨ p2996)
    : p2996 ∨ (¬ p4427) ∨ (¬ p2187) ∨ (¬ p3955) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3039) := (Or.elim h41606 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h96884 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107836 (p2651 p2727 p2996 p3039 p3266 p3286 p3461 p3631 p4450 p4623 p4952 p5175 : Prop)
    (h98169 : p3461 ∨ (¬ p3266) ∨ (¬ p4623) ∨ (¬ p5175) ∨ (¬ p4450) ∨ p3631 ∨ (¬ p4952) ∨ p2651 ∨ (¬ p2727) ∨ (¬ p3039) ∨ (¬ p3286))
    (h96884 : p3039 ∨ p2996)
    : p2996 ∨ (¬ p4623) ∨ (¬ p3266) ∨ p2651 ∨ (¬ p2727) ∨ p3461 ∨ (¬ p3286) ∨ p3631 ∨ (¬ p5175) ∨ (¬ p4952) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p3039) := (Or.elim h98169 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => q9) (fun r9 => (False.elim (r9 u6))))))))))))))))))))));
    (Or.elim h96884 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107841 (p3767 p3770 p3777 : Prop)
    (h66474 : p3777 ∨ p3770)
    (h95145 : p3767 ∨ (¬ p3777))
    : p3767 ∨ p3770 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3767) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3770) := (fun h => hn (Or.inr h));
    let u2 : p3777 := (Or.elim h66474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h95145 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step107842 (p3767 p3770 p3773 : Prop)
    (h96819 : p3773 ∨ (¬ p3770))
    (h107841 : p3767 ∨ p3770)
    : p3767 ∨ p3773 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3767) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3773) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3770) := (Or.elim h96819 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h107841 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step107844 (p3804 p3807 p3811 p5483 : Prop)
    (h107794 : p5483)
    (h96543 : (¬ p5483) ∨ p3804 ∨ p3811)
    (h96809 : p3807 ∨ (¬ p3804))
    : p3807 ∨ p3811 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3807) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3811) := (fun h => hn (Or.inr h));
    let u2 : p5483 := h107794;
    let u3 : p3804 := (Or.elim h96543 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h96809 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u3)))))

theorem step107845 (p3801 p3807 p3811 : Prop)
    (h96148 : p3801 ∨ (¬ p3811))
    (h107844 : p3807 ∨ p3811)
    : p3807 ∨ p3801 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3807) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3801) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3811) := (Or.elim h96148 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h107844 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step107848 (p2241 p3707 p3767 p3852 p3854 p4439 : Prop)
    (h96693 : p3707 ∨ (¬ p3767) ∨ (¬ p3854) ∨ (¬ p4439) ∨ p2241)
    (h96786 : p3854 ∨ (¬ p3852))
    : (¬ p3852) ∨ (¬ p4439) ∨ p3707 ∨ (¬ p3767) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3852 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4439 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3854) := (Or.elim h96693 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96786 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107850 (p3670 p3707 p4028 p4029 : Prop)
    (h107801 : p3670 ∨ (¬ p3707) ∨ (¬ p4028) ∨ (¬ p4029))
    (h96220 : p4028 ∨ p3670)
    : p3670 ∨ (¬ p3707) ∨ (¬ p4029) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4029 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4028) := (Or.elim h107801 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96220 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107856 (p2122 p2707 p2819 p3923 p3953 p4476 : Prop)
    (h50214 : (¬ p2707) ∨ (¬ p2819) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p4476))
    (h96485 : p4476 ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2707) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4476) := (Or.elim h50214 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h96485 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107860 (p2295 p2383 p2668 p2807 p3987 p4569 : Prop)
    (h98601 : p2807 ∨ (¬ p2383) ∨ (¬ p4569) ∨ (¬ p3987) ∨ p2668)
    (h102696 : p4569 ∨ p2295)
    : p2295 ∨ (¬ p3987) ∨ (¬ p2383) ∨ p2668 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4569) := (Or.elim h98601 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102696 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107868 (p2156 p2284 p2950 p3115 p3286 p5039 : Prop)
    (h85507 : (¬ p3286) ∨ (¬ p2284) ∨ p2156 ∨ (¬ p2950) ∨ (¬ p5039))
    (h102666 : p5039 ∨ (¬ p3115))
    : (¬ p3115) ∨ p2156 ∨ (¬ p3286) ∨ (¬ p2284) ∨ (¬ p2950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5039) := (Or.elim h85507 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h102666 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107872 (p2245 p2651 p2727 p3189 p3449 p5078 : Prop)
    (h98141 : (¬ p2727) ∨ (¬ p3449) ∨ (¬ p5078) ∨ p2651 ∨ (¬ p2245))
    (h96308 : p5078 ∨ (¬ p3189))
    : (¬ p3189) ∨ (¬ p3449) ∨ p2651 ∨ (¬ p2727) ∨ (¬ p2245) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5078) := (Or.elim h98141 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96308 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107875 (p2608 p3201 p3367 p3399 p4424 p5082 : Prop)
    (h93474 : (¬ p4424) ∨ p3399 ∨ (¬ p3367) ∨ (¬ p5082) ∨ (¬ p2608))
    (h102661 : p5082 ∨ p3201)
    : p3201 ∨ (¬ p4424) ∨ (¬ p2608) ∨ p3399 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5082) := (Or.elim h93474 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102661 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107876 (p2156 p3461 p3737 p4032 p4033 p5253 : Prop)
    (h41466 : (¬ p2156) ∨ (¬ p3737) ∨ (¬ p4032) ∨ (¬ p4033) ∨ (¬ p5253))
    (h102363 : p5253 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p3737) ∨ (¬ p4033) ∨ (¬ p4032) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5253) := (Or.elim h41466 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h102363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107879 (p2307 p2553 p2584 p3346 p3564 p5321 : Prop)
    (h96592 : (¬ p2307) ∨ (¬ p3346) ∨ p2553 ∨ (¬ p5321) ∨ (¬ p2584))
    (h102594 : p5321 ∨ p3564)
    : p3564 ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p3346) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5321) := (Or.elim h96592 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102594 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107880 (p3016 p3276 p3506 p3564 p5176 p5324 : Prop)
    (h93313 : p3276 ∨ (¬ p5176) ∨ p3016 ∨ (¬ p5324) ∨ (¬ p3506))
    (h96143 : p5324 ∨ (¬ p3564))
    : (¬ p3564) ∨ p3016 ∨ (¬ p3506) ∨ p3276 ∨ (¬ p5176) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5176 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5324) := (Or.elim h93313 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96143 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107885 (p3276 p3367 p3599 p3670 p5159 p5391 p5682 : Prop)
    (h105766 : p5682)
    (h96574 : p3599 ∨ p3276 ∨ (¬ p5159) ∨ (¬ p5682) ∨ (¬ p5391) ∨ (¬ p3367))
    (h102636 : p5391 ∨ (¬ p3670))
    : (¬ p3670) ∨ p3276 ∨ p3599 ∨ (¬ p3367) ∨ (¬ p5159) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5159 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5682 := h105766;
    let u6 : (¬ p5391) := (Or.elim h96574 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h102636 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107894 (p2307 p2493 p2506 p3309 p3379 p5020 : Prop)
    (h79813 : (¬ p5020) ∨ (¬ p2307) ∨ (¬ p2506) ∨ p3309 ∨ p3379)
    (h96945 : p2506 ∨ (¬ p2493))
    : (¬ p2493) ∨ (¬ p2307) ∨ p3309 ∨ (¬ p5020) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2506) := (Or.elim h79813 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96945 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107898 (p3276 p4184 p5131 p5175 p5284 : Prop)
    (h26814 : (¬ p4184) ∨ (¬ p5131) ∨ (¬ p5175) ∨ (¬ p5284))
    (h102655 : p4184 ∨ (¬ p3276))
    : (¬ p3276) ∨ (¬ p5284) ∨ (¬ p5175) ∨ (¬ p5131) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5131 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4184) := (Or.elim h26814 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h102655 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107901 (p2122 p2707 p2819 p3063 p4472 p4869 : Prop)
    (h88458 : (¬ p4869) ∨ (¬ p3063) ∨ p2819 ∨ p2707 ∨ (¬ p4472))
    (h102703 : p4472 ∨ p2122)
    : p2122 ∨ (¬ p3063) ∨ p2707 ∨ p2819 ∨ (¬ p4869) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4472) := (Or.elim h88458 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => r3))))))));
    (Or.elim h102703 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107902 (p2707 p2819 p3063 p4472 p4778 p4841 p4869 : Prop)
    (h88458 : (¬ p4869) ∨ (¬ p3063) ∨ p2819 ∨ p2707 ∨ (¬ p4472))
    (h28943 : p4472 ∨ (¬ p4778) ∨ (¬ p4841))
    : (¬ p4841) ∨ (¬ p4778) ∨ (¬ p3063) ∨ p2707 ∨ p2819 ∨ (¬ p4869) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4841 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4472) := (Or.elim h88458 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h28943 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step107903 (p2177 p2341 p3093 p3309 p4588 p5242 : Prop)
    (h94191 : (¬ p5242) ∨ p3093 ∨ p3309 ∨ (¬ p4588) ∨ p2177)
    (h102693 : p4588 ∨ p2341)
    : p2341 ∨ (¬ p5242) ∨ p2177 ∨ p3093 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4588) := (Or.elim h94191 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h102693 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107907 (p2187 p2284 p2341 p2459 p2807 p2946 p3073 p4853 p4998 : Prop)
    (h80121 : p2341 ∨ (¬ p3073) ∨ (¬ p2284) ∨ p2459 ∨ (¬ p2946) ∨ (¬ p2187) ∨ (¬ p4998) ∨ (¬ p4853))
    (h93814 : p4853 ∨ (¬ p2807))
    : (¬ p2807) ∨ p2459 ∨ (¬ p3073) ∨ (¬ p2284) ∨ (¬ p2187) ∨ (¬ p4998) ∨ p2341 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4853) := (Or.elim h80121 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => r6))))))))))))));
    (Or.elim h93814 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107911 (p2253 p2363 p2383 p2651 p2727 p3005 p3189 p3609 p4969 : Prop)
    (h107539 : (¬ p3189) ∨ p2727 ∨ (¬ p2253) ∨ p2363 ∨ (¬ p3609) ∨ p2383 ∨ (¬ p2651) ∨ (¬ p4969))
    (h95979 : p4969 ∨ (¬ p3005))
    : (¬ p3005) ∨ (¬ p3189) ∨ p2383 ∨ p2363 ∨ (¬ p2253) ∨ (¬ p2651) ∨ p2727 ∨ (¬ p3609) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4969) := (Or.elim h107539 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => r6))))))))))))));
    (Or.elim h95979 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107912 (p2088 p2363 p3063 p3093 p4197 p5018 : Prop)
    (h83515 : (¬ p3063) ∨ (¬ p5018) ∨ (¬ p2363) ∨ (¬ p4197) ∨ p2088)
    (h95388 : p5018 ∨ p3093)
    : p3093 ∨ (¬ p3063) ∨ p2088 ∨ (¬ p2363) ∨ (¬ p4197) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5018) := (Or.elim h83515 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h95388 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107913 (p2177 p2311 p2341 p3093 p3309 p5018 : Prop)
    (h85287 : p2341 ∨ (¬ p3309) ∨ (¬ p2311) ∨ (¬ p5018) ∨ (¬ p2177))
    (h95388 : p5018 ∨ p3093)
    : p3093 ∨ p2341 ∨ (¬ p3309) ∨ (¬ p2311) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5018) := (Or.elim h85287 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h95388 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107915 (p3276 p5131 p5175 p5284 : Prop)
    (h107898 : (¬ p3276) ∨ (¬ p5284) ∨ (¬ p5175) ∨ (¬ p5131))
    (h102596 : p5131 ∨ (¬ p3276))
    : (¬ p3276) ∨ (¬ p5284) ∨ (¬ p5175) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5131) := (Or.elim h107898 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h102596 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107921 (p2470 p3346 p3609 p3641 p4440 p5375 : Prop)
    (h61457 : (¬ p2470) ∨ (¬ p3346) ∨ (¬ p3609) ∨ (¬ p4440) ∨ (¬ p5375))
    (h96249 : p5375 ∨ (¬ p3641))
    : (¬ p3641) ∨ (¬ p3346) ∨ (¬ p3609) ∨ (¬ p4440) ∨ (¬ p2470) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5375) := (Or.elim h61457 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h96249 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107923 (p2241 p2363 p2383 p2744 p2778 p3083 p3366 p3379 p3487 p3609 p3641 p5375 : Prop)
    (h106503 : p2744)
    (h95427 : p2363 ∨ p2241 ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p5375) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3609) ∨ (¬ p3379) ∨ (¬ p3487) ∨ p2383)
    (h96249 : p5375 ∨ (¬ p3641))
    : (¬ p3641) ∨ (¬ p3083) ∨ (¬ p3609) ∨ p2363 ∨ p2241 ∨ (¬ p3379) ∨ (¬ p3366) ∨ p2383 ∨ (¬ p3487) ∨ (¬ p2778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2744 := h106503;
    let u11 : (¬ p5375) := (Or.elim h95427 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (u7 r9))))))))))))))))))))));
    (Or.elim h96249 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107924 (p3707 p3773 p4374 p5413 p5414 : Prop)
    (h14004 : (¬ p3773) ∨ (¬ p4374) ∨ (¬ p5413) ∨ (¬ p5414))
    (h102632 : p5413 ∨ (¬ p3707))
    : (¬ p3707) ∨ (¬ p4374) ∨ (¬ p3773) ∨ (¬ p5414) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4374 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5413) := (Or.elim h14004 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h102632 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step107937 (p2696 p2901 p3136 p3425 p4777 p4917 : Prop)
    (h41107 : (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3425) ∨ (¬ p4777) ∨ (¬ p4917))
    (h96352 : p4917 ∨ p2901)
    : p2901 ∨ (¬ p3425) ∨ (¬ p3136) ∨ (¬ p2696) ∨ (¬ p4777) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4917) := (Or.elim h41107 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96352 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107938 (p2156 p2284 p2807 p2901 p2958 p4917 : Prop)
    (h98191 : (¬ p2958) ∨ p2284 ∨ (¬ p2156) ∨ (¬ p4917) ∨ p2807)
    (h96352 : p4917 ∨ p2901)
    : p2901 ∨ p2284 ∨ (¬ p2156) ∨ p2807 ∨ (¬ p2958) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4917) := (Or.elim h98191 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96352 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107947 (p3212 p4207 p4209 p5092 p5093 p5094 p6008 : Prop)
    (h13045 : (¬ p3212) ∨ (¬ p4207) ∨ (¬ p4209) ∨ (¬ p5093) ∨ (¬ p5094) ∨ (¬ p6008))
    (h8578 : (¬ p5092) ∨ p5093)
    : (¬ p5092) ∨ (¬ p4207) ∨ (¬ p6008) ∨ (¬ p4209) ∨ (¬ p3212) ∨ (¬ p5094) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5092 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6008 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4209 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5094 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5093) := (Or.elim h13045 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h8578 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step107948 (p3212 p4207 p4209 p5092 p5093 p5094 p6008 : Prop)
    (h8580 : (¬ p3212) ∨ (¬ p4207) ∨ (¬ p4209) ∨ p5092 ∨ (¬ p5093) ∨ (¬ p5094))
    (h13043 : p5093 ∨ p6008)
    : p6008 ∨ (¬ p4207) ∨ p5092 ∨ (¬ p4209) ∨ (¬ p3212) ∨ (¬ p5094) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6008) := (fun h => hn (Or.inl h));
    let u1 : p4207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5092) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4209 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5094 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5093) := (Or.elim h8580 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h13043 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107975 (p3619 p4233 p5351 p5352 p5353 p5354 p6092 : Prop)
    (h13660 : (¬ p3619) ∨ (¬ p4233) ∨ (¬ p5352) ∨ (¬ p5353) ∨ (¬ p5354) ∨ (¬ p6092))
    (h9200 : (¬ p5351) ∨ p5354)
    : (¬ p5351) ∨ (¬ p6092) ∨ (¬ p4233) ∨ (¬ p5352) ∨ (¬ p5353) ∨ (¬ p3619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5351 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6092 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5353 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5354) := (Or.elim h13660 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h9200 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step107976 (p3619 p4233 p5351 p5352 p5353 p5354 p6092 : Prop)
    (h9201 : (¬ p3619) ∨ (¬ p4233) ∨ p5351 ∨ (¬ p5352) ∨ (¬ p5353) ∨ (¬ p5354))
    (h13657 : p5354 ∨ p6092)
    : p6092 ∨ (¬ p5352) ∨ p5351 ∨ (¬ p4233) ∨ (¬ p3619) ∨ (¬ p5353) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6092) := (fun h => hn (Or.inl h));
    let u1 : p5352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5351) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5353 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5354) := (Or.elim h9201 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h13657 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step107991 (p5421 p6112 p6113 : Prop)
    (h66611 : (¬ p6112) ∨ (¬ p6113))
    (h13848 : p5421 ∨ p6112)
    : p5421 ∨ (¬ p6113) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5421) := (fun h => hn (Or.inl h));
    let u1 : p6113 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6112) := (Or.elim h66611 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h13848 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108002 (p3717 p5421 p6113 : Prop)
    (h107991 : p5421 ∨ (¬ p6113))
    (h13855 : p3717 ∨ p6113)
    : p3717 ∨ p5421 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5421) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6113) := (Or.elim h107991 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13855 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108009 (p3727 p4258 p5436 p5437 p5438 p5439 p6116 : Prop)
    (h13875 : (¬ p3727) ∨ (¬ p4258) ∨ (¬ p5437) ∨ (¬ p5438) ∨ (¬ p5439) ∨ (¬ p6116))
    (h9378 : (¬ p5436) ∨ p5437)
    : (¬ p5436) ∨ (¬ p3727) ∨ (¬ p5439) ∨ (¬ p4258) ∨ (¬ p5438) ∨ (¬ p6116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5436 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5439 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4258 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p6116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5437) := (Or.elim h13875 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h9378 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108010 (p3727 p4258 p5436 p5437 p5438 p5439 p6116 : Prop)
    (h9383 : (¬ p3727) ∨ (¬ p4258) ∨ p5436 ∨ (¬ p5437) ∨ (¬ p5438) ∨ (¬ p5439))
    (h13870 : p5437 ∨ p6116)
    : p6116 ∨ p5436 ∨ (¬ p3727) ∨ (¬ p4258) ∨ (¬ p5438) ∨ (¬ p5439) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5436) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4258 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5439 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5437) := (Or.elim h9383 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h13870 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108011 (p3727 p4258 p5436 p5438 p5439 p6116 : Prop)
    (h108009 : (¬ p5436) ∨ (¬ p3727) ∨ (¬ p5439) ∨ (¬ p4258) ∨ (¬ p5438) ∨ (¬ p6116))
    (h9382 : (¬ p5436) ∨ p5439)
    : (¬ p5436) ∨ (¬ p3727) ∨ (¬ p4258) ∨ (¬ p5438) ∨ (¬ p6116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5436 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4258 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p6116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5439) := (Or.elim h108009 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h9382 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108012 (p3727 p4258 p5436 p5438 p5439 p6116 : Prop)
    (h108010 : p6116 ∨ p5436 ∨ (¬ p3727) ∨ (¬ p4258) ∨ (¬ p5438) ∨ (¬ p5439))
    (h13874 : p5439 ∨ p6116)
    : p6116 ∨ p5436 ∨ (¬ p3727) ∨ (¬ p4258) ∨ (¬ p5438) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5436) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4258 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5439) := (Or.elim h108010 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h13874 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108013 (p4393 p5440 p5442 p5443 p5444 p5445 p6118 : Prop)
    (h13886 : (¬ p4393) ∨ (¬ p5440) ∨ (¬ p5443) ∨ (¬ p5444) ∨ (¬ p5445) ∨ (¬ p6118))
    (h9394 : (¬ p5442) ∨ p5445)
    : (¬ p5442) ∨ (¬ p6118) ∨ (¬ p5444) ∨ (¬ p5440) ∨ (¬ p5443) ∨ (¬ p4393) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5445) := (Or.elim h13886 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h9394 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108014 (p4393 p5440 p5442 p5443 p5444 p5445 p6118 : Prop)
    (h9395 : (¬ p4393) ∨ (¬ p5440) ∨ p5442 ∨ (¬ p5443) ∨ (¬ p5444) ∨ (¬ p5445))
    (h13885 : p5445 ∨ p6118)
    : p6118 ∨ p5442 ∨ (¬ p5444) ∨ (¬ p4393) ∨ (¬ p5440) ∨ (¬ p5443) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6118) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5442) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5445) := (Or.elim h9395 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => r4))))))))));
    (Or.elim h13885 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108021 (p3888 p3893 p5517 p5518 p5519 p5520 p6134 : Prop)
    (h14123 : (¬ p3888) ∨ (¬ p3893) ∨ (¬ p5518) ∨ (¬ p5519) ∨ (¬ p5520) ∨ (¬ p6134))
    (h9630 : (¬ p5517) ∨ p5520)
    : (¬ p5517) ∨ (¬ p3888) ∨ (¬ p3893) ∨ (¬ p5519) ∨ (¬ p5518) ∨ (¬ p6134) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5517 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3893 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p6134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5520) := (Or.elim h14123 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h9630 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108022 (p3888 p3893 p5517 p5518 p5519 p5520 p6134 : Prop)
    (h9631 : (¬ p3888) ∨ (¬ p3893) ∨ p5517 ∨ (¬ p5518) ∨ (¬ p5519) ∨ (¬ p5520))
    (h14122 : p5520 ∨ p6134)
    : p6134 ∨ p5517 ∨ (¬ p3888) ∨ (¬ p3893) ∨ (¬ p5519) ∨ (¬ p5518) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5517) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3893 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5520) := (Or.elim h9631 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h14122 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108034 (p3892 p6136 p6137 : Prop)
    (h66619 : (¬ p6136) ∨ (¬ p6137))
    (h14131 : p3892 ∨ p6136)
    : p3892 ∨ (¬ p6137) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3892) := (fun h => hn (Or.inl h));
    let u1 : p6137 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6136) := (Or.elim h66619 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h14131 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108054 (p3931 p5549 p5550 p5551 p5552 p5553 p6143 : Prop)
    (h14258 : (¬ p3931) ∨ (¬ p5550) ∨ (¬ p5551) ∨ (¬ p5552) ∨ (¬ p5553) ∨ (¬ p6143))
    (h9710 : (¬ p5549) ∨ p5552)
    : (¬ p5549) ∨ (¬ p3931) ∨ (¬ p6143) ∨ (¬ p5550) ∨ (¬ p5551) ∨ (¬ p5553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5549 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5552) := (Or.elim h14258 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h9710 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108055 (p3931 p5549 p5550 p5551 p5552 p5553 p6143 : Prop)
    (h9712 : (¬ p3931) ∨ p5549 ∨ (¬ p5550) ∨ (¬ p5551) ∨ (¬ p5552) ∨ (¬ p5553))
    (h14256 : p5552 ∨ p6143)
    : p6143 ∨ (¬ p3931) ∨ p5549 ∨ (¬ p5550) ∨ (¬ p5551) ∨ (¬ p5553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6143) := (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5549) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5552) := (Or.elim h9712 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h14256 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108056 (p3931 p5549 p5550 p5551 p5553 p6143 : Prop)
    (h108054 : (¬ p5549) ∨ (¬ p3931) ∨ (¬ p6143) ∨ (¬ p5550) ∨ (¬ p5551) ∨ (¬ p5553))
    (h9711 : (¬ p5549) ∨ p5553)
    : (¬ p5549) ∨ (¬ p3931) ∨ (¬ p6143) ∨ (¬ p5550) ∨ (¬ p5551) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5549 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5553) := (Or.elim h108054 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h9711 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108057 (p3931 p5549 p5550 p5551 p5553 p6143 : Prop)
    (h108055 : p6143 ∨ (¬ p3931) ∨ p5549 ∨ (¬ p5550) ∨ (¬ p5551) ∨ (¬ p5553))
    (h14257 : p5553 ∨ p6143)
    : p6143 ∨ (¬ p3931) ∨ p5549 ∨ (¬ p5550) ∨ (¬ p5551) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6143) := (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5549) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5553) := (Or.elim h108055 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h14257 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108074 (p5597 p5598 p5599 p5600 p5601 p5602 p6157 : Prop)
    (h14524 : (¬ p5598) ∨ (¬ p5599) ∨ (¬ p5600) ∨ (¬ p5601) ∨ (¬ p5602) ∨ (¬ p6157))
    (h9865 : (¬ p5597) ∨ p5601)
    : (¬ p5597) ∨ (¬ p5600) ∨ (¬ p6157) ∨ (¬ p5598) ∨ (¬ p5599) ∨ (¬ p5602) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5597 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5602 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5601) := (Or.elim h14524 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h9865 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108075 (p5597 p5598 p5599 p5600 p5601 p5602 p6157 : Prop)
    (h9867 : p5597 ∨ (¬ p5598) ∨ (¬ p5599) ∨ (¬ p5600) ∨ (¬ p5601) ∨ (¬ p5602))
    (h14522 : p5601 ∨ p6157)
    : p6157 ∨ (¬ p5600) ∨ p5597 ∨ (¬ p5598) ∨ (¬ p5599) ∨ (¬ p5602) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6157) := (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5597) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5602 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5601) := (Or.elim h9867 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h14522 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108076 (p5597 p5598 p5599 p5600 p5602 p6157 : Prop)
    (h108074 : (¬ p5597) ∨ (¬ p5600) ∨ (¬ p6157) ∨ (¬ p5598) ∨ (¬ p5599) ∨ (¬ p5602))
    (h9866 : (¬ p5597) ∨ p5602)
    : (¬ p5597) ∨ (¬ p5600) ∨ (¬ p6157) ∨ (¬ p5598) ∨ (¬ p5599) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5597 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5602) := (Or.elim h108074 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h9866 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108077 (p5597 p5598 p5599 p5600 p5602 p6157 : Prop)
    (h108075 : p6157 ∨ (¬ p5600) ∨ p5597 ∨ (¬ p5598) ∨ (¬ p5599) ∨ (¬ p5602))
    (h14523 : p5602 ∨ p6157)
    : p6157 ∨ (¬ p5600) ∨ p5597 ∨ (¬ p5598) ∨ (¬ p5599) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6157) := (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5597) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5602) := (Or.elim h108075 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h14523 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108090 (p4019 p5615 p5616 p5617 p5618 p5619 p6161 : Prop)
    (h14547 : (¬ p4019) ∨ (¬ p5616) ∨ (¬ p5617) ∨ (¬ p5618) ∨ (¬ p5619) ∨ (¬ p6161))
    (h9886 : (¬ p5615) ∨ p5617)
    : (¬ p5615) ∨ (¬ p4019) ∨ (¬ p6161) ∨ (¬ p5616) ∨ (¬ p5618) ∨ (¬ p5619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5615 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6161 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5616 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5618 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5617) := (Or.elim h14547 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h9886 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108091 (p4019 p5615 p5616 p5617 p5618 p5619 p6161 : Prop)
    (h9890 : (¬ p4019) ∨ p5615 ∨ (¬ p5616) ∨ (¬ p5617) ∨ (¬ p5618) ∨ (¬ p5619))
    (h14543 : p5617 ∨ p6161)
    : p6161 ∨ (¬ p4019) ∨ p5615 ∨ (¬ p5616) ∨ (¬ p5618) ∨ (¬ p5619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6161) := (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5615) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5616 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5618 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5617) := (Or.elim h9890 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h14543 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108092 (p4019 p5615 p5616 p5618 p5619 p6161 : Prop)
    (h108090 : (¬ p5615) ∨ (¬ p4019) ∨ (¬ p6161) ∨ (¬ p5616) ∨ (¬ p5618) ∨ (¬ p5619))
    (h9888 : (¬ p5615) ∨ p5618)
    : (¬ p5615) ∨ (¬ p4019) ∨ (¬ p6161) ∨ (¬ p5616) ∨ (¬ p5619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5615 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6161 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5616 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5618) := (Or.elim h108090 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h9888 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108093 (p4019 p5615 p5616 p5618 p5619 p6161 : Prop)
    (h108091 : p6161 ∨ (¬ p4019) ∨ p5615 ∨ (¬ p5616) ∨ (¬ p5618) ∨ (¬ p5619))
    (h14545 : p5618 ∨ p6161)
    : p6161 ∨ (¬ p4019) ∨ p5615 ∨ (¬ p5616) ∨ (¬ p5619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6161) := (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5615) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5616 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5618) := (Or.elim h108091 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h14545 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108094 (p4019 p5615 p5616 p5619 p6161 : Prop)
    (h108092 : (¬ p5615) ∨ (¬ p4019) ∨ (¬ p6161) ∨ (¬ p5616) ∨ (¬ p5619))
    (h9889 : (¬ p5615) ∨ p5619)
    : (¬ p5615) ∨ (¬ p4019) ∨ (¬ p6161) ∨ (¬ p5616) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5615 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6161 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5616 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5619) := (Or.elim h108092 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h9889 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step108095 (p4019 p5615 p5616 p5619 p6161 : Prop)
    (h108093 : p6161 ∨ (¬ p4019) ∨ p5615 ∨ (¬ p5616) ∨ (¬ p5619))
    (h14546 : p5619 ∨ p6161)
    : p6161 ∨ (¬ p4019) ∨ p5615 ∨ (¬ p5616) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6161) := (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5615) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5616 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5619) := (Or.elim h108093 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h14546 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108107 (p4435 p6163 p6164 : Prop)
    (h66628 : (¬ p6163) ∨ (¬ p6164))
    (h14699 : p4435 ∨ p6163)
    : p4435 ∨ (¬ p6164) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4435) := (fun h => hn (Or.inl h));
    let u1 : p6164 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6163) := (Or.elim h66628 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h14699 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108124 (p4372 p6166 p6167 : Prop)
    (h66629 : (¬ p6166) ∨ (¬ p6167))
    (h14718 : p4372 ∨ p6166)
    : p4372 ∨ (¬ p6167) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4372) := (fun h => hn (Or.inl h));
    let u1 : p6167 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6166) := (Or.elim h66629 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h14718 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108136 (p4063 p4372 p6167 : Prop)
    (h108124 : p4372 ∨ (¬ p6167))
    (h14727 : p4063 ∨ p6167)
    : p4063 ∨ p4372 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4063) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4372) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6167) := (Or.elim h108124 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h14727 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108141 (p4075 p5648 p5649 p5650 p5651 p5652 p6170 : Prop)
    (h14760 : (¬ p4075) ∨ (¬ p5649) ∨ (¬ p5650) ∨ (¬ p5651) ∨ (¬ p5652) ∨ (¬ p6170))
    (h10008 : (¬ p5648) ∨ p5651)
    : (¬ p5648) ∨ (¬ p4075) ∨ (¬ p6170) ∨ (¬ p5649) ∨ (¬ p5650) ∨ (¬ p5652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5649 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5651) := (Or.elim h14760 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h10008 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108142 (p4075 p5648 p5649 p5650 p5651 p5652 p6170 : Prop)
    (h10010 : (¬ p4075) ∨ p5648 ∨ (¬ p5649) ∨ (¬ p5650) ∨ (¬ p5651) ∨ (¬ p5652))
    (h14758 : p5651 ∨ p6170)
    : p6170 ∨ (¬ p4075) ∨ p5648 ∨ (¬ p5649) ∨ (¬ p5650) ∨ (¬ p5652) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6170) := (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5648) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5649 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5651) := (Or.elim h10010 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h14758 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108143 (p4075 p5648 p5649 p5650 p5652 p6170 : Prop)
    (h108141 : (¬ p5648) ∨ (¬ p4075) ∨ (¬ p6170) ∨ (¬ p5649) ∨ (¬ p5650) ∨ (¬ p5652))
    (h10009 : (¬ p5648) ∨ p5652)
    : (¬ p5648) ∨ (¬ p4075) ∨ (¬ p6170) ∨ (¬ p5649) ∨ (¬ p5650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5649 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5652) := (Or.elim h108141 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h10009 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108144 (p4075 p5648 p5649 p5650 p5652 p6170 : Prop)
    (h108142 : p6170 ∨ (¬ p4075) ∨ p5648 ∨ (¬ p5649) ∨ (¬ p5650) ∨ (¬ p5652))
    (h14759 : p5652 ∨ p6170)
    : p6170 ∨ (¬ p4075) ∨ p5648 ∨ (¬ p5649) ∨ (¬ p5650) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6170) := (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5648) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5649 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5652) := (Or.elim h108142 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h14759 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108145 (p4139 p4141 p5659 p5660 p5661 p5662 p6172 : Prop)
    (h15005 : (¬ p4139) ∨ (¬ p4141) ∨ (¬ p5660) ∨ (¬ p5661) ∨ (¬ p5662) ∨ (¬ p6172))
    (h10121 : (¬ p5659) ∨ p5662)
    : (¬ p5659) ∨ (¬ p5660) ∨ (¬ p6172) ∨ (¬ p4139) ∨ (¬ p4141) ∨ (¬ p5661) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5659 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4141 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5662) := (Or.elim h15005 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h10121 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108146 (p4139 p4141 p5659 p5660 p5661 p5662 p6172 : Prop)
    (h10122 : (¬ p4139) ∨ (¬ p4141) ∨ p5659 ∨ (¬ p5660) ∨ (¬ p5661) ∨ (¬ p5662))
    (h15004 : p5662 ∨ p6172)
    : p6172 ∨ (¬ p5660) ∨ p5659 ∨ (¬ p4139) ∨ (¬ p4141) ∨ (¬ p5661) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5659) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4141 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5662) := (Or.elim h10122 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h15004 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108161 (p5681 p6178 p6179 : Prop)
    (h66633 : (¬ p6178) ∨ (¬ p6179))
    (h15152 : p5681 ∨ p6178)
    : p5681 ∨ (¬ p6179) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5681) := (fun h => hn (Or.inl h));
    let u1 : p6179 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6178) := (Or.elim h66633 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h15152 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108172 (p4166 p5681 p6179 : Prop)
    (h108161 : p5681 ∨ (¬ p6179))
    (h15159 : p4166 ∨ p6179)
    : p4166 ∨ p5681 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4166) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5681) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6179) := (Or.elim h108161 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h15159 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108179 (p4181 p5696 p5697 p5698 p5699 p5700 p6182 : Prop)
    (h15271 : (¬ p4181) ∨ (¬ p5697) ∨ (¬ p5698) ∨ (¬ p5699) ∨ (¬ p5700) ∨ (¬ p6182))
    (h10231 : (¬ p5696) ∨ p5699)
    : (¬ p5696) ∨ (¬ p6182) ∨ (¬ p5700) ∨ (¬ p5697) ∨ (¬ p5698) ∨ (¬ p4181) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6182 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5699) := (Or.elim h15271 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h10231 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108180 (p4181 p5696 p5697 p5698 p5699 p5700 p6182 : Prop)
    (h10233 : (¬ p4181) ∨ p5696 ∨ (¬ p5697) ∨ (¬ p5698) ∨ (¬ p5699) ∨ (¬ p5700))
    (h15269 : p5699 ∨ p6182)
    : p6182 ∨ p5696 ∨ (¬ p5697) ∨ (¬ p4181) ∨ (¬ p5698) ∨ (¬ p5700) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6182) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5699) := (Or.elim h10233 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h15269 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108181 (p4181 p5696 p5697 p5698 p5700 p6182 : Prop)
    (h108179 : (¬ p5696) ∨ (¬ p6182) ∨ (¬ p5700) ∨ (¬ p5697) ∨ (¬ p5698) ∨ (¬ p4181))
    (h10232 : (¬ p5696) ∨ p5700)
    : (¬ p5696) ∨ (¬ p6182) ∨ (¬ p5697) ∨ (¬ p5698) ∨ (¬ p4181) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6182 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5700) := (Or.elim h108179 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h10232 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108182 (p4181 p5696 p5697 p5698 p5700 p6182 : Prop)
    (h108180 : p6182 ∨ p5696 ∨ (¬ p5697) ∨ (¬ p4181) ∨ (¬ p5698) ∨ (¬ p5700))
    (h15270 : p5700 ∨ p6182)
    : p6182 ∨ p5696 ∨ (¬ p5697) ∨ (¬ p4181) ∨ (¬ p5698) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6182) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5700) := (Or.elim h108180 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h15270 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108214 (p4228 p6187 p6188 : Prop)
    (h66636 : (¬ p6187) ∨ (¬ p6188))
    (h15773 : p4228 ∨ p6188)
    : p4228 ∨ (¬ p6187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4228) := (fun h => hn (Or.inl h));
    let u1 : p6187 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6188) := (Or.elim h66636 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h15773 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108233 (p5740 p6193 p6194 : Prop)
    (h66638 : (¬ p6193) ∨ (¬ p6194))
    (h16406 : p5740 ∨ p6193)
    : p5740 ∨ (¬ p6194) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5740) := (fun h => hn (Or.inl h));
    let u1 : p6194 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6193) := (Or.elim h66638 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h16406 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108244 (p4272 p5740 p6194 : Prop)
    (h108233 : p5740 ∨ (¬ p6194))
    (h16413 : p4272 ∨ p6194)
    : p4272 ∨ p5740 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4272) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5740) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6194) := (Or.elim h108233 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h16413 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108311 (p2341 p2417 p2911 p3346 p4637 p5201 : Prop)
    (h95980 : (¬ p4637) ∨ (¬ p2341) ∨ (¬ p5201) ∨ (¬ p3346) ∨ p2911)
    (h102581 : p4637 ∨ p2417)
    : p2417 ∨ (¬ p2341) ∨ (¬ p3346) ∨ (¬ p5201) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4637) := (Or.elim h95980 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h102581 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108312 (p2417 p2707 p3367 p3658 p4637 p5160 : Prop)
    (h99813 : (¬ p4637) ∨ (¬ p5160) ∨ (¬ p2707) ∨ p3367 ∨ (¬ p3658))
    (h102581 : p4637 ∨ p2417)
    : p2417 ∨ (¬ p2707) ∨ (¬ p3658) ∨ (¬ p5160) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4637) := (Or.elim h99813 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h102581 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108315 (p2449 p2685 p2707 p3599 p4783 p5233 : Prop)
    (h88406 : (¬ p3599) ∨ (¬ p5233) ∨ (¬ p4783) ∨ p2707 ∨ p2449)
    (h96397 : p4783 ∨ (¬ p2685))
    : (¬ p2685) ∨ p2707 ∨ p2449 ∨ (¬ p3599) ∨ (¬ p5233) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4783) := (Or.elim h88406 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96397 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108320 (p2707 p2717 p3399 p3449 p4797 p5307 : Prop)
    (h97093 : p3399 ∨ (¬ p3449) ∨ (¬ p4797) ∨ p2717 ∨ (¬ p5307))
    (h102685 : p4797 ∨ (¬ p2707))
    : (¬ p2707) ∨ (¬ p3449) ∨ p3399 ∨ (¬ p5307) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4797) := (Or.elim h97093 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102685 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108321 (p2707 p3399 p3434 p3830 p4797 p5362 : Prop)
    (h102151 : (¬ p3830) ∨ p3399 ∨ (¬ p5362) ∨ p3434 ∨ (¬ p4797))
    (h102685 : p4797 ∨ (¬ p2707))
    : (¬ p2707) ∨ (¬ p3830) ∨ p3434 ∨ p3399 ∨ (¬ p5362) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4797) := (Or.elim h102151 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => r3))))))));
    (Or.elim h102685 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108322 (p2761 p2870 p2982 p3698 p4129 p4382 p4830 : Prop)
    (h96665 : (¬ p4129) ∨ (¬ p4830) ∨ (¬ p4382) ∨ p2982 ∨ (¬ p3698) ∨ (¬ p2870))
    (h102684 : p4830 ∨ (¬ p2761))
    : (¬ p2761) ∨ (¬ p4129) ∨ p2982 ∨ (¬ p3698) ∨ (¬ p2870) ∨ (¬ p4382) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4382 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4830) := (Or.elim h96665 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h102684 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108323 (p2230 p2241 p2427 p2761 p2996 p3125 p3872 p3931 p4396 p4830 p5193 : Prop)
    (h105488 : p5193)
    (h82148 : (¬ p3931) ∨ p3125 ∨ p2996 ∨ p2427 ∨ (¬ p4396) ∨ (¬ p4830) ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p3872) ∨ p2230)
    (h102684 : p4830 ∨ (¬ p2761))
    : (¬ p2761) ∨ (¬ p3931) ∨ (¬ p4396) ∨ p2427 ∨ p2996 ∨ p3125 ∨ (¬ p3872) ∨ p2230 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5193 := h105488;
    let u10 : (¬ p4830) := (Or.elim h82148 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (u7 r8))))))))))))))))))));
    (Or.elim h102684 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108328 (p2187 p2248 p2284 p2707 p2819 p2946 p3425 p3537 p3873 p4863 : Prop)
    (h105365 : p2248)
    (h101892 : (¬ p2707) ∨ (¬ p4863) ∨ (¬ p2187) ∨ (¬ p2248) ∨ (¬ p3873) ∨ (¬ p3425) ∨ (¬ p2946) ∨ p3537 ∨ (¬ p2284))
    (h96381 : p4863 ∨ (¬ p2819))
    : (¬ p2819) ∨ p3537 ∨ (¬ p2284) ∨ (¬ p2187) ∨ (¬ p2946) ∨ (¬ p2707) ∨ (¬ p3425) ∨ (¬ p3873) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2248 := h105365;
    let u9 : (¬ p4863) := (Or.elim h101892 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (False.elim (r7 u2))))))))))))))))));
    (Or.elim h96381 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108329 (p2187 p2248 p2284 p2341 p2819 p2946 p3073 p3609 p4863 p5206 p5307 : Prop)
    (h105365 : p2248)
    (h74957 : (¬ p5307) ∨ (¬ p5206) ∨ p3073 ∨ (¬ p2946) ∨ (¬ p3609) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2187) ∨ (¬ p4863) ∨ p2341)
    (h96381 : p4863 ∨ (¬ p2819))
    : (¬ p2819) ∨ (¬ p2187) ∨ p2341 ∨ (¬ p2284) ∨ (¬ p2946) ∨ p3073 ∨ (¬ p3609) ∨ (¬ p5206) ∨ (¬ p5307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2248 := h105365;
    let u10 : (¬ p4863) := (Or.elim h74957 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (u2 r8))))))))))))))))))));
    (Or.elim h96381 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108330 (p2341 p2881 p3246 p4032 p4988 p5102 : Prop)
    (h76725 : (¬ p5102) ∨ (¬ p2341) ∨ (¬ p4988) ∨ (¬ p4032) ∨ p2881)
    (h102563 : p5102 ∨ p3246)
    : p3246 ∨ (¬ p4032) ∨ (¬ p2341) ∨ p2881 ∨ (¬ p4988) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5102) := (Or.elim h76725 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102563 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108331 (p2406 p2922 p2982 p3246 p3569 p5102 : Prop)
    (h88772 : p2982 ∨ (¬ p5102) ∨ (¬ p3569) ∨ (¬ p2922) ∨ p2406)
    (h102563 : p5102 ∨ p3246)
    : p3246 ∨ p2982 ∨ (¬ p2922) ∨ p2406 ∨ (¬ p3569) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5102) := (Or.elim h88772 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102563 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108332 (p2156 p2284 p2901 p3246 p4032 p5102 : Prop)
    (h97945 : (¬ p2901) ∨ p2284 ∨ (¬ p4032) ∨ (¬ p5102) ∨ (¬ p2156))
    (h102563 : p5102 ∨ p3246)
    : p3246 ∨ (¬ p4032) ∨ p2284 ∨ (¬ p2901) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5102) := (Or.elim h97945 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102563 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108333 (p2156 p2284 p2901 p2972 p3246 p3370 p5102 : Prop)
    (h76455 : (¬ p2901) ∨ p2284 ∨ (¬ p5102) ∨ p2972 ∨ (¬ p3370) ∨ (¬ p2156))
    (h102563 : p5102 ∨ p3246)
    : p3246 ∨ p2284 ∨ (¬ p2156) ∨ (¬ p2901) ∨ p2972 ∨ (¬ p3370) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5102) := (Or.elim h76455 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h102563 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108335 (p2210 p2972 p3201 p3276 p3389 p4166 p4322 p5129 p5190 : Prop)
    (h105487 : p5190)
    (h97523 : (¬ p4166) ∨ (¬ p4322) ∨ p2972 ∨ (¬ p5129) ∨ p3201 ∨ p2210 ∨ (¬ p3389) ∨ (¬ p5190))
    (h96293 : p5129 ∨ p3276)
    : p3276 ∨ (¬ p4166) ∨ p3201 ∨ (¬ p4322) ∨ p2972 ∨ p2210 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p4166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5190 := h105487;
    let u8 : (¬ p5129) := (Or.elim h97523 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h96293 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108342 (p2230 p2427 p3246 p3286 p3434 p3670 p4236 p5236 p5284 : Prop)
    (h107601 : (¬ p5284) ∨ (¬ p3670) ∨ p3286 ∨ (¬ p4236) ∨ (¬ p2427) ∨ (¬ p2230) ∨ (¬ p3246) ∨ (¬ p5236))
    (h96176 : p5236 ∨ (¬ p3434))
    : (¬ p3434) ∨ (¬ p3670) ∨ (¬ p2230) ∨ (¬ p3246) ∨ p3286 ∨ (¬ p5284) ∨ (¬ p4236) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5236) := (Or.elim h107601 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => r6))))))))))))));
    (Or.elim h96176 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108344 (p2230 p2427 p2696 p2737 p3246 p3434 p3599 p3873 p5190 p5236 : Prop)
    (h105487 : p5190)
    (h82573 : (¬ p2737) ∨ p3599 ∨ (¬ p3246) ∨ p2696 ∨ (¬ p3873) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p5236) ∨ (¬ p5190))
    (h96176 : p5236 ∨ (¬ p3434))
    : (¬ p3434) ∨ p3599 ∨ p2696 ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3873) ∨ (¬ p2230) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5190 := h105487;
    let u9 : (¬ p5236) := (Or.elim h82573 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h96176 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108346 (p2088 p2459 p2717 p3425 p3961 p5258 : Prop)
    (h101683 : (¬ p5258) ∨ (¬ p3961) ∨ p2088 ∨ (¬ p2459) ∨ (¬ p2717))
    (h96168 : p5258 ∨ (¬ p3425))
    : (¬ p3425) ∨ (¬ p2459) ∨ (¬ p2717) ∨ p2088 ∨ (¬ p3961) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5258) := (Or.elim h101683 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96168 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108360 (p4139 p4141 p5659 p5660 p5661 p6172 : Prop)
    (h108145 : (¬ p5659) ∨ (¬ p5660) ∨ (¬ p6172) ∨ (¬ p4139) ∨ (¬ p4141) ∨ (¬ p5661))
    (h10117 : p4141 ∨ (¬ p5659))
    : (¬ p5659) ∨ (¬ p5660) ∨ (¬ p6172) ∨ (¬ p4139) ∨ (¬ p5661) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5659 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4141) := (Or.elim h108145 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h10117 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108361 (p4139 p4141 p5659 p5660 p5661 p6172 : Prop)
    (h108146 : p6172 ∨ (¬ p5660) ∨ p5659 ∨ (¬ p4139) ∨ (¬ p4141) ∨ (¬ p5661))
    (h15002 : p4141 ∨ p6172)
    : p6172 ∨ (¬ p5660) ∨ p5659 ∨ (¬ p4139) ∨ (¬ p5661) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5659) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4141) := (Or.elim h108146 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h15002 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108362 (p3791 p4139 p4140 p4141 p5659 : Prop)
    (h6178 : (¬ p3791) ∨ (¬ p4139) ∨ (¬ p4140) ∨ (¬ p4141))
    (h10117 : p4141 ∨ (¬ p5659))
    : (¬ p5659) ∨ (¬ p3791) ∨ (¬ p4139) ∨ (¬ p4140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5659 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4141) := (Or.elim h6178 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h10117 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108364 (p3727 p4258 p5436 p5438 p6116 : Prop)
    (h108011 : (¬ p5436) ∨ (¬ p3727) ∨ (¬ p4258) ∨ (¬ p5438) ∨ (¬ p6116))
    (h9379 : p4258 ∨ (¬ p5436))
    : (¬ p5436) ∨ (¬ p3727) ∨ (¬ p5438) ∨ (¬ p6116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5436 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p6116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4258) := (Or.elim h108011 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h9379 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108365 (p3727 p4258 p5436 p5438 p6116 : Prop)
    (h108012 : p6116 ∨ p5436 ∨ (¬ p3727) ∨ (¬ p4258) ∨ (¬ p5438))
    (h13871 : p4258 ∨ p6116)
    : p6116 ∨ p5436 ∨ (¬ p3727) ∨ (¬ p5438) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5436) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4258) := (Or.elim h108012 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h13871 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108377 (p2717 p2881 p3246 p3609 p4807 : Prop)
    (h102861 : p3246 ∨ (¬ p4807) ∨ (¬ p3609) ∨ (¬ p2881))
    (h77955 : p4807 ∨ (¬ p2717))
    : (¬ p2717) ∨ p3246 ∨ (¬ p2881) ∨ (¬ p3609) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4807) := (Or.elim h102861 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h77955 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108378 (p2459 p2717 p3537 p3599 p4807 p5343 : Prop)
    (h96835 : (¬ p3599) ∨ (¬ p5343) ∨ p2459 ∨ p3537 ∨ (¬ p4807))
    (h77955 : p4807 ∨ (¬ p2717))
    : (¬ p2717) ∨ p2459 ∨ p3537 ∨ (¬ p3599) ∨ (¬ p5343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4807) := (Or.elim h96835 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => r3))))))));
    (Or.elim h77955 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108379 (p2098 p2264 p2717 p2807 p4117 p4807 : Prop)
    (h100709 : p2098 ∨ (¬ p4807) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p4117))
    (h77955 : p4807 ∨ (¬ p2717))
    : (¬ p2717) ∨ p2098 ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4807) := (Or.elim h100709 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h77955 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108382 (p2245 p2727 p2946 p2992 p3379 p4813 : Prop)
    (h85862 : (¬ p2992) ∨ p2946 ∨ (¬ p2245) ∨ (¬ p3379) ∨ (¬ p4813))
    (h95901 : p4813 ∨ (¬ p2727))
    : (¬ p2727) ∨ (¬ p2245) ∨ (¬ p3379) ∨ (¬ p2992) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4813) := (Or.elim h85862 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h95901 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108384 (p2230 p2241 p2406 p2727 p4079 p4813 : Prop)
    (h93844 : p2406 ∨ (¬ p4079) ∨ (¬ p4813) ∨ (¬ p2230) ∨ p2241)
    (h95901 : p4813 ∨ (¬ p2727))
    : (¬ p2727) ∨ (¬ p4079) ∨ p2241 ∨ (¬ p2230) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4813) := (Or.elim h93844 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h95901 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108386 (p2246 p2459 p2528 p2727 p2946 p3005 p3136 p3347 p3389 p4186 p4311 p4813 p4902 : Prop)
    (h105456 : p4902)
    (h101677 : p2528 ∨ (¬ p2946) ∨ (¬ p4186) ∨ (¬ p2459) ∨ (¬ p4902) ∨ (¬ p4813) ∨ (¬ p3005) ∨ (¬ p3347) ∨ (¬ p2246) ∨ p3389 ∨ p3136 ∨ (¬ p4311))
    (h95901 : p4813 ∨ (¬ p2727))
    : (¬ p2727) ∨ (¬ p4311) ∨ p2528 ∨ p3389 ∨ p3136 ∨ (¬ p4186) ∨ (¬ p2246) ∨ (¬ p3005) ∨ (¬ p3347) ∨ (¬ p2946) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4902 := h105456;
    let u12 : (¬ p4813) := (Or.elim h101677 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u3 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u4 q10))) (fun r10 => (False.elim (r10 u1))))))))))))))))))))))));
    (Or.elim h95901 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108387 (p2761 p3434 p4253 p4823 : Prop)
    (h37977 : p3434 ∨ (¬ p4253) ∨ (¬ p4823))
    (h96387 : p4823 ∨ p2761)
    : p2761 ∨ (¬ p4253) ∨ p3434 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4823) := (Or.elim h37977 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h96387 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108388 (p2761 p3516 p4063 p4823 : Prop)
    (h101543 : (¬ p4063) ∨ (¬ p4823) ∨ p3516)
    (h96387 : p4823 ∨ p2761)
    : p2761 ∨ (¬ p4063) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p4063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4823) := (Or.elim h101543 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96387 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108401 (p3212 p4207 p4209 p5092 p5094 p6008 : Prop)
    (h107947 : (¬ p5092) ∨ (¬ p4207) ∨ (¬ p6008) ∨ (¬ p4209) ∨ (¬ p3212) ∨ (¬ p5094))
    (h8579 : (¬ p5092) ∨ p5094)
    : (¬ p5092) ∨ (¬ p4207) ∨ (¬ p6008) ∨ (¬ p4209) ∨ (¬ p3212) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5092 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6008 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4209 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5094) := (Or.elim h107947 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h8579 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108402 (p3212 p4207 p4209 p5092 p5094 p6008 : Prop)
    (h107948 : p6008 ∨ (¬ p4207) ∨ p5092 ∨ (¬ p4209) ∨ (¬ p3212) ∨ (¬ p5094))
    (h13044 : p5094 ∨ p6008)
    : p6008 ∨ (¬ p4207) ∨ p5092 ∨ (¬ p4209) ∨ (¬ p3212) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6008) := (fun h => hn (Or.inl h));
    let u1 : p4207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5092) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4209 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5094) := (Or.elim h107948 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h13044 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108416 (p2284 p2341 p2459 p2946 p3266 p3461 p4393 p4850 p5248 : Prop)
    (h96128 : (¬ p4393) ∨ (¬ p4850) ∨ (¬ p5248) ∨ p2946 ∨ (¬ p2341) ∨ p2284 ∨ (¬ p3266) ∨ (¬ p2459))
    (h93206 : p5248 ∨ p3461)
    : p3461 ∨ (¬ p3266) ∨ (¬ p4393) ∨ (¬ p4850) ∨ (¬ p2341) ∨ (¬ p2459) ∨ p2284 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5248) := (Or.elim h96128 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u5))))))))))))))));
    (Or.elim h93206 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108420 (p2144 p2651 p3016 p3212 p3564 p3670 p3680 p4789 p5263 p5267 : Prop)
    (h105646 : p4789)
    (h94259 : p3670 ∨ (¬ p3212) ∨ (¬ p5267) ∨ (¬ p4789) ∨ (¬ p2144) ∨ (¬ p3680) ∨ p2651 ∨ p3564 ∨ p3016)
    (h8964 : (¬ p5263) ∨ p5267)
    : (¬ p5263) ∨ (¬ p3680) ∨ p3016 ∨ p3564 ∨ (¬ p3212) ∨ p3670 ∨ (¬ p2144) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5263 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4789 := h105646;
    let u9 : (¬ p5267) := (Or.elim h94259 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (False.elim (u2 r7))))))))))))))))));
    (Or.elim h8964 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u9 r0)))))

theorem step108430 (p3599 p3670 p3707 p5332 : Prop)
    (h96586 : p3707 ∨ (¬ p5332) ∨ (¬ p3670))
    (h96260 : p5332 ∨ (¬ p3599))
    : (¬ p3599) ∨ p3707 ∨ (¬ p3670) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5332) := (Or.elim h96586 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96260 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108436 (p2098 p3366 p3599 p3609 p5338 : Prop)
    (h96223 : (¬ p5338) ∨ p2098 ∨ (¬ p3366) ∨ (¬ p3599))
    (h102524 : p5338 ∨ p3609)
    : p3609 ∨ p2098 ∨ (¬ p3366) ∨ (¬ p3599) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5338) := (Or.elim h96223 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h102524 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108438 (p2459 p3266 p3609 p3670 p4802 p5338 : Prop)
    (h94247 : p3670 ∨ (¬ p5338) ∨ (¬ p3266) ∨ (¬ p2459) ∨ (¬ p4802))
    (h102524 : p5338 ∨ p3609)
    : p3609 ∨ (¬ p3266) ∨ p3670 ∨ (¬ p2459) ∨ (¬ p4802) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4802 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5338) := (Or.elim h94247 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102524 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108440 (p3619 p4233 p5351 p5352 p5353 p6092 : Prop)
    (h107975 : (¬ p5351) ∨ (¬ p6092) ∨ (¬ p4233) ∨ (¬ p5352) ∨ (¬ p5353) ∨ (¬ p3619))
    (h9199 : (¬ p5351) ∨ p5353)
    : (¬ p5351) ∨ (¬ p6092) ∨ (¬ p4233) ∨ (¬ p5352) ∨ (¬ p3619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5351 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6092 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5353) := (Or.elim h107975 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h9199 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108441 (p3619 p4233 p5351 p5352 p5353 p6092 : Prop)
    (h107976 : p6092 ∨ (¬ p5352) ∨ p5351 ∨ (¬ p4233) ∨ (¬ p3619) ∨ (¬ p5353))
    (h13656 : p5353 ∨ p6092)
    : p6092 ∨ (¬ p5352) ∨ p5351 ∨ (¬ p4233) ∨ (¬ p3619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6092) := (fun h => hn (Or.inl h));
    let u1 : p5352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5351) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5353) := (Or.elim h107976 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h13656 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108448 (p3707 p3773 p4374 p5414 : Prop)
    (h107924 : (¬ p3707) ∨ (¬ p4374) ∨ (¬ p3773) ∨ (¬ p5414))
    (h102633 : p5414 ∨ (¬ p3707))
    : (¬ p3707) ∨ (¬ p4374) ∨ (¬ p3773) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4374 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5414) := (Or.elim h107924 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h102633 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108454 (p5430 p5433 p5436 : Prop)
    (h9374 : (¬ p5430) ∨ p5433)
    (h66471 : p5430 ∨ p5436)
    : p5436 ∨ p5433 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5436) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5433) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5430) := (Or.elim h9374 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66471 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108462 (p3727 p5436 p5438 p6116 : Prop)
    (h108364 : (¬ p5436) ∨ (¬ p3727) ∨ (¬ p5438) ∨ (¬ p6116))
    (h9381 : (¬ p5436) ∨ p5438)
    : (¬ p5436) ∨ (¬ p3727) ∨ (¬ p6116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5436 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5438) := (Or.elim h108364 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h9381 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step108463 (p3727 p5436 p5438 p6116 : Prop)
    (h108365 : p6116 ∨ p5436 ∨ (¬ p3727) ∨ (¬ p5438))
    (h13873 : p5438 ∨ p6116)
    : p6116 ∨ p5436 ∨ (¬ p3727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5436) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5438) := (Or.elim h108365 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h13873 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108466 (p4393 p5440 p5442 p5443 p5444 p6118 : Prop)
    (h108013 : (¬ p5442) ∨ (¬ p6118) ∨ (¬ p5444) ∨ (¬ p5440) ∨ (¬ p5443) ∨ (¬ p4393))
    (h9390 : (¬ p5442) ∨ p5443)
    : (¬ p5442) ∨ (¬ p6118) ∨ (¬ p5444) ∨ (¬ p5440) ∨ (¬ p4393) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5443) := (Or.elim h108013 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h9390 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108467 (p4393 p5440 p5442 p5443 p5444 p6118 : Prop)
    (h108014 : p6118 ∨ p5442 ∨ (¬ p5444) ∨ (¬ p4393) ∨ (¬ p5440) ∨ (¬ p5443))
    (h13883 : p5443 ∨ p6118)
    : p6118 ∨ p5442 ∨ (¬ p5444) ∨ (¬ p4393) ∨ (¬ p5440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6118) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5442) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5443) := (Or.elim h108014 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h13883 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108470 (p4393 p5440 p5442 p5444 p6118 : Prop)
    (h108466 : (¬ p5442) ∨ (¬ p6118) ∨ (¬ p5444) ∨ (¬ p5440) ∨ (¬ p4393))
    (h9391 : (¬ p5442) ∨ p5444)
    : (¬ p5442) ∨ (¬ p6118) ∨ (¬ p5440) ∨ (¬ p4393) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5444) := (Or.elim h108466 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h9391 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step108471 (p4393 p5440 p5442 p5444 p6118 : Prop)
    (h108467 : p6118 ∨ p5442 ∨ (¬ p5444) ∨ (¬ p4393) ∨ (¬ p5440))
    (h13881 : p5444 ∨ p6118)
    : p6118 ∨ p5442 ∨ (¬ p4393) ∨ (¬ p5440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6118) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5442) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5444) := (Or.elim h108467 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h13881 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108490 (p5500 p5501 p5502 p5503 p5504 p5505 p6130 : Prop)
    (h14037 : (¬ p5501) ∨ (¬ p5502) ∨ (¬ p5503) ∨ (¬ p5504) ∨ (¬ p5505) ∨ (¬ p6130))
    (h9582 : (¬ p5500) ∨ p5502)
    : (¬ p5500) ∨ (¬ p5503) ∨ (¬ p6130) ∨ (¬ p5501) ∨ (¬ p5504) ∨ (¬ p5505) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5500 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6130 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5502) := (Or.elim h14037 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h9582 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108491 (p2437 p2440 p3434 p4253 p5500 p5501 p5502 : Prop)
    (h97244 : (¬ p4253) ∨ (¬ p5501) ∨ p2440 ∨ p2437 ∨ (¬ p5502) ∨ p3434)
    (h9582 : (¬ p5500) ∨ p5502)
    : (¬ p5500) ∨ (¬ p5501) ∨ (¬ p4253) ∨ p2440 ∨ p3434 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5500 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5502) := (Or.elim h97244 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h9582 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108492 (p5500 p5501 p5502 p5503 p5504 p5505 p6130 : Prop)
    (h9586 : p5500 ∨ (¬ p5501) ∨ (¬ p5502) ∨ (¬ p5503) ∨ (¬ p5504) ∨ (¬ p5505))
    (h14032 : p5502 ∨ p6130)
    : p6130 ∨ (¬ p5503) ∨ p5500 ∨ (¬ p5501) ∨ (¬ p5504) ∨ (¬ p5505) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6130) := (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5500) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5502) := (Or.elim h9586 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h14032 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108494 (p5500 p5501 p5503 p5504 p5505 p6130 : Prop)
    (h108490 : (¬ p5500) ∨ (¬ p5503) ∨ (¬ p6130) ∨ (¬ p5501) ∨ (¬ p5504) ∨ (¬ p5505))
    (h9584 : (¬ p5500) ∨ p5504)
    : (¬ p5500) ∨ (¬ p5503) ∨ (¬ p6130) ∨ (¬ p5501) ∨ (¬ p5505) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5500 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6130 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5504) := (Or.elim h108490 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h9584 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108495 (p5500 p5501 p5503 p5504 p5505 p6130 : Prop)
    (h108492 : p6130 ∨ (¬ p5503) ∨ p5500 ∨ (¬ p5501) ∨ (¬ p5504) ∨ (¬ p5505))
    (h14035 : p5504 ∨ p6130)
    : p6130 ∨ (¬ p5503) ∨ p5500 ∨ (¬ p5501) ∨ (¬ p5505) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6130) := (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5500) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5504) := (Or.elim h108492 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h14035 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108498 (p3868 p5506 p5507 p5508 p5509 p5510 p6131 : Prop)
    (h14043 : (¬ p3868) ∨ (¬ p5507) ∨ (¬ p5508) ∨ (¬ p5509) ∨ (¬ p5510) ∨ (¬ p6131))
    (h9591 : (¬ p5506) ∨ p5510)
    : (¬ p5506) ∨ (¬ p3868) ∨ (¬ p6131) ∨ (¬ p5507) ∨ (¬ p5509) ∨ (¬ p5508) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6131 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5508 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5510) := (Or.elim h14043 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h9591 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108500 (p3868 p5506 p5507 p5508 p5509 p5510 p6131 : Prop)
    (h9592 : (¬ p3868) ∨ p5506 ∨ (¬ p5507) ∨ (¬ p5508) ∨ (¬ p5509) ∨ (¬ p5510))
    (h14042 : p5510 ∨ p6131)
    : p6131 ∨ (¬ p3868) ∨ p5506 ∨ (¬ p5507) ∨ (¬ p5509) ∨ (¬ p5508) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6131) := (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5506) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5508 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5510) := (Or.elim h9592 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h14042 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108512 (p4024 p4435 p5539 p5540 p6140 : Prop)
    (h17147 : (¬ p4024) ∨ (¬ p4435) ∨ (¬ p5539) ∨ (¬ p5540))
    (h14171 : p5539 ∨ p6140)
    : p6140 ∨ (¬ p4435) ∨ (¬ p4024) ∨ (¬ p5540) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6140) := (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5539) := (Or.elim h17147 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h14171 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108515 (p4391 p5544 p5549 : Prop)
    (h9703 : p4391 ∨ (¬ p5544))
    (h66483 : p5544 ∨ p5549)
    : p5549 ∨ p4391 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5549) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4391) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5544) := (Or.elim h9703 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66483 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108523 (p3931 p5549 p5550 p5551 p6143 : Prop)
    (h108056 : (¬ p5549) ∨ (¬ p3931) ∨ (¬ p6143) ∨ (¬ p5550) ∨ (¬ p5551))
    (h9707 : (¬ p5549) ∨ p5550)
    : (¬ p5549) ∨ (¬ p3931) ∨ (¬ p6143) ∨ (¬ p5551) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5549 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5550) := (Or.elim h108056 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h9707 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step108524 (p3931 p5549 p5550 p5551 p6143 : Prop)
    (h108057 : p6143 ∨ (¬ p3931) ∨ p5549 ∨ (¬ p5550) ∨ (¬ p5551))
    (h14253 : p5550 ∨ p6143)
    : p6143 ∨ (¬ p3931) ∨ p5549 ∨ (¬ p5551) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6143) := (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5549) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5550) := (Or.elim h108057 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h14253 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108527 (p5555 p5556 p5561 : Prop)
    (h9719 : (¬ p5555) ∨ p5556)
    (h66484 : p5555 ∨ p5561)
    : p5561 ∨ p5556 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5561) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5556) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5555) := (Or.elim h9719 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66484 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108528 (p5555 p5557 p5561 : Prop)
    (h9720 : (¬ p5555) ∨ p5557)
    (h66484 : p5555 ∨ p5561)
    : p5561 ∨ p5557 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5561) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5557) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5555) := (Or.elim h9720 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66484 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108529 (p5555 p5558 p5561 : Prop)
    (h9721 : (¬ p5555) ∨ p5558)
    (h66484 : p5555 ∨ p5561)
    : p5561 ∨ p5558 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5561) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5558) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5555) := (Or.elim h9721 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66484 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108530 (p5597 p5598 p5599 p5600 p6157 : Prop)
    (h108076 : (¬ p5597) ∨ (¬ p5600) ∨ (¬ p6157) ∨ (¬ p5598) ∨ (¬ p5599))
    (h9863 : (¬ p5597) ∨ p5599)
    : (¬ p5597) ∨ (¬ p5600) ∨ (¬ p6157) ∨ (¬ p5598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5597 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5599) := (Or.elim h108076 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h9863 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step108531 (p5597 p5598 p5599 p5600 p6157 : Prop)
    (h108077 : p6157 ∨ (¬ p5600) ∨ p5597 ∨ (¬ p5598) ∨ (¬ p5599))
    (h14519 : p5599 ∨ p6157)
    : p6157 ∨ (¬ p5600) ∨ p5597 ∨ (¬ p5598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6157) := (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5597) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5599) := (Or.elim h108077 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h14519 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108534 (p4009 p5597 p5603 : Prop)
    (h9870 : p4009 ∨ (¬ p5603))
    (h66488 : p5597 ∨ p5603)
    : p5597 ∨ p4009 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5597) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4009) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5603) := (Or.elim h9870 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66488 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108544 (p5609 p5612 p5615 : Prop)
    (h9881 : (¬ p5609) ∨ p5612)
    (h66489 : p5609 ∨ p5615)
    : p5615 ∨ p5612 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5615) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5612) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5609) := (Or.elim h9881 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66489 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108548 (p4019 p5615 p5616 p6161 : Prop)
    (h108094 : (¬ p5615) ∨ (¬ p4019) ∨ (¬ p6161) ∨ (¬ p5616))
    (h9885 : (¬ p5615) ∨ p5616)
    : (¬ p5615) ∨ (¬ p4019) ∨ (¬ p6161) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5615 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6161 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5616) := (Or.elim h108094 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h9885 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step108549 (p4019 p5615 p5616 p6161 : Prop)
    (h108095 : p6161 ∨ (¬ p4019) ∨ p5615 ∨ (¬ p5616))
    (h14542 : p5616 ∨ p6161)
    : p6161 ∨ (¬ p4019) ∨ p5615 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6161) := (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5615) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5616) := (Or.elim h108095 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h14542 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108550 (p2098 p2598 p4149 p5369 p5615 p5616 p5682 : Prop)
    (h105766 : p5682)
    (h96509 : (¬ p5616) ∨ p4149 ∨ p2098 ∨ (¬ p5369) ∨ (¬ p2598) ∨ (¬ p5682))
    (h9885 : (¬ p5615) ∨ p5616)
    : (¬ p5615) ∨ p4149 ∨ (¬ p2598) ∨ p2098 ∨ (¬ p5369) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5615 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4149) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5682 := h105766;
    let u6 : (¬ p5616) := (Or.elim h96509 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h9885 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108564 (p4075 p5648 p5649 p5650 p6170 : Prop)
    (h108143 : (¬ p5648) ∨ (¬ p4075) ∨ (¬ p6170) ∨ (¬ p5649) ∨ (¬ p5650))
    (h10006 : (¬ p5648) ∨ p5650)
    : (¬ p5648) ∨ (¬ p4075) ∨ (¬ p6170) ∨ (¬ p5649) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5649 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5650) := (Or.elim h108143 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h10006 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step108565 (p4075 p5648 p5649 p5650 p6170 : Prop)
    (h108144 : p6170 ∨ (¬ p4075) ∨ p5648 ∨ (¬ p5649) ∨ (¬ p5650))
    (h14756 : p5650 ∨ p6170)
    : p6170 ∨ (¬ p4075) ∨ p5648 ∨ (¬ p5649) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6170) := (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5648) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5649 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5650) := (Or.elim h108144 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h14756 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108567 (p3546 p4372 p5649 p5650 p6170 : Prop)
    (h14895 : (¬ p3546) ∨ (¬ p4372) ∨ (¬ p5649) ∨ (¬ p5650))
    (h14756 : p5650 ∨ p6170)
    : p6170 ∨ (¬ p4372) ∨ (¬ p5649) ∨ (¬ p3546) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6170) := (fun h => hn (Or.inl h));
    let u1 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5649 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5650) := (Or.elim h14895 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h14756 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108568 (p4139 p5659 p5660 p5661 p6172 : Prop)
    (h108360 : (¬ p5659) ∨ (¬ p5660) ∨ (¬ p6172) ∨ (¬ p4139) ∨ (¬ p5661))
    (h10120 : (¬ p5659) ∨ p5661)
    : (¬ p5659) ∨ (¬ p5660) ∨ (¬ p6172) ∨ (¬ p4139) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5659 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5661) := (Or.elim h108360 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h10120 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step108569 (p4139 p5659 p5660 p5661 p6172 : Prop)
    (h108361 : p6172 ∨ (¬ p5660) ∨ p5659 ∨ (¬ p4139) ∨ (¬ p5661))
    (h15003 : p5661 ∨ p6172)
    : p6172 ∨ (¬ p5660) ∨ p5659 ∨ (¬ p4139) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6172) := (fun h => hn (Or.inl h));
    let u1 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5659) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5661) := (Or.elim h108361 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h15003 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108570 (p2685 p3136 p4333 p5659 p5661 p5740 : Prop)
    (h89026 : (¬ p5740) ∨ (¬ p5661) ∨ (¬ p4333) ∨ p3136 ∨ (¬ p2685))
    (h10120 : (¬ p5659) ∨ p5661)
    : (¬ p5659) ∨ (¬ p5740) ∨ (¬ p4333) ∨ p3136 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5659 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5661) := (Or.elim h89026 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h10120 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108573 (p4129 p5659 p5663 : Prop)
    (h10125 : p4129 ∨ (¬ p5663))
    (h66493 : p5659 ∨ p5663)
    : p5659 ∨ p4129 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5659) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4129) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5663) := (Or.elim h10125 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66493 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108581 (p3641 p3969 p4149 p4158 p5670 p5681 : Prop)
    (h106187 : p4158)
    (h41720 : (¬ p3641) ∨ (¬ p3969) ∨ (¬ p4158) ∨ (¬ p5670) ∨ (¬ p5681))
    (h96156 : p5670 ∨ p4149)
    : p4149 ∨ (¬ p5681) ∨ (¬ p3969) ∨ (¬ p3641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : p5681 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4158 := h106187;
    let u5 : (¬ p5670) := (Or.elim h41720 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96156 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108592 (p5693 p6181 p6182 : Prop)
    (h66634 : (¬ p6181) ∨ (¬ p6182))
    (h15261 : p5693 ∨ p6181)
    : p5693 ∨ (¬ p6182) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5693) := (fun h => hn (Or.inl h));
    let u1 : p6182 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6181) := (Or.elim h66634 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h15261 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108595 (p4181 p5696 p5697 p5698 p6182 : Prop)
    (h108181 : (¬ p5696) ∨ (¬ p6182) ∨ (¬ p5697) ∨ (¬ p5698) ∨ (¬ p4181))
    (h10229 : (¬ p5696) ∨ p5698)
    : (¬ p5696) ∨ (¬ p6182) ∨ (¬ p5697) ∨ (¬ p4181) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6182 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5698) := (Or.elim h108181 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h10229 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step108596 (p4181 p5696 p5697 p5698 p6182 : Prop)
    (h108182 : p6182 ∨ p5696 ∨ (¬ p5697) ∨ (¬ p4181) ∨ (¬ p5698))
    (h15267 : p5698 ∨ p6182)
    : p6182 ∨ p5696 ∨ (¬ p5697) ∨ (¬ p4181) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6182) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5698) := (Or.elim h108182 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h15267 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108606 (p4228 p5717 p6187 : Prop)
    (h108214 : p4228 ∨ (¬ p6187))
    (h15766 : p5717 ∨ p6187)
    : p5717 ∨ p4228 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6187) := (Or.elim h108214 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h15766 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108641 (p5558 p6145 p6146 : Prop)
    (h14265 : p5558 ∨ p6145)
    (h66622 : (¬ p6145) ∨ (¬ p6146))
    : (¬ p6146) ∨ p5558 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5558) := (fun h => hn (Or.inr h));
    let u2 : p6145 := (Or.elim h14265 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66622 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (r0 u0)))))

theorem step108644 (p2761 p3461 p3516 p4063 p4621 p4828 : Prop)
    (h105407 : p4621)
    (h96667 : (¬ p4063) ∨ p3461 ∨ (¬ p4621) ∨ p3516 ∨ (¬ p4828))
    (h102683 : p4828 ∨ (¬ p2761))
    : (¬ p2761) ∨ p3461 ∨ (¬ p4063) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4621 := h105407;
    let u5 : (¬ p4828) := (Or.elim h96667 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h102683 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108649 (p2396 p2761 p4260 p4829 : Prop)
    (h25866 : (¬ p2396) ∨ (¬ p4260) ∨ (¬ p4829))
    (h93759 : p4829 ∨ (¬ p2761))
    : (¬ p2761) ∨ (¬ p2396) ∨ (¬ p4260) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4829) := (Or.elim h25866 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h93759 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108650 (p2761 p3516 p4372 p4829 : Prop)
    (h29718 : (¬ p3516) ∨ (¬ p4372) ∨ (¬ p4829))
    (h93759 : p4829 ∨ (¬ p2761))
    : (¬ p2761) ∨ (¬ p4372) ∨ (¬ p3516) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4829) := (Or.elim h29718 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h93759 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108655 (p2396 p3309 p3399 p3830 p5145 p5362 : Prop)
    (h93345 : (¬ p5362) ∨ p3399 ∨ p2396 ∨ (¬ p5145) ∨ (¬ p3830))
    (h96289 : p5145 ∨ (¬ p3309))
    : (¬ p3309) ∨ (¬ p3830) ∨ (¬ p5362) ∨ p3399 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5145) := (Or.elim h93345 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96289 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108656 (p2177 p3309 p3399 p3449 p5145 p5307 : Prop)
    (h93372 : p3399 ∨ (¬ p3449) ∨ (¬ p5145) ∨ (¬ p5307) ∨ p2177)
    (h96289 : p5145 ∨ (¬ p3309))
    : (¬ p3309) ∨ (¬ p5307) ∨ p2177 ∨ p3399 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5145) := (Or.elim h93372 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96289 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108664 (p2449 p2696 p2742 p2839 p2996 p3105 p3461 p4322 p4394 p4625 p5252 : Prop)
    (h106455 : p4625)
    (h84539 : (¬ p2742) ∨ (¬ p4322) ∨ (¬ p4625) ∨ (¬ p2449) ∨ p2839 ∨ p3105 ∨ p2996 ∨ (¬ p5252) ∨ (¬ p4394) ∨ (¬ p2696))
    (h102361 : p5252 ∨ (¬ p3461))
    : (¬ p3461) ∨ p3105 ∨ (¬ p4322) ∨ p2996 ∨ (¬ p2449) ∨ (¬ p2696) ∨ p2839 ∨ (¬ p2742) ∨ (¬ p4394) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4394 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4625 := h106455;
    let u10 : (¬ p5252) := (Or.elim h84539 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u5))))))))))))))))))));
    (Or.elim h102361 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108671 (p2177 p2241 p2717 p2750 p2753 p3425 p3449 p4149 p4712 p5074 p5508 p5600 p5674 : Prop)
    (h106345 : p2750)
    (h105422 : p4712)
    (h89210 : (¬ p5674) ∨ (¬ p5600) ∨ (¬ p5508) ∨ p3425 ∨ (¬ p2750) ∨ (¬ p2717) ∨ (¬ p5074) ∨ (¬ p2753) ∨ p2177 ∨ (¬ p2241) ∨ p3449 ∨ (¬ p4712))
    (h102607 : p5674 ∨ (¬ p4149))
    : (¬ p4149) ∨ (¬ p5508) ∨ p3449 ∨ p3425 ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p5600) ∨ (¬ p2241) ∨ (¬ p5074) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5508 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5074 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2750 := h106345;
    let u11 : p4712 := h105422;
    let u12 : (¬ p5674) := (Or.elim h89210 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u9 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u2 q10))) (fun r10 => (False.elim (r10 u11))))))))))))))))))))))));
    (Or.elim h102607 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108673 (p3888 p3893 p5517 p5518 p5519 p6134 : Prop)
    (h108021 : (¬ p5517) ∨ (¬ p3888) ∨ (¬ p3893) ∨ (¬ p5519) ∨ (¬ p5518) ∨ (¬ p6134))
    (h9627 : p3893 ∨ (¬ p5517))
    : (¬ p5517) ∨ (¬ p3888) ∨ (¬ p5519) ∨ (¬ p5518) ∨ (¬ p6134) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5517 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p6134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3893) := (Or.elim h108021 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h9627 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108674 (p3888 p3893 p5517 p5518 p5519 p6134 : Prop)
    (h108022 : p6134 ∨ p5517 ∨ (¬ p3888) ∨ (¬ p3893) ∨ (¬ p5519) ∨ (¬ p5518))
    (h14119 : p3893 ∨ p6134)
    : p6134 ∨ p5517 ∨ (¬ p3888) ∨ (¬ p5519) ∨ (¬ p5518) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5517) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3893) := (Or.elim h108022 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h14119 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108687 (p2509 p3453 p4370 p4683 p4684 p4685 p5866 : Prop)
    (h12192 : (¬ p2509) ∨ (¬ p3453) ∨ (¬ p4370) ∨ (¬ p4684) ∨ (¬ p4685) ∨ (¬ p5866))
    (h7551 : (¬ p4683) ∨ p4684)
    : (¬ p4683) ∨ (¬ p5866) ∨ (¬ p4370) ∨ (¬ p3453) ∨ (¬ p2509) ∨ (¬ p4685) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4683 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4684) := (Or.elim h12192 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h7551 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u6 r0)))))

theorem step108690 (p2509 p3453 p4370 p4683 p4684 p4685 p5866 : Prop)
    (h7553 : (¬ p2509) ∨ (¬ p3453) ∨ (¬ p4370) ∨ p4683 ∨ (¬ p4684) ∨ (¬ p4685))
    (h12188 : p4684 ∨ p5866)
    : p5866 ∨ p4683 ∨ (¬ p4370) ∨ (¬ p3453) ∨ (¬ p2509) ∨ (¬ p4685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5866) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4683) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4684) := (Or.elim h7553 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h12188 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108691 (p4380 p5089 p5092 : Prop)
    (h8569 : p4380 ∨ (¬ p5089))
    (h66432 : p5089 ∨ p5092)
    : p5092 ∨ p4380 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5092) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4380) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5089) := (Or.elim h8569 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66432 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108692 (p4323 p5089 p5092 : Prop)
    (h8570 : p4323 ∨ (¬ p5089))
    (h66432 : p5089 ∨ p5092)
    : p5092 ∨ p4323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5092) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4323) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5089) := (Or.elim h8570 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66432 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108693 (p4032 p5089 p5092 : Prop)
    (h8571 : p4032 ∨ (¬ p5089))
    (h66432 : p5089 ∨ p5092)
    : p5092 ∨ p4032 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5092) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4032) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5089) := (Or.elim h8571 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66432 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108698 (p5157 p5160 p5163 : Prop)
    (h8741 : (¬ p5157) ∨ p5160)
    (h66442 : p5157 ∨ p5163)
    : p5163 ∨ p5160 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5163) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5160) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5157) := (Or.elim h8741 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66442 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108699 (p5157 p5158 p5163 : Prop)
    (h8739 : (¬ p5157) ∨ p5158)
    (h66442 : p5157 ∨ p5163)
    : p5163 ∨ p5158 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5163) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5158) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5157) := (Or.elim h8739 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66442 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108700 (p5157 p5159 p5163 : Prop)
    (h8740 : (¬ p5157) ∨ p5159)
    (h66442 : p5157 ∨ p5163)
    : p5163 ∨ p5159 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5163) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5159) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5157) := (Or.elim h8740 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66442 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108702 (p5160 p6028 p6029 : Prop)
    (h13163 : p5160 ∨ p6028)
    (h66583 : (¬ p6028) ∨ (¬ p6029))
    : (¬ p6029) ∨ p5160 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6029 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5160) := (fun h => hn (Or.inr h));
    let u2 : p6028 := (Or.elim h13163 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66583 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (r0 u0)))))

theorem step108705 (p3346 p5180 p5185 : Prop)
    (h8776 : p3346 ∨ (¬ p5180))
    (h66444 : p5180 ∨ p5185)
    : p5185 ∨ p3346 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5185) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3346) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5180) := (Or.elim h8776 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66444 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108706 (p5180 p5181 p5185 : Prop)
    (h8774 : (¬ p5180) ∨ p5181)
    (h66444 : p5180 ∨ p5185)
    : p5185 ∨ p5181 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5185) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5181) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5180) := (Or.elim h8774 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66444 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108707 (p5180 p5182 p5185 : Prop)
    (h8775 : (¬ p5180) ∨ p5182)
    (h66444 : p5180 ∨ p5185)
    : p5185 ∨ p5182 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5185) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5182) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5180) := (Or.elim h8775 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66444 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108709 (p3346 p6034 p6035 : Prop)
    (h13198 : p3346 ∨ p6034)
    (h66585 : (¬ p6034) ∨ (¬ p6035))
    : (¬ p6035) ∨ p3346 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6035 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3346) := (fun h => hn (Or.inr h));
    let u2 : p6034 := (Or.elim h13198 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66585 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (r0 u0)))))

theorem step108712 (p5281 p5282 p5287 : Prop)
    (h9000 : (¬ p5281) ∨ p5282)
    (h66456 : p5281 ∨ p5287)
    : p5287 ∨ p5282 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5287) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5282) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5281) := (Or.elim h9000 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66456 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108713 (p5281 p5283 p5287 : Prop)
    (h9001 : (¬ p5281) ∨ p5283)
    (h66456 : p5281 ∨ p5287)
    : p5287 ∨ p5283 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5287) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5283) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5281) := (Or.elim h9001 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66456 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108714 (p5281 p5284 p5287 : Prop)
    (h9002 : (¬ p5281) ∨ p5284)
    (h66456 : p5281 ∨ p5287)
    : p5287 ∨ p5284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5287) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5284) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5281) := (Or.elim h9002 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66456 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108720 (p2295 p2608 p3707 p3830 p5274 p5282 p5283 p5287 : Prop)
    (h75743 : (¬ p5283) ∨ (¬ p3707) ∨ (¬ p2295) ∨ (¬ p3830) ∨ p2608 ∨ (¬ p5282) ∨ (¬ p5274))
    (h108712 : p5287 ∨ p5282)
    : p5287 ∨ (¬ p3830) ∨ p2608 ∨ (¬ p3707) ∨ (¬ p5274) ∨ (¬ p5283) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5287) := (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5282) := (Or.elim h75743 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u4))))))))))))));
    (Or.elim h108712 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u7 r0)))))

theorem step108725 (p4398 p5348 p5351 : Prop)
    (h9190 : p4398 ∨ (¬ p5348))
    (h66463 : p5348 ∨ p5351)
    : p5351 ∨ p4398 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5351) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4398) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5348) := (Or.elim h9190 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66463 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108726 (p4234 p5348 p5351 : Prop)
    (h9191 : p4234 ∨ (¬ p5348))
    (h66463 : p5348 ∨ p5351)
    : p5351 ∨ p4234 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5351) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4234) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5348) := (Or.elim h9191 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66463 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108727 (p4232 p5348 p5351 : Prop)
    (h9192 : p4232 ∨ (¬ p5348))
    (h66463 : p5348 ∨ p5351)
    : p5351 ∨ p4232 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5351) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4232) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5348) := (Or.elim h9192 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66463 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108736 (p4322 p5396 p5401 : Prop)
    (h9308 : p4322 ∨ (¬ p5396))
    (h66468 : p5396 ∨ p5401)
    : p5401 ∨ p4322 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5401) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4322) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5396) := (Or.elim h9308 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66468 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108737 (p5396 p5400 p5401 : Prop)
    (h9310 : (¬ p5396) ∨ p5400)
    (h66468 : p5396 ∨ p5401)
    : p5401 ∨ p5400 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5401) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5400) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5396) := (Or.elim h9310 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66468 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108743 (p3276 p4952 p5401 p5402 p5403 : Prop)
    (h96568 : p3276 ∨ (¬ p5403) ∨ (¬ p4952) ∨ (¬ p5402))
    (h9313 : (¬ p5401) ∨ p5403)
    : (¬ p5401) ∨ p3276 ∨ (¬ p5402) ∨ (¬ p4952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5401 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5403) := (Or.elim h96568 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h9313 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step108747 (p5500 p5501 p5503 p5505 p6130 : Prop)
    (h108494 : (¬ p5500) ∨ (¬ p5503) ∨ (¬ p6130) ∨ (¬ p5501) ∨ (¬ p5505))
    (h9585 : (¬ p5500) ∨ p5505)
    : (¬ p5500) ∨ (¬ p5503) ∨ (¬ p6130) ∨ (¬ p5501) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5500 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6130 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5505) := (Or.elim h108494 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h9585 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step108748 (p5500 p5501 p5503 p5505 p6130 : Prop)
    (h108495 : p6130 ∨ (¬ p5503) ∨ p5500 ∨ (¬ p5501) ∨ (¬ p5505))
    (h14036 : p5505 ∨ p6130)
    : p6130 ∨ (¬ p5503) ∨ p5500 ∨ (¬ p5501) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6130) := (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5500) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5505) := (Or.elim h108495 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h14036 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108753 (p3868 p5506 p5507 p5508 p5509 p6131 : Prop)
    (h108498 : (¬ p5506) ∨ (¬ p3868) ∨ (¬ p6131) ∨ (¬ p5507) ∨ (¬ p5509) ∨ (¬ p5508))
    (h9587 : (¬ p5506) ∨ p5507)
    : (¬ p5506) ∨ (¬ p3868) ∨ (¬ p6131) ∨ (¬ p5509) ∨ (¬ p5508) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6131 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5508 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5507) := (Or.elim h108498 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h9587 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108754 (p3868 p5506 p5507 p5508 p5509 p6131 : Prop)
    (h108500 : p6131 ∨ (¬ p3868) ∨ p5506 ∨ (¬ p5507) ∨ (¬ p5509) ∨ (¬ p5508))
    (h14038 : p5507 ∨ p6131)
    : p6131 ∨ (¬ p3868) ∨ p5506 ∨ (¬ p5509) ∨ (¬ p5508) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6131) := (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5506) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5508 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5507) := (Or.elim h108500 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h14038 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108756 (p2177 p2493 p3801 p4260 p5506 p5507 : Prop)
    (h96531 : (¬ p3801) ∨ (¬ p4260) ∨ (¬ p2177) ∨ (¬ p5507) ∨ p2493)
    (h9587 : (¬ p5506) ∨ p5507)
    : (¬ p5506) ∨ (¬ p3801) ∨ (¬ p4260) ∨ (¬ p2177) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3801 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5507) := (Or.elim h96531 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h9587 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step108759 (p3868 p5506 p5508 p5509 p6131 : Prop)
    (h108753 : (¬ p5506) ∨ (¬ p3868) ∨ (¬ p6131) ∨ (¬ p5509) ∨ (¬ p5508))
    (h9588 : (¬ p5506) ∨ p5508)
    : (¬ p5506) ∨ (¬ p3868) ∨ (¬ p6131) ∨ (¬ p5509) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6131 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5508) := (Or.elim h108753 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h9588 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step108760 (p3868 p5506 p5508 p5509 p6131 : Prop)
    (h108754 : p6131 ∨ (¬ p3868) ∨ p5506 ∨ (¬ p5509) ∨ (¬ p5508))
    (h14039 : p5508 ∨ p6131)
    : p6131 ∨ (¬ p3868) ∨ p5506 ∨ (¬ p5509) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6131) := (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5506) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5508) := (Or.elim h108754 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h14039 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108762 (p2177 p2241 p2717 p2753 p3425 p3449 p4149 p5074 p5506 p5508 p5600 : Prop)
    (h108671 : (¬ p4149) ∨ (¬ p5508) ∨ p3449 ∨ p3425 ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p5600) ∨ (¬ p2241) ∨ (¬ p5074) ∨ p2177)
    (h9588 : (¬ p5506) ∨ p5508)
    : (¬ p5506) ∨ (¬ p4149) ∨ p3449 ∨ p3425 ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p5600) ∨ (¬ p2241) ∨ (¬ p5074) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5074 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p5508) := (Or.elim h108671 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (u9 r8))))))))))))))))))));
    (Or.elim h9588 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u10 r0)))))

theorem step108765 (p5512 p5514 p5517 : Prop)
    (h9622 : (¬ p5512) ∨ p5514)
    (h66480 : p5512 ∨ p5517)
    : p5517 ∨ p5514 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5517) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5514) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5512) := (Or.elim h9622 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66480 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108784 (p4329 p5533 p5538 : Prop)
    (h9661 : p4329 ∨ (¬ p5533))
    (h66482 : p5533 ∨ p5538)
    : p5538 ∨ p4329 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5538) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4329) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5533) := (Or.elim h9661 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66482 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108789 (p4024 p4435 p5540 p6140 : Prop)
    (h108512 : p6140 ∨ (¬ p4435) ∨ (¬ p4024) ∨ (¬ p5540))
    (h14172 : p5540 ∨ p6140)
    : p6140 ∨ (¬ p4435) ∨ (¬ p4024) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6140) := (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5540) := (Or.elim h108512 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h14172 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108792 (p3914 p6139 p6140 : Prop)
    (h14173 : p3914 ∨ p6140)
    (h66620 : (¬ p6139) ∨ (¬ p6140))
    : (¬ p6139) ∨ p3914 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6139 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3914) := (fun h => hn (Or.inr h));
    let u2 : p6140 := (Or.elim h14173 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66620 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u2)))))

theorem step108794 (p4024 p4435 p6139 p6140 : Prop)
    (h108789 : p6140 ∨ (¬ p4435) ∨ (¬ p4024))
    (h66620 : (¬ p6139) ∨ (¬ p6140))
    : (¬ p6139) ∨ (¬ p4435) ∨ (¬ p4024) :=
  Classical.byContradiction (fun hn =>
    let u0 : p6139 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p6140 := (Or.elim h108789 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h66620 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step108796 (p3931 p5549 p5551 p6143 : Prop)
    (h108523 : (¬ p5549) ∨ (¬ p3931) ∨ (¬ p6143) ∨ (¬ p5551))
    (h9708 : (¬ p5549) ∨ p5551)
    : (¬ p5549) ∨ (¬ p3931) ∨ (¬ p6143) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5549 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5551) := (Or.elim h108523 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h9708 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step108798 (p3931 p5549 p5551 p6143 : Prop)
    (h108524 : p6143 ∨ (¬ p3931) ∨ p5549 ∨ (¬ p5551))
    (h14254 : p5551 ∨ p6143)
    : p6143 ∨ (¬ p3931) ∨ p5549 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6143) := (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5549) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5551) := (Or.elim h108524 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h14254 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108800 (p3969 p5567 p5571 : Prop)
    (h9797 : p3969 ∨ (¬ p5571))
    (h66485 : p5567 ∨ p5571)
    : p5567 ∨ p3969 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5567) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3969) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5571) := (Or.elim h9797 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66485 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108804 (p3969 p6148 p6149 : Prop)
    (h14398 : p3969 ∨ p6149)
    (h66623 : (¬ p6148) ∨ (¬ p6149))
    : (¬ p6148) ∨ p3969 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6148 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3969) := (fun h => hn (Or.inr h));
    let u2 : p6149 := (Or.elim h14398 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66623 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u2)))))

theorem step108813 (p4309 p5589 p5593 : Prop)
    (h9836 : p4309 ∨ (¬ p5589))
    (h66487 : p5589 ∨ p5593)
    : p5593 ∨ p4309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5593) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4309) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5589) := (Or.elim h9836 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66487 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108814 (p4310 p5589 p5593 : Prop)
    (h9837 : p4310 ∨ (¬ p5589))
    (h66487 : p5589 ∨ p5593)
    : p5593 ∨ p4310 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5593) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4310) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5589) := (Or.elim h9837 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66487 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108815 (p5589 p5590 p5593 : Prop)
    (h9838 : (¬ p5589) ∨ p5590)
    (h66487 : p5589 ∨ p5593)
    : p5593 ∨ p5590 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5593) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5590) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5589) := (Or.elim h9838 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66487 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108819 (p5590 p6154 p6155 : Prop)
    (h14475 : p5590 ∨ p6154)
    (h66625 : (¬ p6154) ∨ (¬ p6155))
    : (¬ p6155) ∨ p5590 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6155 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5590) := (fun h => hn (Or.inr h));
    let u2 : p6154 := (Or.elim h14475 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66625 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (r0 u0)))))

theorem step108851 (p4423 p5726 p5731 : Prop)
    (h10527 : p4423 ∨ (¬ p5726))
    (h66499 : p5726 ∨ p5731)
    : p5731 ∨ p4423 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5731) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4423) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5726) := (Or.elim h10527 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66499 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108859 (p4253 p6190 p6191 : Prop)
    (h16038 : p4253 ∨ p6191)
    (h66637 : (¬ p6190) ∨ (¬ p6191))
    : (¬ p6190) ∨ p4253 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4253) := (fun h => hn (Or.inr h));
    let u2 : p6191 := (Or.elim h16038 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66637 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u2)))))

theorem step108864 (p5284 p6070 p6071 : Prop)
    (h13449 : p5284 ∨ p6070)
    (h66597 : (¬ p6070) ∨ (¬ p6071))
    : (¬ p6071) ∨ p5284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6071 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5284) := (fun h => hn (Or.inr h));
    let u2 : p6070 := (Or.elim h13449 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66597 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (r0 u0)))))

theorem step108869 (p4322 p6106 p6107 : Prop)
    (h13783 : p4322 ∨ p6106)
    (h66609 : (¬ p6106) ∨ (¬ p6107))
    : (¬ p6107) ∨ p4322 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6107 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4322) := (fun h => hn (Or.inr h));
    let u2 : p6106 := (Or.elim h13783 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66609 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (r0 u0)))))

theorem step108875 (p4442 p6169 p6170 : Prop)
    (h14750 : p4442 ∨ p6169)
    (h66630 : (¬ p6169) ∨ (¬ p6170))
    : (¬ p6170) ∨ p4442 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6170 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4442) := (fun h => hn (Or.inr h));
    let u2 : p6169 := (Or.elim h14750 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66630 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (r0 u0)))))

theorem step108893 (p2641 p3038 p3093 p3516 p3631 p4760 p5206 : Prop)
    (h76752 : (¬ p3631) ∨ p3516 ∨ (¬ p3093) ∨ (¬ p4760) ∨ (¬ p3038) ∨ (¬ p5206))
    (h96020 : p4760 ∨ (¬ p2641))
    : (¬ p2641) ∨ (¬ p3038) ∨ p3516 ∨ (¬ p3631) ∨ (¬ p5206) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4760) := (Or.elim h76752 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96020 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108894 (p2641 p2934 p3093 p3516 p3631 p4281 p4760 p5206 : Prop)
    (h76273 : (¬ p3631) ∨ (¬ p5206) ∨ (¬ p3093) ∨ (¬ p4281) ∨ p3516 ∨ (¬ p4760) ∨ (¬ p2934))
    (h96020 : p4760 ∨ (¬ p2641))
    : (¬ p2641) ∨ (¬ p3631) ∨ (¬ p3093) ∨ (¬ p5206) ∨ (¬ p4281) ∨ (¬ p2934) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2934 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4760) := (Or.elim h76273 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h96020 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108896 (p2246 p2440 p2641 p2651 p2982 p3073 p3093 p3449 p4760 : Prop)
    (h107549 : (¬ p2246) ∨ p2440 ∨ (¬ p3093) ∨ (¬ p2982) ∨ p3073 ∨ p3449 ∨ (¬ p4760) ∨ (¬ p2651))
    (h96020 : p4760 ∨ (¬ p2641))
    : (¬ p2641) ∨ p3073 ∨ (¬ p3093) ∨ p3449 ∨ p2440 ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4760) := (Or.elim h107549 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (r6 u5))))))))))))))));
    (Or.elim h96020 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108901 (p2493 p2573 p2870 p2982 p3051 p3105 p3193 p4079 p4950 : Prop)
    (h99297 : p3193 ∨ p3051 ∨ (¬ p2573) ∨ p2493 ∨ (¬ p2870) ∨ p3105 ∨ (¬ p4079) ∨ (¬ p4950))
    (h96345 : p4950 ∨ p2982)
    : p2982 ∨ p3105 ∨ (¬ p2573) ∨ p3051 ∨ (¬ p2870) ∨ p2493 ∨ p3193 ∨ (¬ p4079) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4950) := (Or.elim h99297 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => r6))))))))))))));
    (Or.elim h96345 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108903 (p2145 p2220 p2573 p2982 p3115 p3156 p3333 p3362 p3422 p4950 : Prop)
    (h92511 : (¬ p3156) ∨ p3115 ∨ (¬ p3333) ∨ p2220 ∨ (¬ p2145) ∨ (¬ p3362) ∨ p3422 ∨ (¬ p4950) ∨ (¬ p2573))
    (h96345 : p4950 ∨ p2982)
    : p2982 ∨ (¬ p3362) ∨ p3115 ∨ (¬ p2573) ∨ p3422 ∨ (¬ p3156) ∨ p2220 ∨ (¬ p3333) ∨ (¬ p2145) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4950) := (Or.elim h92511 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u3))))))))))))))))));
    (Or.elim h96345 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108910 (p2156 p2241 p2727 p3125 p3276 p3461 p3892 p4521 p5133 : Prop)
    (h96640 : (¬ p3892) ∨ (¬ p5133) ∨ (¬ p2156) ∨ p2727 ∨ p2241 ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4521))
    (h102657 : p5133 ∨ (¬ p3276))
    : (¬ p3276) ∨ (¬ p3461) ∨ (¬ p3125) ∨ (¬ p2156) ∨ p2241 ∨ p2727 ∨ (¬ p3892) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3892 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5133) := (Or.elim h96640 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h102657 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108914 (p2210 p3830 p4942 p5486 p5487 : Prop)
    (h38000 : (¬ p2210) ∨ (¬ p4942) ∨ (¬ p5486) ∨ (¬ p5487))
    (h96231 : p5486 ∨ p3830)
    : p3830 ∨ (¬ p5487) ∨ (¬ p2210) ∨ (¬ p4942) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p5487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4942 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5486) := (Or.elim h38000 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h96231 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108915 (p3093 p3830 p5153 p5486 p5487 : Prop)
    (h14961 : (¬ p3093) ∨ (¬ p5153) ∨ (¬ p5486) ∨ (¬ p5487))
    (h96231 : p5486 ∨ p3830)
    : p3830 ∨ (¬ p5153) ∨ (¬ p5487) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p5153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5486) := (Or.elim h14961 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96231 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108917 (p2608 p3707 p3773 p3830 p5329 p5486 : Prop)
    (h105498 : p5329)
    (h50220 : (¬ p2608) ∨ (¬ p3707) ∨ (¬ p3773) ∨ (¬ p5329) ∨ (¬ p5486))
    (h96231 : p5486 ∨ p3830)
    : p3830 ∨ (¬ p3773) ∨ (¬ p2608) ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5329 := h105498;
    let u5 : (¬ p5486) := (Or.elim h50220 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96231 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108921 (p2922 p2936 p3201 p3631 p4636 p5160 : Prop)
    (h42615 : (¬ p2936) ∨ (¬ p3201) ∨ (¬ p3631) ∨ (¬ p4636) ∨ (¬ p5160))
    (h96901 : p2936 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p3631) ∨ (¬ p3201) ∨ (¬ p5160) ∨ (¬ p4636) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2936) := (Or.elim h42615 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96901 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108923 (p2911 p2922 p2936 p3399 p3449 p5307 : Prop)
    (h93374 : (¬ p5307) ∨ p3399 ∨ (¬ p2936) ∨ (¬ p3449) ∨ p2911)
    (h96901 : p2936 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p5307) ∨ p3399 ∨ (¬ p3449) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2936) := (Or.elim h93374 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96901 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108924 (p2341 p2911 p2922 p2936 p3516 p3631 : Prop)
    (h95937 : p3516 ∨ (¬ p3631) ∨ (¬ p2936) ∨ (¬ p2341) ∨ p2911)
    (h96901 : p2936 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p3631) ∨ p2911 ∨ p3516 ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2936) := (Or.elim h95937 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96901 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108925 (p2417 p2922 p2936 p3399 p3830 p5362 : Prop)
    (h100093 : (¬ p5362) ∨ p3399 ∨ (¬ p3830) ∨ p2417 ∨ (¬ p2936))
    (h96901 : p2936 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p5362) ∨ p2417 ∨ p3399 ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2936) := (Or.elim h100093 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => r3))))))));
    (Or.elim h96901 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step108929 (p3845 p3848 p3852 : Prop)
    (h94414 : p3848 ∨ (¬ p3845))
    (h67255 : p3845 ∨ p3852)
    : p3852 ∨ p3848 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3852) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3848) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3845) := (Or.elim h94414 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h67255 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108930 (p3845 p3846 p3852 : Prop)
    (h102515 : p3846 ∨ (¬ p3845))
    (h67255 : p3845 ∨ p3852)
    : p3852 ∨ p3846 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3852) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3846) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3845) := (Or.elim h102515 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h67255 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108931 (p3845 p3847 p3852 : Prop)
    (h102792 : p3847 ∨ (¬ p3845))
    (h67255 : p3845 ∨ p3852)
    : p3852 ∨ p3847 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3852) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3847) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3845) := (Or.elim h102792 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h67255 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108934 (p3599 p3670 p3707 p4029 : Prop)
    (h107850 : p3670 ∨ (¬ p3707) ∨ (¬ p4029))
    (h102480 : p4029 ∨ p3599)
    : p3599 ∨ p3670 ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4029) := (Or.elim h107850 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h102480 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108936 (p2396 p3425 p3599 p3619 p4029 p4477 p5362 : Prop)
    (h94316 : (¬ p3619) ∨ (¬ p4029) ∨ (¬ p3425) ∨ p2396 ∨ (¬ p4477) ∨ (¬ p5362))
    (h102480 : p4029 ∨ p3599)
    : p3599 ∨ (¬ p5362) ∨ (¬ p3619) ∨ p2396 ∨ (¬ p3425) ∨ (¬ p4477) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : p5362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4029) := (Or.elim h94316 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h102480 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108939 (p2230 p2427 p2608 p3519 p3599 p3670 p3830 p4029 p4129 p4376 p4826 : Prop)
    (h106320 : p4376)
    (h105444 : p4826)
    (h94283 : (¬ p4129) ∨ p3670 ∨ (¬ p4826) ∨ (¬ p3519) ∨ (¬ p2427) ∨ (¬ p2608) ∨ p3830 ∨ (¬ p2230) ∨ (¬ p4376) ∨ (¬ p4029))
    (h102480 : p4029 ∨ p3599)
    : p3599 ∨ (¬ p2230) ∨ (¬ p2427) ∨ p3830 ∨ (¬ p3519) ∨ p3670 ∨ (¬ p4129) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p4826 := h105444;
    let u10 : (¬ p4029) := (Or.elim h94283 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => r8))))))))))))))))));
    (Or.elim h102480 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108945 (p2088 p2352 p2383 p3564 p4345 p4614 : Prop)
    (h96682 : (¬ p3564) ∨ p2088 ∨ (¬ p4345) ∨ (¬ p4614) ∨ p2352)
    (h102691 : p4614 ∨ p2383)
    : p2383 ∨ (¬ p3564) ∨ p2352 ∨ (¬ p4345) ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2383) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4614) := (Or.elim h96682 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h102691 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108950 (p4683 p4686 p4687 : Prop)
    (h7554 : (¬ p4686) ∨ p4687)
    (h66365 : p4683 ∨ p4686)
    : p4683 ∨ p4687 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4683) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4687) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4686) := (Or.elim h7554 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66365 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108951 (p4683 p4686 p4688 : Prop)
    (h7555 : (¬ p4686) ∨ p4688)
    (h66365 : p4683 ∨ p4686)
    : p4683 ∨ p4688 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4683) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4688) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4686) := (Or.elim h7555 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66365 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108952 (p2518 p4683 p4686 : Prop)
    (h7556 : p2518 ∨ (¬ p4686))
    (h66365 : p4683 ∨ p4686)
    : p4683 ∨ p2518 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4683) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2518) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4686) := (Or.elim h7556 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66365 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108953 (p4683 p4686 p4690 : Prop)
    (h7558 : (¬ p4686) ∨ p4690)
    (h66365 : p4683 ∨ p4686)
    : p4683 ∨ p4690 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4683) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4690) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4686) := (Or.elim h7558 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66365 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108964 (p2396 p2761 p3276 p3951 p4260 p4824 p4947 : Prop)
    (h106536 : p3951)
    (h62633 : (¬ p2396) ∨ (¬ p3276) ∨ (¬ p3951) ∨ (¬ p4260) ∨ (¬ p4824) ∨ (¬ p4947))
    (h96386 : p4824 ∨ p2761)
    : p2761 ∨ (¬ p4260) ∨ (¬ p3276) ∨ (¬ p2396) ∨ (¬ p4947) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3951 := h106536;
    let u6 : (¬ p4824) := (Or.elim h62633 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96386 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108967 (p4318 p4992 p4996 : Prop)
    (h8338 : p4318 ∨ (¬ p4996))
    (h66420 : p4992 ∨ p4996)
    : p4992 ∨ p4318 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4318) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4996) := (Or.elim h8338 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66420 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108968 (p4317 p4992 p4996 : Prop)
    (h8339 : p4317 ∨ (¬ p4996))
    (h66420 : p4992 ∨ p4996)
    : p4992 ∨ p4317 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4317) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4996) := (Or.elim h8339 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66420 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108969 (p3063 p4992 p4996 : Prop)
    (h8340 : p3063 ∨ (¬ p4996))
    (h66420 : p4992 ∨ p4996)
    : p4992 ∨ p3063 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3063) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4996) := (Or.elim h8340 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66420 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108970 (p4992 p4996 p4998 : Prop)
    (h8342 : (¬ p4996) ∨ p4998)
    (h66420 : p4992 ∨ p4996)
    : p4992 ∨ p4998 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4998) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4996) := (Or.elim h8342 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66420 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step108972 (p4318 p5971 p5972 : Prop)
    (h12823 : p4318 ∨ p5972)
    (h66564 : (¬ p5971) ∨ (¬ p5972))
    : (¬ p5971) ∨ p4318 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5971 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4318) := (fun h => hn (Or.inr h));
    let u2 : p5972 := (Or.elim h12823 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66564 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u2)))))

theorem step108974 (p3063 p5971 p5972 : Prop)
    (h12825 : p3063 ∨ p5972)
    (h66564 : (¬ p5971) ∨ (¬ p5972))
    : (¬ p5971) ∨ p3063 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5971 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3063) := (fun h => hn (Or.inr h));
    let u2 : p5972 := (Or.elim h12825 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66564 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u2)))))

theorem step108977 (p2839 p3105 p3599 p5025 : Prop)
    (h32945 : p2839 ∨ (¬ p3599) ∨ (¬ p5025))
    (h96327 : p5025 ∨ p3105)
    : p3105 ∨ (¬ p3599) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3105) := (fun h => hn (Or.inl h));
    let u1 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5025) := (Or.elim h32945 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h96327 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108986 (p2363 p2761 p3266 p3516 p5117 p5580 : Prop)
    (h50016 : (¬ p2363) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p5117) ∨ (¬ p5580))
    (h96294 : p5117 ∨ p3266)
    : p3266 ∨ (¬ p3516) ∨ (¬ p5580) ∨ (¬ p2761) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5117) := (Or.elim h50016 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96294 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108987 (p2459 p3266 p3461 p4604 p5117 p5558 : Prop)
    (h106293 : p4604)
    (h48614 : (¬ p2459) ∨ (¬ p3461) ∨ (¬ p4604) ∨ (¬ p5117) ∨ (¬ p5558))
    (h96294 : p5117 ∨ p3266)
    : p3266 ∨ (¬ p3461) ∨ (¬ p5558) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4604 := h106293;
    let u5 : (¬ p5117) := (Or.elim h48614 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96294 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108990 (p2132 p2331 p2619 p3266 p3506 p4421 p4786 p5117 p5568 : Prop)
    (h106425 : p4786)
    (h84805 : (¬ p5568) ∨ (¬ p4421) ∨ (¬ p5117) ∨ p2619 ∨ p2132 ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p4786))
    (h96294 : p5117 ∨ p3266)
    : p3266 ∨ (¬ p5568) ∨ (¬ p3506) ∨ p2132 ∨ (¬ p2331) ∨ p2619 ∨ (¬ p4421) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    let u8 : (¬ p5117) := (Or.elim h84805 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h96294 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108991 (p2331 p2717 p3266 p3425 p3506 p4421 p4786 p5117 p5558 : Prop)
    (h106425 : p4786)
    (h88675 : (¬ p5558) ∨ (¬ p5117) ∨ p2717 ∨ (¬ p3506) ∨ (¬ p4421) ∨ (¬ p2331) ∨ (¬ p3425) ∨ (¬ p4786))
    (h96294 : p5117 ∨ p3266)
    : p3266 ∨ (¬ p5558) ∨ (¬ p3506) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p2331) ∨ (¬ p4421) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    let u8 : (¬ p5117) := (Or.elim h88675 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h96294 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step108997 (p3323 p3461 p3984 p5247 p5514 : Prop)
    (h87603 : (¬ p5247) ∨ p5514 ∨ p3323 ∨ (¬ p3984))
    (h93207 : p5247 ∨ p3461)
    : p3461 ∨ p5514 ∨ (¬ p3984) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5514) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5247) := (Or.elim h87603 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h93207 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109000 (p3917 p5263 p5268 : Prop)
    (h8962 : p3917 ∨ (¬ p5263))
    (h66454 : p5263 ∨ p5268)
    : p5268 ∨ p3917 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5268) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3917) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5263) := (Or.elim h8962 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66454 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109001 (p5263 p5264 p5268 : Prop)
    (h8960 : (¬ p5263) ∨ p5264)
    (h66454 : p5263 ∨ p5268)
    : p5268 ∨ p5264 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5268) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5264) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5263) := (Or.elim h8960 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66454 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109002 (p5263 p5265 p5268 : Prop)
    (h8961 : (¬ p5263) ∨ p5265)
    (h66454 : p5263 ∨ p5268)
    : p5268 ∨ p5265 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5268) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5265) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5263) := (Or.elim h8961 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66454 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109004 (p2144 p2651 p3016 p3212 p3564 p3670 p3680 p5263 p5268 : Prop)
    (h108420 : (¬ p5263) ∨ (¬ p3680) ∨ p3016 ∨ p3564 ∨ (¬ p3212) ∨ p3670 ∨ (¬ p2144) ∨ p2651)
    (h66454 : p5263 ∨ p5268)
    : p5268 ∨ (¬ p3680) ∨ p3016 ∨ p3564 ∨ (¬ p3212) ∨ p3670 ∨ (¬ p2144) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5268) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5263) := (Or.elim h108420 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u7 r6))))))))))))))));
    (Or.elim h66454 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109014 (p2098 p2363 p3609 p4232 p4859 p5339 : Prop)
    (h41368 : (¬ p2098) ∨ (¬ p2363) ∨ (¬ p4232) ∨ (¬ p4859) ∨ (¬ p5339))
    (h102523 : p5339 ∨ p3609)
    : p3609 ∨ (¬ p4232) ∨ (¬ p2098) ∨ (¬ p2363) ∨ (¬ p4859) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p4232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4859 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5339) := (Or.elim h41368 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h102523 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109015 (p2088 p2098 p3537 p3599 p3609 p5339 : Prop)
    (h107829 : (¬ p2098) ∨ (¬ p2088) ∨ (¬ p3537) ∨ p3599 ∨ (¬ p5339))
    (h102523 : p5339 ∨ p3609)
    : p3609 ∨ (¬ p2098) ∨ (¬ p2088) ∨ (¬ p3537) ∨ p3599 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5339) := (Or.elim h107829 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h102523 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109018 (p2459 p3322 p3461 p3609 p3670 p4133 p5339 : Prop)
    (h105712 : p4133)
    (h82478 : (¬ p3670) ∨ (¬ p5339) ∨ (¬ p3322) ∨ (¬ p2459) ∨ (¬ p4133) ∨ p3461)
    (h102523 : p5339 ∨ p3609)
    : p3609 ∨ (¬ p3670) ∨ (¬ p3322) ∨ p3461 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4133 := h105712;
    let u6 : (¬ p5339) := (Or.elim h82478 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h102523 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109022 (p3619 p4233 p5351 p5352 p6092 : Prop)
    (h108440 : (¬ p5351) ∨ (¬ p6092) ∨ (¬ p4233) ∨ (¬ p5352) ∨ (¬ p3619))
    (h9197 : (¬ p5351) ∨ p5352)
    : (¬ p5351) ∨ (¬ p6092) ∨ (¬ p4233) ∨ (¬ p3619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5351 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6092 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5352) := (Or.elim h108440 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h9197 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step109023 (p3619 p4233 p5351 p5352 p6092 : Prop)
    (h108441 : p6092 ∨ (¬ p5352) ∨ p5351 ∨ (¬ p4233) ∨ (¬ p3619))
    (h13658 : p5352 ∨ p6092)
    : p6092 ∨ p5351 ∨ (¬ p4233) ∨ (¬ p3619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6092) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5351) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5352) := (Or.elim h108441 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h13658 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109024 (p2753 p3599 p4233 p5351 p5352 : Prop)
    (h96583 : (¬ p2753) ∨ p3599 ∨ (¬ p5352) ∨ (¬ p4233))
    (h9197 : (¬ p5351) ∨ p5352)
    : (¬ p5351) ∨ (¬ p4233) ∨ (¬ p2753) ∨ p3599 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5351 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5352) := (Or.elim h96583 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h9197 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step109030 (p4393 p5440 p5442 p6118 : Prop)
    (h108470 : (¬ p5442) ∨ (¬ p6118) ∨ (¬ p5440) ∨ (¬ p4393))
    (h9393 : p5440 ∨ (¬ p5442))
    : (¬ p5442) ∨ (¬ p6118) ∨ (¬ p4393) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5440) := (Or.elim h108470 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h9393 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109031 (p4393 p5440 p5442 p6118 : Prop)
    (h108471 : p6118 ∨ p5442 ∨ (¬ p4393) ∨ (¬ p5440))
    (h13884 : p5440 ∨ p6118)
    : p6118 ∨ p5442 ∨ (¬ p4393) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6118) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5442) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5440) := (Or.elim h108471 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h13884 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109036 (p2440 p3016 p4203 p5433 p5440 p6118 : Prop)
    (h56501 : (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4203) ∨ (¬ p5433) ∨ (¬ p5440))
    (h13884 : p5440 ∨ p6118)
    : p6118 ∨ (¬ p5433) ∨ (¬ p4203) ∨ (¬ p2440) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6118) := (fun h => hn (Or.inl h));
    let u1 : p5433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5440) := (Or.elim h56501 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => r3))))))));
    (Or.elim h13884 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109046 (p4260 p5469 p5474 : Prop)
    (h9481 : p4260 ∨ (¬ p5469))
    (h66477 : p5469 ∨ p5474)
    : p5474 ∨ p4260 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5474) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4260) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5469) := (Or.elim h9481 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66477 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109047 (p5469 p5472 p5474 : Prop)
    (h9482 : (¬ p5469) ∨ p5472)
    (h66477 : p5469 ∨ p5474)
    : p5474 ∨ p5472 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5474) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5472) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5469) := (Or.elim h9482 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66477 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109054 (p2274 p3737 p4276 p5474 p5475 p5503 : Prop)
    (h105516 : p4276)
    (h96554 : (¬ p3737) ∨ (¬ p5475) ∨ (¬ p5503) ∨ (¬ p4276) ∨ p2274)
    (h9485 : (¬ p5474) ∨ p5475)
    : (¬ p5474) ∨ (¬ p3737) ∨ (¬ p5503) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5474 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4276 := h105516;
    let u5 : (¬ p5475) := (Or.elim h96554 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h9485 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step109059 (p3868 p5506 p5509 p6131 : Prop)
    (h108759 : (¬ p5506) ∨ (¬ p3868) ∨ (¬ p6131) ∨ (¬ p5509))
    (h9590 : (¬ p5506) ∨ p5509)
    : (¬ p5506) ∨ (¬ p3868) ∨ (¬ p6131) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6131 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5509) := (Or.elim h108759 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h9590 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step109060 (p3868 p5506 p5509 p6131 : Prop)
    (h108760 : p6131 ∨ (¬ p3868) ∨ p5506 ∨ (¬ p5509))
    (h14041 : p5509 ∨ p6131)
    : p6131 ∨ (¬ p3868) ∨ p5506 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6131) := (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5506) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5509) := (Or.elim h108760 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h14041 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109067 (p3888 p5517 p5518 p5519 p6134 : Prop)
    (h108673 : (¬ p5517) ∨ (¬ p3888) ∨ (¬ p5519) ∨ (¬ p5518) ∨ (¬ p6134))
    (h9629 : (¬ p5517) ∨ p5519)
    : (¬ p5517) ∨ (¬ p3888) ∨ (¬ p5518) ∨ (¬ p6134) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5517 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p6134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5519) := (Or.elim h108673 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h9629 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u4 r0)))))

theorem step109068 (p3888 p5517 p5518 p5519 p6134 : Prop)
    (h108674 : p6134 ∨ p5517 ∨ (¬ p3888) ∨ (¬ p5519) ∨ (¬ p5518))
    (h14121 : p5519 ∨ p6134)
    : p6134 ∨ p5517 ∨ (¬ p3888) ∨ (¬ p5518) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5517) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5519) := (Or.elim h108674 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h14121 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109078 (p3005 p3136 p4311 p5567 p5569 p5740 : Prop)
    (h94043 : (¬ p5569) ∨ (¬ p5740) ∨ p3136 ∨ (¬ p4311) ∨ (¬ p3005))
    (h9792 : (¬ p5567) ∨ p5569)
    : (¬ p5567) ∨ (¬ p5740) ∨ p3136 ∨ (¬ p3005) ∨ (¬ p4311) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5569) := (Or.elim h94043 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h9792 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step109079 (p2440 p2531 p3083 p5433 p5567 p5569 : Prop)
    (h41787 : (¬ p2440) ∨ (¬ p2531) ∨ (¬ p3083) ∨ (¬ p5433) ∨ (¬ p5569))
    (h9792 : (¬ p5567) ∨ p5569)
    : (¬ p5567) ∨ (¬ p3083) ∨ (¬ p2531) ∨ (¬ p5433) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5569) := (Or.elim h41787 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h9792 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step109083 (p3979 p5577 p5583 : Prop)
    (h9814 : p3979 ∨ (¬ p5583))
    (h66486 : p5577 ∨ p5583)
    : p5577 ∨ p3979 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5577) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3979) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5583) := (Or.elim h9814 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66486 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step109084 (p5577 p5583 p5584 : Prop)
    (h9812 : (¬ p5583) ∨ p5584)
    (h66486 : p5577 ∨ p5583)
    : p5577 ∨ p5584 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5577) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5584) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5583) := (Or.elim h9812 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66486 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step109086 (p5577 p5583 p5586 : Prop)
    (h9815 : (¬ p5583) ∨ p5586)
    (h66486 : p5577 ∨ p5583)
    : p5577 ∨ p5586 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5577) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5586) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5583) := (Or.elim h9815 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66486 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step109088 (p4075 p5648 p5649 p6170 : Prop)
    (h108564 : (¬ p5648) ∨ (¬ p4075) ∨ (¬ p6170) ∨ (¬ p5649))
    (h10005 : (¬ p5648) ∨ p5649)
    : (¬ p5648) ∨ (¬ p4075) ∨ (¬ p6170) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5648 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5649) := (Or.elim h108564 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h10005 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step109090 (p4075 p5648 p5649 p6170 : Prop)
    (h108565 : p6170 ∨ (¬ p4075) ∨ p5648 ∨ (¬ p5649))
    (h14755 : p5649 ∨ p6170)
    : p6170 ∨ (¬ p4075) ∨ p5648 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6170) := (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5648) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5649) := (Or.elim h108565 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h14755 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109091 (p3546 p4372 p5649 p6170 : Prop)
    (h108567 : p6170 ∨ (¬ p4372) ∨ (¬ p5649) ∨ (¬ p3546))
    (h14755 : p5649 ∨ p6170)
    : p6170 ∨ (¬ p4372) ∨ (¬ p3546) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6170) := (fun h => hn (Or.inl h));
    let u1 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5649) := (Or.elim h108567 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h14755 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109094 (p4181 p5696 p5697 p6182 : Prop)
    (h108595 : (¬ p5696) ∨ (¬ p6182) ∨ (¬ p5697) ∨ (¬ p4181))
    (h10228 : (¬ p5696) ∨ p5697)
    : (¬ p5696) ∨ (¬ p6182) ∨ (¬ p4181) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6182 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5697) := (Or.elim h108595 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h10228 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step109095 (p4181 p5696 p5697 p6182 : Prop)
    (h108596 : p6182 ∨ p5696 ∨ (¬ p5697) ∨ (¬ p4181))
    (h15266 : p5697 ∨ p6182)
    : p6182 ∨ p5696 ∨ (¬ p4181) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6182) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5697) := (Or.elim h108596 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h15266 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109108 (p3917 p6064 p6065 : Prop)
    (h13394 : p3917 ∨ p6064)
    (h66595 : (¬ p6064) ∨ (¬ p6065))
    : (¬ p6065) ∨ p3917 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6065 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3917) := (fun h => hn (Or.inr h));
    let u2 : p6064 := (Or.elim h13394 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66595 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (r0 u0)))))

theorem step109115 (p4260 p6124 p6125 : Prop)
    (h13957 : p4260 ∨ p6124)
    (h66615 : (¬ p6124) ∨ (¬ p6125))
    : (¬ p6125) ∨ p4260 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4260) := (fun h => hn (Or.inr h));
    let u2 : p6124 := (Or.elim h13957 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66615 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (r0 u0)))))

theorem step109123 (p3979 p6151 p6152 : Prop)
    (h14416 : p3979 ∨ p6152)
    (h66624 : (¬ p6151) ∨ (¬ p6152))
    : (¬ p6151) ∨ p3979 :=
  Classical.byContradiction (fun hn =>
    let u0 : p6151 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3979) := (fun h => hn (Or.inr h));
    let u2 : p6152 := (Or.elim h14416 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h66624 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u2)))))

theorem step109128 (p2449 p2696 p2742 p2839 p2996 p3105 p3461 p4322 p4394 : Prop)
    (h108664 : (¬ p3461) ∨ p3105 ∨ (¬ p4322) ∨ p2996 ∨ (¬ p2449) ∨ (¬ p2696) ∨ p2839 ∨ (¬ p2742) ∨ (¬ p4394))
    (h102362 : p4394 ∨ (¬ p3461))
    : (¬ p3461) ∨ p3105 ∨ (¬ p4322) ∨ p2996 ∨ (¬ p2449) ∨ (¬ p2696) ∨ p2839 ∨ (¬ p2742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4394) := (Or.elim h108664 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => r7))))))))))))))));
    (Or.elim h102362 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109131 (p3125 p3461 p4393 p4394 : Prop)
    (h96096 : (¬ p4393) ∨ (¬ p4394) ∨ (¬ p3125))
    (h102362 : p4394 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p4393) ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4394) := (Or.elim h96096 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h102362 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109137 (p2363 p3422 p3564 p3641 p4432 p4603 : Prop)
    (h77655 : p3641 ∨ (¬ p3564) ∨ (¬ p4603) ∨ (¬ p4432) ∨ (¬ p3422))
    (h102251 : p4603 ∨ (¬ p2363))
    : (¬ p2363) ∨ (¬ p3564) ∨ (¬ p4432) ∨ (¬ p3422) ∨ p3641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4603) := (Or.elim h77655 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102251 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109139 (p2363 p2373 p2563 p3125 p4506 p4603 : Prop)
    (h79012 : (¬ p3125) ∨ p2373 ∨ (¬ p4506) ∨ (¬ p4603) ∨ (¬ p2563))
    (h102251 : p4603 ∨ (¬ p2363))
    : (¬ p2363) ∨ p2373 ∨ (¬ p3125) ∨ (¬ p4506) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4603) := (Or.elim h79012 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h102251 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109141 (p2352 p2363 p3276 p3461 p4422 p4603 : Prop)
    (h91312 : p3461 ∨ (¬ p3276) ∨ p2352 ∨ (¬ p4603) ∨ (¬ p4422))
    (h102251 : p4603 ∨ (¬ p2363))
    : (¬ p2363) ∨ p3461 ∨ (¬ p3276) ∨ (¬ p4422) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4603) := (Or.elim h91312 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102251 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109147 (p2493 p2553 p2911 p3527 p4708 : Prop)
    (h104402 : p3527 ∨ (¬ p2911) ∨ (¬ p4708) ∨ (¬ p2493))
    (h101336 : p4708 ∨ p2553)
    : p2553 ∨ (¬ p2911) ∨ p3527 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4708) := (Or.elim h104402 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h101336 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109150 (p2553 p2829 p3201 p3367 p4390 p4708 : Prop)
    (h87963 : (¬ p2829) ∨ p3201 ∨ (¬ p4390) ∨ (¬ p4708) ∨ p3367)
    (h101336 : p4708 ∨ p2553)
    : p2553 ∨ p3201 ∨ p3367 ∨ (¬ p2829) ∨ (¬ p4390) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4708) := (Or.elim h87963 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h101336 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109151 (p2341 p2553 p2573 p2911 p4708 p5197 : Prop)
    (h95101 : (¬ p2911) ∨ p2341 ∨ (¬ p4708) ∨ (¬ p2573) ∨ (¬ p5197))
    (h101336 : p4708 ∨ p2553)
    : p2553 ∨ p2341 ∨ (¬ p2911) ∨ (¬ p5197) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4708) := (Or.elim h95101 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h101336 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109152 (p2553 p2630 p2685 p3016 p3740 p4708 : Prop)
    (h101273 : (¬ p3740) ∨ (¬ p4708) ∨ p2685 ∨ (¬ p3016) ∨ (¬ p2630))
    (h101336 : p4708 ∨ p2553)
    : p2553 ∨ p2685 ∨ (¬ p2630) ∨ (¬ p3740) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4708) := (Or.elim h101273 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h101336 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109154 (p2417 p2553 p3016 p3516 p4112 p4155 p4708 : Prop)
    (h101275 : p3516 ∨ (¬ p4112) ∨ (¬ p4708) ∨ (¬ p2417) ∨ (¬ p4155) ∨ (¬ p3016))
    (h101336 : p4708 ∨ p2553)
    : p2553 ∨ (¬ p2417) ∨ (¬ p4155) ∨ p3516 ∨ (¬ p4112) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4708) := (Or.elim h101275 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h101336 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109155 (p2220 p2532 p2619 p3212 p3609 p4742 : Prop)
    (h92497 : (¬ p3212) ∨ p3609 ∨ p2220 ∨ (¬ p4742) ∨ (¬ p2532))
    (h96152 : p4742 ∨ p2619)
    : p2619 ∨ p2220 ∨ p3609 ∨ (¬ p2532) ∨ (¬ p3212) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4742) := (Or.elim h92497 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96152 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109156 (p2532 p2619 p3115 p3156 p3609 p4742 : Prop)
    (h97126 : (¬ p3115) ∨ p3609 ∨ (¬ p4742) ∨ p3156 ∨ (¬ p2532))
    (h96152 : p4742 ∨ p2619)
    : p2619 ∨ p3156 ∨ p3609 ∨ (¬ p2532) ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4742) := (Or.elim h97126 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96152 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109164 (p2839 p3105 p3599 p5031 : Prop)
    (h30681 : (¬ p2839) ∨ p3599 ∨ (¬ p5031))
    (h102669 : p5031 ∨ (¬ p3105))
    : (¬ p3105) ∨ p3599 ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5031) := (Or.elim h30681 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h102669 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109165 (p2143 p3105 p4032 p5030 p5031 : Prop)
    (h19338 : (¬ p2143) ∨ (¬ p4032) ∨ (¬ p5030) ∨ (¬ p5031))
    (h102669 : p5031 ∨ (¬ p3105))
    : (¬ p3105) ∨ (¬ p2143) ∨ (¬ p4032) ∨ (¬ p5030) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5031) := (Or.elim h19338 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h102669 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109166 (p2608 p2839 p3105 p3670 p4322 p5031 : Prop)
    (h42868 : (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3670) ∨ (¬ p4322) ∨ (¬ p5031))
    (h102669 : p5031 ∨ (¬ p3105))
    : (¬ p3105) ∨ (¬ p4322) ∨ (¬ p3670) ∨ (¬ p2839) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5031) := (Or.elim h42868 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => r3))))))));
    (Or.elim h102669 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109168 (p2972 p3105 p3670 p4322 p4875 p5031 : Prop)
    (h106227 : p4875)
    (h96651 : (¬ p3670) ∨ (¬ p4322) ∨ (¬ p4875) ∨ (¬ p5031) ∨ p2972)
    (h102669 : p5031 ∨ (¬ p3105))
    : (¬ p3105) ∨ p2972 ∨ (¬ p3670) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2972) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4875 := h106227;
    let u5 : (¬ p5031) := (Or.elim h96651 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h102669 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109169 (p2427 p3105 p3571 p3670 p3707 p5031 p5357 : Prop)
    (h107426 : (¬ p5357) ∨ (¬ p3571) ∨ (¬ p5031) ∨ (¬ p3670) ∨ p2427 ∨ p3707)
    (h102669 : p5031 ∨ (¬ p3105))
    : (¬ p3105) ∨ (¬ p3670) ∨ (¬ p3571) ∨ p3707 ∨ p2427 ∨ (¬ p5357) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5031) := (Or.elim h107426 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h102669 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109174 (p3227 p3276 p3707 p5126 p5127 : Prop)
    (h14030 : (¬ p3227) ∨ (¬ p3707) ∨ (¬ p5126) ∨ (¬ p5127))
    (h96291 : p5126 ∨ p3276)
    : p3276 ∨ (¬ p5127) ∨ (¬ p3707) ∨ (¬ p3227) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p5127 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3227 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5126) := (Or.elim h14030 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h96291 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109175 (p3276 p3461 p4331 p5126 p5127 : Prop)
    (h16144 : (¬ p3461) ∨ (¬ p4331) ∨ (¬ p5126) ∨ (¬ p5127))
    (h96291 : p5126 ∨ p3276)
    : p3276 ∨ (¬ p4331) ∨ (¬ p3461) ∨ (¬ p5127) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5127 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5126) := (Or.elim h16144 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h96291 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109179 (p2598 p2608 p2753 p2761 p3276 p3461 p3654 p4166 p4638 p5021 p5126 : Prop)
    (h105409 : p4638)
    (h99871 : (¬ p4166) ∨ p3461 ∨ (¬ p2608) ∨ (¬ p5021) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p5126) ∨ (¬ p2598) ∨ p3654 ∨ (¬ p4638))
    (h96291 : p5126 ∨ p3276)
    : p3276 ∨ (¬ p2761) ∨ (¬ p4166) ∨ (¬ p2598) ∨ (¬ p5021) ∨ p3461 ∨ (¬ p2753) ∨ p3654 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4638 := h105409;
    let u10 : (¬ p5126) := (Or.elim h99871 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u7 q8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h96291 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109183 (p2230 p2563 p2685 p2807 p3125 p3323 p3755 p4236 p5279 : Prop)
    (h107563 : p3755 ∨ (¬ p3125) ∨ (¬ p5279) ∨ (¬ p2563) ∨ p2807 ∨ (¬ p2230) ∨ (¬ p2685) ∨ (¬ p4236))
    (h95304 : (¬ p3323) ∨ p5279)
    : (¬ p3323) ∨ p3755 ∨ (¬ p2230) ∨ p2807 ∨ (¬ p3125) ∨ (¬ p2685) ∨ (¬ p2563) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5279) := (Or.elim h107563 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h95304 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u8 r0)))))

theorem step109185 (p2156 p2685 p2807 p3096 p3276 p3323 p3461 p3755 p4236 p4422 p5279 : Prop)
    (h107683 : (¬ p3276) ∨ p3755 ∨ (¬ p3096) ∨ (¬ p4236) ∨ (¬ p5279) ∨ (¬ p2156) ∨ (¬ p2685) ∨ p2807 ∨ p3461 ∨ (¬ p4422))
    (h95304 : (¬ p3323) ∨ p5279)
    : (¬ p3323) ∨ p3461 ∨ (¬ p2156) ∨ (¬ p2685) ∨ (¬ p3276) ∨ p3755 ∨ (¬ p3096) ∨ (¬ p4236) ∨ (¬ p4422) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p5279) := (Or.elim h107683 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u9 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u1 q8))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h95304 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u10 r0)))))

theorem step109192 (p2737 p3599 p3755 p5459 : Prop)
    (h39439 : (¬ p2737) ∨ p3599 ∨ (¬ p5459))
    (h96235 : p5459 ∨ (¬ p3755))
    : (¬ p3755) ∨ p3599 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5459) := (Or.elim h39439 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h96235 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109213 (p2850 p3096 p3422 p3727 p5449 p6119 : Prop)
    (h87911 : (¬ p3727) ∨ (¬ p5449) ∨ (¬ p3096) ∨ p3422 ∨ (¬ p2850))
    (h13890 : p5449 ∨ p6119)
    : p6119 ∨ (¬ p3727) ∨ (¬ p2850) ∨ p3422 ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6119) := (fun h => hn (Or.inl h));
    let u1 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5449) := (Or.elim h87911 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h13890 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109214 (p2797 p3136 p3745 p4272 p5449 p6119 : Prop)
    (h96087 : (¬ p4272) ∨ (¬ p5449) ∨ (¬ p3136) ∨ (¬ p3745) ∨ p2797)
    (h13890 : p5449 ∨ p6119)
    : p6119 ∨ (¬ p4272) ∨ (¬ p3136) ∨ (¬ p3745) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6119) := (fun h => hn (Or.inl h));
    let u1 : p4272 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5449) := (Or.elim h96087 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h13890 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109215 (p2122 p2307 p3717 p3743 p4193 p5449 p6119 : Prop)
    (h96086 : (¬ p3717) ∨ (¬ p5449) ∨ p2122 ∨ (¬ p2307) ∨ (¬ p3743) ∨ (¬ p4193))
    (h13890 : p5449 ∨ p6119)
    : p6119 ∨ (¬ p3717) ∨ (¬ p2307) ∨ (¬ p3743) ∨ p2122 ∨ (¬ p4193) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6119) := (fun h => hn (Or.inl h));
    let u1 : p3717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5449) := (Or.elim h96086 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h13890 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109230 (p2668 p3969 p4134 p5577 p5579 p5717 : Prop)
    (h105379 : p4134)
    (h61652 : (¬ p2668) ∨ (¬ p3969) ∨ (¬ p4134) ∨ (¬ p5579) ∨ (¬ p5717))
    (h9807 : (¬ p5577) ∨ p5579)
    : (¬ p5577) ∨ (¬ p5717) ∨ (¬ p3969) ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4134 := h105379;
    let u5 : (¬ p5579) := (Or.elim h61652 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h9807 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step109231 (p2352 p4009 p4774 p5514 p5577 p5579 : Prop)
    (h42621 : (¬ p2352) ∨ (¬ p4009) ∨ (¬ p4774) ∨ (¬ p5514) ∨ (¬ p5579))
    (h9807 : (¬ p5577) ∨ p5579)
    : (¬ p5577) ∨ (¬ p5514) ∨ (¬ p4009) ∨ (¬ p4774) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5579) := (Or.elim h42621 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => r3))))))));
    (Or.elim h9807 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step109232 (p2352 p3969 p4134 p5514 p5577 p5579 : Prop)
    (h105379 : p4134)
    (h64914 : (¬ p2352) ∨ (¬ p3969) ∨ (¬ p4134) ∨ (¬ p5514) ∨ (¬ p5579))
    (h9807 : (¬ p5577) ∨ p5579)
    : (¬ p5577) ∨ (¬ p5514) ∨ (¬ p3969) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4134 := h105379;
    let u5 : (¬ p5579) := (Or.elim h64914 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => r3))))))));
    (Or.elim h9807 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step109239 (p3016 p3379 p3801 p3807 p3901 : Prop)
    (h102597 : (¬ p3807) ∨ (¬ p3901) ∨ p3379 ∨ p3016)
    (h107845 : p3807 ∨ p3801)
    : p3801 ∨ (¬ p3901) ∨ p3016 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3801) := (fun h => hn (Or.inl h));
    let u1 : p3901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3807) := (Or.elim h102597 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h107845 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109241 (p2761 p3193 p3801 p3807 p4638 p5127 : Prop)
    (h105409 : p4638)
    (h99872 : (¬ p3807) ∨ (¬ p5127) ∨ (¬ p4638) ∨ p3193 ∨ (¬ p2761))
    (h107845 : p3807 ∨ p3801)
    : p3801 ∨ (¬ p5127) ∨ p3193 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3801) := (fun h => hn (Or.inl h));
    let u1 : p5127 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4638 := h105409;
    let u5 : (¬ p3807) := (Or.elim h99872 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h107845 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109248 (p3266 p3609 p4019 p4200 : Prop)
    (h38914 : (¬ p3609) ∨ p4019 ∨ (¬ p4200))
    (h93630 : p4200 ∨ (¬ p3266))
    : (¬ p3266) ∨ p4019 ∨ (¬ p3609) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4019) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4200) := (Or.elim h38914 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h93630 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109249 (p2363 p3266 p4200 p5580 : Prop)
    (h20175 : (¬ p2363) ∨ (¬ p4200) ∨ (¬ p5580))
    (h93630 : p4200 ∨ (¬ p3266))
    : (¬ p3266) ∨ (¬ p5580) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4200) := (Or.elim h20175 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h93630 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109250 (p2459 p3266 p4200 p5558 : Prop)
    (h20091 : (¬ p2459) ∨ (¬ p4200) ∨ (¬ p5558))
    (h93630 : p4200 ∨ (¬ p3266))
    : (¬ p3266) ∨ (¬ p5558) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4200) := (Or.elim h20091 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h93630 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109251 (p3256 p3266 p4009 p4200 : Prop)
    (h40270 : (¬ p3256) ∨ p4009 ∨ (¬ p4200))
    (h93630 : p4200 ∨ (¬ p3266))
    : (¬ p3266) ∨ p4009 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4009) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4200) := (Or.elim h40270 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h93630 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109255 (p2132 p2331 p2619 p3266 p3461 p3506 p4200 p4330 p4421 p4786 p5568 : Prop)
    (h106425 : p4786)
    (h106329 : p4330)
    (h84800 : (¬ p3506) ∨ p3461 ∨ (¬ p4200) ∨ (¬ p5568) ∨ p2132 ∨ (¬ p2331) ∨ (¬ p4330) ∨ (¬ p4421) ∨ p2619 ∨ (¬ p4786))
    (h93630 : p4200 ∨ (¬ p3266))
    : (¬ p3266) ∨ (¬ p4421) ∨ (¬ p2331) ∨ p3461 ∨ p2619 ∨ (¬ p3506) ∨ (¬ p5568) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4786 := h106425;
    let u9 : p4330 := h106329;
    let u10 : (¬ p4200) := (Or.elim h84800 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h93630 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109256 (p2331 p2717 p3266 p3425 p3461 p3506 p4200 p4330 p4421 p4786 p5558 : Prop)
    (h106425 : p4786)
    (h106329 : p4330)
    (h97047 : (¬ p3506) ∨ p3461 ∨ (¬ p5558) ∨ p2717 ∨ (¬ p4200) ∨ (¬ p3425) ∨ (¬ p2331) ∨ (¬ p4330) ∨ (¬ p4786) ∨ (¬ p4421))
    (h93630 : p4200 ∨ (¬ p3266))
    : (¬ p3266) ∨ p3461 ∨ (¬ p3425) ∨ p2717 ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p5558) ∨ (¬ p4421) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4786 := h106425;
    let u9 : p4330 := h106329;
    let u10 : (¬ p4200) := (Or.elim h97047 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u7))))))))))))))))))));
    (Or.elim h93630 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109268 (p3227 p3276 p3707 p5127 : Prop)
    (h109174 : p3276 ∨ (¬ p5127) ∨ (¬ p3707) ∨ (¬ p3227))
    (h96290 : p5127 ∨ p3276)
    : p3276 ∨ (¬ p3707) ∨ (¬ p3227) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3227 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5127) := (Or.elim h109174 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96290 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109269 (p3276 p3461 p4331 p5127 : Prop)
    (h109175 : p3276 ∨ (¬ p4331) ∨ (¬ p3461) ∨ (¬ p5127))
    (h96290 : p5127 ∨ p3276)
    : p3276 ∨ (¬ p4331) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5127) := (Or.elim h109175 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h96290 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109272 (p2761 p3193 p3276 p3801 p5127 : Prop)
    (h109241 : p3801 ∨ (¬ p5127) ∨ p3193 ∨ (¬ p2761))
    (h96290 : p5127 ∨ p3276)
    : p3276 ∨ p3801 ∨ p3193 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3801) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5127) := (Or.elim h109241 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h96290 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109276 (p2156 p2241 p2727 p3125 p3276 p3461 p3892 p4521 p5127 : Prop)
    (h96781 : (¬ p3892) ∨ (¬ p5127) ∨ (¬ p4521) ∨ (¬ p2156) ∨ (¬ p3125) ∨ (¬ p3461) ∨ p2727 ∨ p2241)
    (h96290 : p5127 ∨ p3276)
    : p3276 ∨ (¬ p3892) ∨ (¬ p2156) ∨ (¬ p3125) ∨ (¬ p3461) ∨ p2241 ∨ p2727 ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3892 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5127) := (Or.elim h96781 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (False.elim (u5 r6))))))))))))))));
    (Or.elim h96290 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109278 (p2761 p3434 p3670 p5229 : Prop)
    (h96617 : (¬ p3670) ∨ p2761 ∨ (¬ p5229))
    (h102623 : p5229 ∨ p3434)
    : p3434 ∨ p2761 ∨ (¬ p3670) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5229) := (Or.elim h96617 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h102623 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109282 (p2717 p2753 p3425 p3434 p3599 p4666 p5229 : Prop)
    (h105658 : p4666)
    (h96614 : (¬ p5229) ∨ (¬ p2753) ∨ (¬ p2717) ∨ p3599 ∨ (¬ p4666) ∨ p3425)
    (h102623 : p5229 ∨ p3434)
    : p3434 ∨ (¬ p2717) ∨ (¬ p2753) ∨ p3599 ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4666 := h105658;
    let u6 : (¬ p5229) := (Or.elim h96614 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h102623 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109288 (p3506 p3670 p3755 p5458 : Prop)
    (h94276 : p3670 ∨ (¬ p3506) ∨ (¬ p5458))
    (h96234 : p5458 ∨ (¬ p3755))
    : (¬ p3755) ∨ p3670 ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5458) := (Or.elim h94276 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96234 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109290 (p2630 p2737 p3599 p3755 p5177 p5458 : Prop)
    (h96622 : (¬ p3599) ∨ (¬ p5458) ∨ p2630 ∨ (¬ p5177) ∨ p2737)
    (h96234 : p5458 ∨ (¬ p3755))
    : (¬ p3755) ∨ (¬ p5177) ∨ p2630 ∨ p2737 ∨ (¬ p3599) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5458) := (Or.elim h96622 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96234 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109298 (p3379 p3422 p3801 p4166 p5681 : Prop)
    (h43781 : (¬ p3379) ∨ (¬ p3422) ∨ (¬ p3801) ∨ (¬ p5681))
    (h108172 : p4166 ∨ p5681)
    : p4166 ∨ (¬ p3801) ∨ (¬ p3379) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4166) := (fun h => hn (Or.inl h));
    let u1 : p3801 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5681) := (Or.elim h43781 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    (Or.elim h108172 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step109300 (p3641 p3969 p4149 p4166 p5681 : Prop)
    (h108581 : p4149 ∨ (¬ p5681) ∨ (¬ p3969) ∨ (¬ p3641))
    (h108172 : p4166 ∨ p5681)
    : p4166 ∨ p4149 ∨ (¬ p3969) ∨ (¬ p3641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4166) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4149) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p5681) := (Or.elim h108581 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h108172 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u4 r0)))))

theorem step109320 (p2230 p2427 p2449 p3005 p3166 p3246 p3755 p4236 p4663 : Prop)
    (h107598 : (¬ p4663) ∨ p3755 ∨ (¬ p3005) ∨ (¬ p4236) ∨ (¬ p3246) ∨ (¬ p2230) ∨ (¬ p2427) ∨ p3166)
    (h96423 : p4663 ∨ (¬ p2449))
    : (¬ p2449) ∨ p3755 ∨ (¬ p2230) ∨ (¬ p3246) ∨ p3166 ∨ (¬ p3005) ∨ (¬ p2427) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4663) := (Or.elim h107598 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u4 r6))))))))))))))));
    (Or.elim h96423 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109321 (p2449 p2630 p2651 p2761 p2962 p3461 p3654 p3755 p4236 p4663 : Prop)
    (h107654 : (¬ p3461) ∨ p3755 ∨ p2761 ∨ (¬ p4236) ∨ p2651 ∨ (¬ p4663) ∨ (¬ p2962) ∨ (¬ p2630) ∨ (¬ p3654))
    (h96423 : p4663 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p3461) ∨ (¬ p3654) ∨ p2651 ∨ p2761 ∨ (¬ p2630) ∨ p3755 ∨ (¬ p4236) ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4663) := (Or.elim h107654 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u2))))))))))))))))));
    (Or.elim h96423 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109322 (p2307 p2449 p2761 p2781 p2946 p3136 p3461 p3755 p4187 p4236 p4663 : Prop)
    (h84382 : p2761 ∨ (¬ p4187) ∨ p2946 ∨ p3755 ∨ (¬ p4236) ∨ (¬ p3136) ∨ (¬ p2307) ∨ (¬ p3461) ∨ (¬ p4663) ∨ (¬ p2781))
    (h96423 : p4663 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p3461) ∨ p3755 ∨ (¬ p3136) ∨ p2761 ∨ (¬ p2781) ∨ (¬ p4236) ∨ (¬ p2307) ∨ p2946 ∨ (¬ p4187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4663) := (Or.elim h84382 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (r8 u5))))))))))))))))))));
    (Or.elim h96423 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109328 (p2156 p2252 p2396 p2449 p2553 p2741 p3005 p3096 p3166 p3519 p3755 p4376 p4399 p4663 : Prop)
    (h106320 : p4376)
    (h76838 : p3755 ∨ (¬ p2553) ∨ (¬ p2156) ∨ (¬ p3096) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p2252) ∨ p3166 ∨ (¬ p2741) ∨ (¬ p3005) ∨ (¬ p2396) ∨ (¬ p4663))
    (h96423 : p4663 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p3005) ∨ (¬ p2396) ∨ (¬ p2156) ∨ p3166 ∨ (¬ p2553) ∨ p3755 ∨ (¬ p3096) ∨ (¬ p3519) ∨ (¬ p4399) ∨ (¬ p2252) ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4376 := h106320;
    let u13 : (¬ p4663) := (Or.elim h76838 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u1))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u2))) (fun r11 => r11))))))))))))))))))))))));
    (Or.elim h96423 (fun q0 => (False.elim (u13 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109329 (p2331 p2341 p2449 p2797 p2911 p3246 p3366 p3519 p3569 p3755 p4236 p4376 p4399 p4663 p4988 : Prop)
    (h106320 : p4376)
    (h101103 : (¬ p2341) ∨ p3755 ∨ (¬ p4236) ∨ p2331 ∨ (¬ p2797) ∨ (¬ p3366) ∨ (¬ p4663) ∨ (¬ p4399) ∨ (¬ p4988) ∨ (¬ p3519) ∨ (¬ p4376) ∨ p2911 ∨ (¬ p3246) ∨ (¬ p3569))
    (h96423 : p4663 ∨ (¬ p2449))
    : (¬ p2449) ∨ (¬ p2797) ∨ p3755 ∨ (¬ p4236) ∨ (¬ p3246) ∨ p2911 ∨ (¬ p3366) ∨ p2331 ∨ (¬ p3519) ∨ (¬ p4399) ∨ (¬ p2341) ∨ (¬ p4988) ∨ (¬ p3569) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p4376 := h106320;
    let u14 : (¬ p4663) := (Or.elim h101103 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u13))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (u5 q11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u4))) (fun r12 => (False.elim (r12 u12))))))))))))))))))))))))))));
    (Or.elim h96423 (fun q0 => (False.elim (u14 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109330 (p2122 p2829 p3093 p3399 p3547 p4871 : Prop)
    (h80362 : p3093 ∨ (¬ p3547) ∨ (¬ p4871) ∨ p2122 ∨ (¬ p3399))
    (h102353 : p4871 ∨ (¬ p2829))
    : (¬ p2829) ∨ (¬ p3399) ∨ p2122 ∨ p3093 ∨ (¬ p3547) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3547 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4871) := (Or.elim h80362 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102353 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109331 (p2363 p2829 p3063 p3609 p4078 p4871 : Prop)
    (h83475 : (¬ p4871) ∨ (¬ p3063) ∨ (¬ p2363) ∨ p3609 ∨ (¬ p4078))
    (h102353 : p4871 ∨ (¬ p2829))
    : (¬ p2829) ∨ (¬ p3063) ∨ p3609 ∨ (¬ p4078) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4871) := (Or.elim h83475 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h102353 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109332 (p2819 p2829 p3093 p3449 p4318 p4871 : Prop)
    (h92358 : p3093 ∨ (¬ p3449) ∨ p2819 ∨ (¬ p4871) ∨ (¬ p4318))
    (h102353 : p4871 ∨ (¬ p2829))
    : (¬ p2829) ∨ (¬ p4318) ∨ p2819 ∨ (¬ p3449) ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4871) := (Or.elim h92358 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h102353 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109333 (p2829 p3093 p3830 p3917 p4871 p5152 : Prop)
    (h92634 : (¬ p3830) ∨ p3093 ∨ (¬ p3917) ∨ (¬ p5152) ∨ (¬ p4871))
    (h102353 : p4871 ∨ (¬ p2829))
    : (¬ p2829) ∨ (¬ p3917) ∨ (¬ p3830) ∨ (¬ p5152) ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4871) := (Or.elim h92634 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h102353 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109334 (p2088 p2819 p2829 p3073 p4113 p4317 p4871 : Prop)
    (h93108 : (¬ p4317) ∨ (¬ p4113) ∨ (¬ p3073) ∨ p2819 ∨ p2088 ∨ (¬ p4871))
    (h102353 : p4871 ∨ (¬ p2829))
    : (¬ p2829) ∨ (¬ p4317) ∨ (¬ p3073) ∨ (¬ p4113) ∨ p2088 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4871) := (Or.elim h93108 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => r4))))))))));
    (Or.elim h102353 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step109342 (p2295 p2608 p3707 p3830 p5274 p5283 p5287 : Prop)
    (h108720 : p5287 ∨ (¬ p3830) ∨ p2608 ∨ (¬ p3707) ∨ (¬ p5274) ∨ (¬ p5283) ∨ (¬ p2295))
    (h108713 : p5287 ∨ p5283)
    : p5287 ∨ (¬ p3830) ∨ p2608 ∨ (¬ p3707) ∨ (¬ p5274) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5287) := (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p5283) := (Or.elim h108720 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h108713 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u6 r0)))))

theorem step109352 (p2230 p3054 p3717 p3727 p4730 p5421 : Prop)
    (h106074 : p4730)
    (h41056 : (¬ p2230) ∨ (¬ p3054) ∨ (¬ p3727) ∨ (¬ p4730) ∨ (¬ p5421))
    (h108002 : p3717 ∨ p5421)
    : p3717 ∨ (¬ p3727) ∨ (¬ p2230) ∨ (¬ p3054) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3717) := (fun h => hn (Or.inl h));
    let u1 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4730 := h106074;
    let u5 : (¬ p5421) := (Or.elim h41056 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h108002 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u5 r0)))))

theorem step109360 (p5500 p5501 p5503 p6130 : Prop)
    (h108747 : (¬ p5500) ∨ (¬ p5503) ∨ (¬ p6130) ∨ (¬ p5501))
    (h9581 : (¬ p5500) ∨ p5501)
    : (¬ p5500) ∨ (¬ p5503) ∨ (¬ p6130) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5500 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6130 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5501) := (Or.elim h108747 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h9581 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step109361 (p2437 p2440 p3434 p4253 p5500 p5501 : Prop)
    (h108491 : (¬ p5500) ∨ (¬ p5501) ∨ (¬ p4253) ∨ p2440 ∨ p3434 ∨ p2437)
    (h9581 : (¬ p5500) ∨ p5501)
    : (¬ p5500) ∨ (¬ p4253) ∨ p2440 ∨ p3434 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5500 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p5501) := (Or.elim h108491 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h9581 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u5 r0)))))

theorem step109362 (p5500 p5501 p5503 p6130 : Prop)
    (h108748 : p6130 ∨ (¬ p5503) ∨ p5500 ∨ (¬ p5501))
    (h14034 : p5501 ∨ p6130)
    : p6130 ∨ (¬ p5503) ∨ p5500 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6130) := (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5500) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5501) := (Or.elim h108748 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h14034 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109370 (p3888 p5517 p5518 p6134 : Prop)
    (h109067 : (¬ p5517) ∨ (¬ p3888) ∨ (¬ p5518) ∨ (¬ p6134))
    (h9626 : (¬ p5517) ∨ p5518)
    : (¬ p5517) ∨ (¬ p3888) ∨ (¬ p6134) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5517 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p6134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5518) := (Or.elim h109067 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h9626 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (u3 r0)))))

theorem step109371 (p3888 p5517 p5518 p6134 : Prop)
    (h109068 : p6134 ∨ p5517 ∨ (¬ p3888) ∨ (¬ p5518))
    (h14118 : p5518 ∨ p6134)
    : p6134 ∨ p5517 ∨ (¬ p3888) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p6134) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5517) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5518) := (Or.elim h109068 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h14118 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step109376 (p2807 p2996 p3034 p3166 p3527 p4378 : Prop)
    (h96889 : (¬ p3166) ∨ (¬ p3034) ∨ p3527 ∨ (¬ p4378) ∨ p2807)
    (h102816 : p3034 ∨ (¬ p2996))
    : (¬ p2996) ∨ p3527 ∨ (¬ p4378) ∨ p2807 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3034) := (Or.elim h96889 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h102816 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

end ElevenRUP
